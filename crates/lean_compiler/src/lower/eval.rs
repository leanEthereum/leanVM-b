//! Compile-time evaluation: what an expression is worth before anything runs.
//!
//! Every function here takes `&self` and emits nothing. That is the boundary,
//! and it is what lets a caller ask what an expression is worth without paying
//! for the answer: an index that folds costs no instruction, and a query that
//! comes back `None` has not already committed the program to something.
//!
//! There are two answers, not one, and the POSITION of a use decides which is
//! wanted. [`FnLower::try_const_int`] reads an expression as a compile-time
//! integer, which is what a size, an index, a bound and an exponent want.
//! [`FnLower::try_field_const`] reads the same expression as a field element,
//! where `+` is XOR, which is what a value wants. They disagree on anything
//! carrying a sum of overlapping integers, and `const(...)` is how an author
//! says the integer one was meant, in a condition or in a value.

use super::*;

/// `a·b` in the [`GAddr`] representation: exponents add, and at most one factor
/// may carry a runtime base (two pointers can't be multiplied symbolically).
fn gmul(a: GAddr, b: GAddr) -> Option<GAddr> {
    let base = match (a.base, b.base) {
        (None, x) | (x, None) => x,
        (Some(_), Some(_)) => return None,
    };
    Some(GAddr {
        base,
        exp: a.exp.checked_add(b.exp)?,
        // Only a based address carries a run, and at most one side is based, so
        // the shift keeps its origin: `addr(sb) * GEN ** k` stays bounded by `sb`.
        run: a.run.or(b.run),
    })
}

/// `b^k` for a compile-time exponent (small, so plain repeated multiplication).
pub(super) fn field_pow(b: F192, k: u32) -> F192 {
    let mut acc = F192::ONE;
    for _ in 0..k {
        acc *= b;
    }
    acc
}

impl FnLower<'_> {
    /// A compile-time integer expression. `None` means either a runtime value
    /// or arithmetic outside the source language's `u128` literal domain.
    pub(super) fn try_const_int(&self, e: &Expr) -> Option<u128> {
        match e {
            Expr::Lit(k) => Some(*k),
            Expr::Var(v) => self.scope.int(v),
            Expr::Add(a, b) => self.try_const_int(a)?.checked_add(self.try_const_int(b)?),
            Expr::Sub(a, b) => self.try_const_int(a)?.checked_sub(self.try_const_int(b)?),
            Expr::Mul(a, b) => self.try_const_int(a)?.checked_mul(self.try_const_int(b)?),
            Expr::Div(a, b) => {
                let d = self.try_const_int(b)?;
                if d == 0 {
                    self.fail("compile-time division by zero")
                };
                Some(self.try_const_int(a)? / d)
            }
            Expr::Mod(a, b) => {
                let d = self.try_const_int(b)?;
                if d == 0 {
                    self.fail("compile-time modulo by zero")
                };
                Some(self.try_const_int(a)? % d)
            }
            Expr::Index(..) => self
                .const_array_elem(e)
                .and_then(|value| (value.c2 == 0).then_some(value.c0 as u128 | ((value.c1 as u128) << 64))),
            // `const(e)` is already the integer reading, so it is transparent here.
            Expr::Call(f, args) if f == "const" && args.len() == 1 => {
                self.check_const_leaves(&args[0]);
                self.try_const_int(&args[0])
            }
            Expr::Call(..) => self.const_len(e).map(|n| n as u128),
            Expr::Pow(b, e) => self
                .try_const_int(b)?
                .checked_pow(u32::try_from(self.try_const_int(e)?).ok()?),
            _ => None,
        }
    }

    /// A compile-time integer index. The general integer evaluator is narrowed
    /// here so stack offsets, bounds, and immediate exponents remain `u32`.
    pub(super) fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        u32::try_from(self.try_const_int(idx)?).ok()
    }

    /// A stack index or compile-time slice bound: [`Self::try_const_index`],
    /// required to succeed.
    pub(super) fn const_index(&self, idx: &Expr) -> u32 {
        self.try_const_index(idx).unwrap_or_else(|| {
            // An oversized index is an index-shaped mistake, not a runtime value,
            // so diagnose it precisely (`sa[2^32]` must not wrap to `sa[0]`). Read
            // through the integer evaluator, so `const(2 ** 33)` gets the same
            // message a bare literal does rather than "not a compile-time integer".
            if let Some(k) = self.try_const_int(idx) {
                self.fail(format!("stack index {k} does not fit in u32"));
            }
            self.fail(format!(
                "a StackBuf index must be a compile-time integer, got `{idx:?}`"
            ))
        })
    }

    /// The exponent of `GEN ** e`: a compile-time integer, required to succeed.
    pub(super) fn gpow_exp(&self, e: &Expr) -> u128 {
        self.try_const_index(e)
            .unwrap_or_else(|| self.fail(format!("`GEN ** e` needs a compile-time integer exponent, got `{e:?}`")))
            as u128
    }

    /// If `e` is `NAME[i]` for a top-level constant array `NAME` with a
    /// compile-time index `i`, its element (a raw `u128`).
    pub(super) fn const_array_elem(&self, e: &Expr) -> Option<F192> {
        if let Expr::Index(arr, idx) = e
            && let Expr::Var(v) = arr.as_ref()
            && let Some(a) = self.const_arrays.get(v)
        {
            let i = self.try_const_index(idx)? as usize;
            return Some(
                *a.get(i).unwrap_or_else(|| {
                    self.fail(format!("const array `{v}` index {i} out of bounds (len {})", a.len()))
                }),
            );
        }
        None
    }

    /// If `e` is `len(NAME)` for a top-level constant array `NAME`, its length.
    pub(super) fn const_len(&self, e: &Expr) -> Option<usize> {
        if let Expr::Call(f, args) = e
            && f == "len"
            && args.len() == 1
            && let Expr::Var(v) = &args[0]
        {
            return self.const_arrays.get(v).map(|a| a.len());
        }
        None
    }

    /// The surviving operand of `a + b` when the other is a compile-time zero,
    /// which contributes nothing and (being a constant) has no side effect to
    /// preserve. So `x + 0` lowers to just `x`: no cell, no XOR. Kills the
    /// `acc = 0; acc = acc + t` accumulator seed and similar.
    pub(super) fn add_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ZERO) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ZERO)).then_some(a)
    }

    /// The surviving operand of `a * b` when the other is a compile-time one, a
    /// no-op multiply. Kills the `acc = GEN ** 0` (= 1) accumulator seed's first
    /// `1 * f` in every product loop.
    pub(super) fn mul_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ONE) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ONE)).then_some(a)
    }

    /// The field value of `e` when it is a trivial compile-time constant (a
    /// literal, a literal-bound name, or `GEN ** 0`), for the `x*1`/`x+0`
    /// arithmetic identities and the `== 0` test of [`Self::lower_if`].
    pub(super) fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.scope.int(v).and_then(|n| u64::try_from(n).ok()),
            Expr::GPow(0) => Some(1),
            _ => None,
        }
    }

    /// `e`'s two readings when they DISAGREE: the compile-time integer, and the
    /// field element a value position would see. `None` when they agree, or when
    /// `e` has only one of them (`3 - 1` has no field reading at all, so nothing
    /// contradicts its integer one).
    ///
    /// One literal cannot stand for both, so an expression like this means
    /// different things in an index and in a value, and any construct that must
    /// pick one has to say which.
    pub(super) fn diverging_readings(&self, e: &Expr) -> Option<(u128, F192)> {
        let n = self.try_const_int(e)?;
        let f = self.try_field_const(e)?;
        (f != lit_field(n)).then_some((n, f))
    }

    /// Check the LEAVES of a `const(...)`. The wrapper reinterprets the
    /// OPERATORS as integer arithmetic, which is its whole purpose, so their two
    /// readings are expected to diverge (`3 + 1` is the integer 4 and the value
    /// 2). A LEAF is different: `const(...)` cannot change what a name already
    /// stands for, so a leaf whose own two readings disagree would have the
    /// wrapper hand back a value that leaf never had.
    ///
    /// `n = 2 + 3` is the case. The cell holds `2 XOR 3` = 1 while the name's
    /// integer reading is 5, so `assert n == 1` and `assert const(n) == 5` both
    /// passed, in one program. This is the ambiguity `if const(...)` already
    /// rejects per side, one level up, and the rule is the same one.
    pub(super) fn check_const_leaves(&self, e: &Expr) {
        match e {
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b) => {
                self.check_const_leaves(a);
                self.check_const_leaves(b);
            }
            Expr::Call(f, args) if f == "const" && args.len() == 1 => self.check_const_leaves(&args[0]),
            leaf => {
                if let Some((n, f)) = self.diverging_readings(leaf) {
                    self.fail(format!(
                        "const(...) reads its operators as integer arithmetic, but it cannot reinterpret \
                         `{leaf:?}`, which is the integer {n} and the value {:#x}:{:#x}: two different \
                         numbers. Bind it in one regime and name that one",
                        f.c1, f.c0
                    ))
                }
            }
        }
    }

    /// The exponent of `e` when it is a *constant* g-power small enough to ride a
    /// `DEREF` `β` immediate, for the constant factor of a product index.
    ///
    /// The one g-power recognizer. A second one used to match `Expr::Var`
    /// against the *integer* reading of a name and take that integer's bit
    /// position as the exponent, which is a different question: `K = 3 + 1` is
    /// the integer 4 and the field element `3 XOR 1` = 2, so it folded to `g²`
    /// in an index position while being `g¹` everywhere else.
    ///
    /// The rule that replaces it never picks a reading. It folds `e` only where
    /// the readings **agree**: either the compiler already tracks `e` as an
    /// address, or `e` is the integer `2^j` AND its field value is `g^j`, in
    /// which case both readings name cell `j` and folding decides nothing.
    pub(super) fn const_gpow(&self, e: &Expr) -> Option<u32> {
        if let Some(GAddr { base: None, exp, .. }) = self.gaddr_of(e)
            && exp <= FOLD_MAX
        {
            return Some(exp as u32);
        }
        // `g = x`, so the integer `2^j` reads as `g^j`, but ONLY for `j < 64`:
        // at and above that the modulus folds the monomial back into the low
        // limb while the literal's bit lands in the tower coefficient of `y`.
        let n = self.try_const_int(e)?;
        if !n.is_power_of_two() || n >= (1 << 64) {
            return None;
        }
        let j = n.trailing_zeros();
        (u128::from(j) <= FOLD_MAX && self.try_field_const(e)? == g_pow_u128(u128::from(j)).into()).then_some(j)
    }

    /// The symbolic g-address of `e`, when it is one: a constant g-power
    /// (`1 = g⁰`, `GEN`, `GEN ** k`), a tracked cursor/shifted pointer, or a
    /// plain scalar var as its own base (`base·g⁰`). Products of these combine
    /// via [`gmul`]. `None` for anything with a runtime, non-g-power value.
    pub(super) fn gaddr_of(&self, e: &Expr) -> Option<GAddr> {
        match e {
            // A literal `2^k` IS `g^k` here, since `g = x`. `try_gpow_index`
            // always knew that; without this arm `hb[GEN * 2]` was rejected as
            // "not a g-power" while `hb[GEN * GEN]`, the same field element,
            // compiled, and `hb[r * 2]` compiled again once `r` was runtime.
            // `g = x`, so the literal `2^k` IS `g^k` -- but ONLY while `k < 64`.
            // At and above that the modulus `x^64 + x^4 + x^3 + x + 1` folds the
            // monomial back into the low limb, while the literal's bit `k` lands
            // in the NEXT limb, the tower coefficient of `y`. `try_gpow_index`
            // carries this guard; without it here the guest's own
            // `Y_TOWER = 2^64` would read as `g^64` in a pointer position.
            Expr::Lit(n) if n.is_power_of_two() && *n < (1 << 64) => Some(GAddr {
                base: None,
                exp: n.trailing_zeros() as u128,
                run: None,
            }),
            Expr::Gen => Some(GAddr {
                base: None,
                exp: 1,
                run: None,
            }),
            Expr::GPow(k) => Some(GAddr {
                base: None,
                exp: *k,
                run: None,
            }),
            Expr::GenPow(e) => Some(GAddr {
                base: None,
                exp: self.try_const_index(e)? as u128,
                run: None,
            }),
            Expr::Var(v) => match self.scope.bound(v)?.val {
                Binding::Gaddr(ga) => Some(ga),
                // A plain scalar is its own base, unshifted.
                Binding::Scalar(c) => Some(GAddr {
                    base: Some(c),
                    exp: 0,
                    run: None,
                }),
                _ => None,
            },
            Expr::Mul(a, b) => gmul(self.gaddr_of(a)?, self.gaddr_of(b)?),
            _ => None,
        }
    }

    /// `e` as a compile-time *field* constant, when it is one: a literal, `GEN`,
    /// `GEN ** k`, a var bound to a field constant (or a constant g-power), or
    /// `+`/`*` of those evaluated in the field (XOR / `K`-mul). `None` for a
    /// runtime value, a literal exceeding the 64-bit word, or a compile-time
    /// *integer* op (`//`/`%` are index-only).
    pub(super) fn try_field_const(&self, e: &Expr) -> Option<F192> {
        match e {
            // A source literal fills the low 128 bits; g-powers/addresses embed in K.
            Expr::Lit(n) => Some(lit_field(*n)),
            Expr::Gen => Some(g_pow(1).into()),
            Expr::GPow(k) => Some(g_pow_u128(*k).into()),
            Expr::GenPow(e) => Some(g_pow_u128(self.try_const_index(e)? as u128).into()),
            Expr::Var(v) => match self.scope.bound(v)?.val {
                Binding::FConst(c) => Some(c),
                Binding::Gaddr(GAddr { base: None, exp, .. }) => Some(g_pow_u128(exp).into()),
                _ => None,
            },
            Expr::Add(a, b) => Some(self.try_field_const(a)? + self.try_field_const(b)?),
            Expr::Mul(a, b) => Some(self.try_field_const(a)? * self.try_field_const(b)?),
            // A constant-array element `NAME[i]` as a field value, or `len(NAME)`.
            Expr::Index(..) => self.const_array_elem(e),
            Expr::Call(f, args) if f == "f192" && args.len() == 3 => {
                let limb = |i: usize| match &args[i] {
                    Expr::Lit(n) => u64::try_from(*n).ok(),
                    _ => None,
                };
                Some(F192::new(limb(0)?, limb(1)?, limb(2)?))
            }
            // `const(e)`: the one place a value position reads INTEGER arithmetic,
            // because the author asked for it. Without it `v = lvl + 1` is
            // `lvl XOR 1`, silently, since `+` in a value position is XOR.
            Expr::Call(f, args) if f == "const" && args.len() == 1 => {
                self.check_const_leaves(&args[0]);
                Some(lit_field(self.try_const_int(&args[0])?))
            }
            Expr::Call(..) => self.const_len(e).map(|n| F192::new(n as u64, 0, 0)),
            // `b ** e` as a field constant (constant base, compile-time exponent).
            Expr::Pow(b, e) => Some(field_pow(self.try_field_const(b)?, self.try_const_index(e)?)),
            _ => None,
        }
    }
}
