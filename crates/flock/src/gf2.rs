//! Symbolic GF(2) words and the 32-bit adder gadgets the hash circuits share.
//!
//! BLAKE2s is a 32-bit ARX round whose XORs and rotations are free over GF(2)
//! and whose only nonlinear constraints are the product bits of the modular
//! ADDs. This module owns that part, separately from the hash's schedule and
//! layout, because the adder algebra is where the subtlety lives: the fused
//! three-operand gadget's bit-0 and bit-31 boundaries are what make the
//! ten-round encoding fit, and they get their own tests here and in the
//! circuit.
//!
//! Two representations of the same thing appear here, and they have to agree
//! row for row:
//!
//! - [`Word`], a symbolic 32-bit word carrying a *list of slot indices* per
//!   bit, used by the matrix builders to emit sparse rows.
//! - [`WireWord`], the same word carrying an *`F192` value* per bit, used by
//!   the circuit walk to evaluate `uᵀ A₀ w` and `uᵀ B₀ w` in O(circuit) field
//!   ops without materializing the substituted matrices.
//!
//! Each gadget therefore comes in a `write_*` (rows) and a `walk_*` (wires)
//! flavour, and `blake2s`'s `bilinear_walk_matches_matrices` test is what pins
//! the two together.

use crate::witness::xor_dedup;
use primitives::field::F192;

/// Bits per word.
pub(crate) const WORD_BITS: usize = 32;
/// Carry_aux bits per 32-bit two-operand ADD (bit 0..30; bit 31 is the
/// discarded mod-2³² carry-out and isn't allocated).
pub(crate) const CARRY_BITS_PER_ADD: usize = WORD_BITS - 1; // 31
/// Ripple-layer product bits per fused three-operand ADD (bit 1..30): bit 0's
/// product is `p₀ · 0`, since the shifted majority word's bit 0 is zero.
pub(crate) const RIPPLE_BITS_PER_ADD3: usize = WORD_BITS - 2; // 30
/// Product slots per fused three-operand ADD: 31 majorities + 30 ripple.
pub(crate) const ADD3_BITS: usize = CARRY_BITS_PER_ADD + RIPPLE_BITS_PER_ADD3; // 61

// ---------------------------------------------------------------------------
// Symbolic words (matrix builder side)
// ---------------------------------------------------------------------------

/// A 32-bit symbolic word. `bits[i]` is a list of slot indices whose XOR
/// equals bit `i` of the word.
#[derive(Clone)]
pub(crate) struct Word {
    pub(crate) bits: [Vec<usize>; WORD_BITS],
}

impl Word {
    pub(crate) fn zero() -> Self {
        Self {
            bits: std::array::from_fn(|_| Vec::new()),
        }
    }
    /// Construct from a 32-bit witness or lin-id slot whose 32 bits live at
    /// `[base + 0, base + 1, …, base + 31]`.
    pub(crate) fn from_slot_base(base: usize) -> Self {
        Self {
            bits: std::array::from_fn(|i| vec![base + i]),
        }
    }
    /// Construct from a 32-bit constant: bit `i` is `[const_pos]`, the
    /// circuit's constant wire, if set, and `[]` otherwise.
    pub(crate) fn from_const(val: u32, const_pos: usize) -> Self {
        Self {
            bits: std::array::from_fn(|i| {
                if (val >> i) & 1 == 1 {
                    vec![const_pos]
                } else {
                    Vec::new()
                }
            }),
        }
    }
    /// Bitwise XOR, no dedup. Caller calls `dedup()` after a chain if it
    /// wants canonical rows.
    pub(crate) fn xor(&self, other: &Word) -> Word {
        let mut out = self.clone();
        for i in 0..WORD_BITS {
            out.bits[i].extend(&other.bits[i]);
        }
        out
    }
    /// `rotr(n)`: pure index permutation, doesn't touch slot lists.
    pub(crate) fn rotr(&self, n: usize) -> Word {
        Word {
            bits: std::array::from_fn(|i| self.bits[(i + n) % WORD_BITS].clone()),
        }
    }
    /// Sort + cancel duplicates per bit.
    pub(crate) fn dedup(mut self) -> Word {
        for i in 0..WORD_BITS {
            self.bits[i] = xor_dedup(std::mem::take(&mut self.bits[i]));
        }
        self
    }
    /// "Sum bit" lin_func of an ADD `x + y` whose carry_aux slots live at
    /// `[carry_base, carry_base + 31)`.
    ///
    ///   sum[i] = x[i] ⊕ y[i] ⊕ ⊕_{j<i} carry_aux[j]
    fn add_sum(x: &Word, y: &Word, carry_base: usize) -> Word {
        let mut out = Word::zero();
        for i in 0..WORD_BITS {
            let mut v = x.bits[i].clone();
            v.extend(&y.bits[i]);
            for j in 0..i {
                v.push(carry_base + j);
            }
            out.bits[i] = v;
        }
        out.dedup()
    }
}

// ---------------------------------------------------------------------------
// Per-ADD: write the 31 carry_aux rows and return the sum-bit `Word`.
//
//   carry_aux[i] = (X[i] ⊕ cin[i]) · (Y[i] ⊕ cin[i])   (R1CS AND row)
//   sum[i]       = X[i] ⊕ Y[i] ⊕ cin[i]                (no slot, lin_func)
//
// where cin[i] = ⊕_{j<i} carry_aux[j].
// ---------------------------------------------------------------------------

pub(crate) fn write_add_carry_rows(
    a_rows: &mut [Vec<usize>],
    b_rows: &mut [Vec<usize>],
    x: &Word,
    y: &Word,
    carry_base: usize,
) -> Word {
    for i in 0..CARRY_BITS_PER_ADD {
        let mut a = x.bits[i].clone();
        for j in 0..i {
            a.push(carry_base + j);
        }
        let mut b = y.bits[i].clone();
        for j in 0..i {
            b.push(carry_base + j);
        }
        a_rows[carry_base + i] = xor_dedup(a);
        b_rows[carry_base + i] = xor_dedup(b);
    }
    Word::add_sum(x, y, carry_base)
}

// ---------------------------------------------------------------------------
// Per fused three-operand ADD `x + y + z`: write the 31 majority rows and the
// 30 ripple rows, and return the sum-bit `Word`.
//
// Carry-save layer, slots `[base, base + 31)`:
//
//   maj_aux[i] = (X[i] ⊕ Z[i]) · (Y[i] ⊕ Z[i])       (R1CS AND row)
//   maj[i]     = maj_aux[i] ⊕ Z[i]                   (majority, affine)
//
// since over GF(2) `(x+z)(y+z) = xy ⊕ xz ⊕ yz ⊕ z`. Then `x + y + z` equals
// `p + 2·maj` with `p[i] = X[i] ⊕ Y[i] ⊕ Z[i]`, so the ripple layer at slots
// `[base + 31, base + 61)` adds `p` against `q[i] = maj[i-1]`, `q[0] = 0`:
//
//   rip_aux[i] = (p[i] ⊕ cin[i]) · (q[i] ⊕ cin[i]),  i = 1..30
//   sum[i]     = p[i] ⊕ q[i] ⊕ cin[i]                (no slot, lin_func)
//
// with `cin[i] = ⊕_{1 ≤ j < i} rip_aux[j]`. Bit 0 needs no row: `q[0] = 0` and
// `cin[0] = 0` make its product identically zero, hence `cin[1] = 0` too, and
// slot `base + 31 + i − 1` carries bit `i`. `maj[31]` would weigh 2³², so the
// majority layer stops at bit 30 like a two-operand carry chain.
//
// Pass the sparsest operand as `z`: it appears in both layer-1 rows and in
// both `p` and `q`, roughly twice as often as `x` or `y`.
// ---------------------------------------------------------------------------

pub(crate) fn write_add3_fused_rows(
    a_rows: &mut [Vec<usize>],
    b_rows: &mut [Vec<usize>],
    x: &Word,
    y: &Word,
    z: &Word,
    base: usize,
) -> Word {
    let rip_base = base + CARRY_BITS_PER_ADD;
    for i in 0..CARRY_BITS_PER_ADD {
        let mut a = x.bits[i].clone();
        a.extend(&z.bits[i]);
        let mut b = y.bits[i].clone();
        b.extend(&z.bits[i]);
        a_rows[base + i] = xor_dedup(a);
        b_rows[base + i] = xor_dedup(b);
    }

    let mut p = Word::zero();
    let mut q = Word::zero();
    for i in 0..WORD_BITS {
        let mut v = x.bits[i].clone();
        v.extend(&y.bits[i]);
        v.extend(&z.bits[i]);
        p.bits[i] = xor_dedup(v);
        if i > 0 {
            let mut v = vec![base + i - 1];
            v.extend(&z.bits[i - 1]);
            q.bits[i] = xor_dedup(v);
        }
    }

    // `cin[i]`, empty for i ∈ {0, 1}.
    let cin = |i: usize| (1..i).map(|j| rip_base + j - 1);
    for i in 1..=RIPPLE_BITS_PER_ADD3 {
        let mut a = p.bits[i].clone();
        a.extend(cin(i));
        let mut b = q.bits[i].clone();
        b.extend(cin(i));
        a_rows[rip_base + i - 1] = xor_dedup(a);
        b_rows[rip_base + i - 1] = xor_dedup(b);
    }

    let mut out = Word::zero();
    for i in 0..WORD_BITS {
        let mut v = p.bits[i].clone();
        v.extend(&q.bits[i]);
        v.extend(cin(i));
        out.bits[i] = v;
    }
    out.dedup()
}

/// Write 32 consecutive `lin_func · 1 = slot` rows: the "lin-id" shape that
/// materializes an affine word into its own slots, breaking the cascade.
pub(crate) fn write_lin_word_rows(
    a_rows: &mut [Vec<usize>],
    b_rows: &mut [Vec<usize>],
    val: &Word,
    base: usize,
    const_pos: usize,
) {
    for i in 0..WORD_BITS {
        a_rows[base + i] = val.bits[i].clone();
        b_rows[base + i] = vec![const_pos];
    }
}

// ---------------------------------------------------------------------------
// Circuit-walk evaluation (wire side)
//
// Evaluates the two bilinear forms `uᵀ A_0 w` and `uᵀ B_0 w` for arbitrary row
// weights `u` and column weights `w` by walking the UNSUBSTITUTED circuit
// forward: the same cascade the matrix builder threads symbolically, evaluated
// over F192 values. A lane is a 32-vector of wire values; a committed slot
// contributes `w[slot]`, an intermediate wire the running linear combination.
// Row `i`'s contribution `u[i]·⟨A_i, w⟩` is accumulated exactly where the
// builder would emit that row, with `⟨row, w⟩` read off the threaded wires.
// Cost: O(circuit) field ops, never the millions of substituted nonzeros, and
// the matrices need not be materialized at all. This is what lets a verifier
// evaluate the matrix MLEs directly instead of deferring the claim.
// ---------------------------------------------------------------------------

/// One lane's wire values: bit `i` of the word, as the F192 combination
/// `⟨lin_func_i, w⟩`.
pub(crate) type WireWord = [F192; WORD_BITS];

#[inline]
pub(crate) fn wire_from_slot_base(w: &[F192], base: usize) -> WireWord {
    std::array::from_fn(|i| w[base + i])
}

/// Constant word: a set bit is the constant-wire lin_func, a clear bit empty.
#[inline]
pub(crate) fn wire_from_const(w: &[F192], val: u32, const_pos: usize) -> WireWord {
    std::array::from_fn(|i| if (val >> i) & 1 == 1 { w[const_pos] } else { F192::ZERO })
}

#[inline]
pub(crate) fn wire_xor(x: &WireWord, y: &WireWord) -> WireWord {
    std::array::from_fn(|i| x[i] + y[i])
}

#[inline]
pub(crate) fn wire_rotr(x: &WireWord, n: usize) -> WireWord {
    std::array::from_fn(|i| x[(i + n) % WORD_BITS])
}

/// Pair of accumulators for the A-side and B-side bilinear forms, plus the
/// running sum of `u` over rows whose B-side is the single constant-wire entry
/// (lin-id / free-input rows), factored so those rows cost one B-side
/// F-addition instead of a multiplication each.
pub(crate) struct WalkAcc {
    pub(crate) a: F192,
    pub(crate) b: F192,
    /// Σ u[row] over rows with `B_row = [const_pos]`; folded in once at the
    /// end as `b += w[const_pos] · u_bconst`.
    pub(crate) u_bconst: F192,
}

impl WalkAcc {
    pub(crate) fn zero() -> Self {
        Self {
            a: F192::ZERO,
            b: F192::ZERO,
            u_bconst: F192::ZERO,
        }
    }

    /// A free-input row `A = [slot]`, `B = [const_pos]`, for each slot in
    /// `[base, base + len)`.
    pub(crate) fn free_input_rows(&mut self, u: &[F192], w: &[F192], base: usize, len: usize) {
        for s in base..base + len {
            self.a += u[s] * w[s];
            self.u_bconst += u[s];
        }
    }

    /// Walk 32 consecutive `lin_func · 1` rows: row `base + i` has
    /// `A = <wire bit i>`, `B = [const_pos]`.
    pub(crate) fn lin_word_rows(&mut self, u: &[F192], vals: &WireWord, base: usize) {
        for i in 0..WORD_BITS {
            self.a += u[base + i] * vals[i];
            self.u_bconst += u[base + i];
        }
    }

    /// Fold in the factored constant-B and constant-A/B row sums, yielding
    /// `(uᵀ A₀ w, uᵀ B₀ w)`. `u_abconst` is `Σ u[row]` over rows with
    /// `A = B = [const_pos]`.
    pub(crate) fn finish(self, w: &[F192], const_pos: usize, u_abconst: F192) -> (F192, F192) {
        let wc = w[const_pos];
        (self.a + wc * u_abconst, self.b + wc * (self.u_bconst + u_abconst))
    }
}

/// Walk one 32-bit ADD (mirror of [`write_add_carry_rows`]): accumulate the 31
/// carry rows into `acc` and return the sum-bit wires.
///
///   carry row cb+i:  A = X[i] ⊕ cin[i],  B = Y[i] ⊕ cin[i]
///   sum[i]         = X[i] ⊕ Y[i] ⊕ cin[i]
///
/// with `cin[i] = ⊕_{j<i} carry_aux[cb+j]`, a running prefix of `w` reads.
pub(crate) fn walk_add(
    acc: &mut WalkAcc,
    u: &[F192],
    w: &[F192],
    x: &WireWord,
    y: &WireWord,
    carry_base: usize,
) -> WireWord {
    let mut out = [F192::ZERO; WORD_BITS];
    let mut cin = F192::ZERO;
    for i in 0..WORD_BITS {
        let a_side = x[i] + cin;
        let b_side = y[i] + cin;
        out[i] = a_side + y[i];
        if i < CARRY_BITS_PER_ADD {
            let ui = u[carry_base + i];
            acc.a += ui * a_side;
            acc.b += ui * b_side;
            cin += w[carry_base + i];
        }
    }
    out
}

/// Walk one fused three-operand ADD (mirror of [`write_add3_fused_rows`]):
/// accumulate the 31 majority rows and the 30 ripple rows into `acc` and
/// return the sum-bit wires.
pub(crate) fn walk_add3_fused(
    acc: &mut WalkAcc,
    u: &[F192],
    w: &[F192],
    x: &WireWord,
    y: &WireWord,
    z: &WireWord,
    base: usize,
) -> WireWord {
    let rip_base = base + CARRY_BITS_PER_ADD;
    let mut maj = [F192::ZERO; CARRY_BITS_PER_ADD];
    for i in 0..CARRY_BITS_PER_ADD {
        let ui = u[base + i];
        acc.a += ui * (x[i] + z[i]);
        acc.b += ui * (y[i] + z[i]);
        maj[i] = w[base + i] + z[i];
    }

    let mut out = [F192::ZERO; WORD_BITS];
    let mut cin = F192::ZERO;
    for i in 0..WORD_BITS {
        let q_i = if i == 0 { F192::ZERO } else { maj[i - 1] };
        let a_side = x[i] + y[i] + z[i] + cin;
        out[i] = a_side + q_i;
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            let ui = u[rip_base + i - 1];
            acc.a += ui * a_side;
            acc.b += ui * (q_i + cin);
            cin += w[rip_base + i - 1];
        }
    }
    out
}
