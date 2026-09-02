//! The precompile and the hints: the two places a value arrives without an
//! instruction computing it.
//!
//! `blake2s` is a STATEMENT, not an expression: it writes its digest into a
//! two-cell run the caller names, so a pre-written destination checks the digest
//! instead of computing it, by the same write-once rule as any store.
//!
//! A hint writes values the prover chose and the circuit did not, so **the
//! program must constrain them**. A hint names its destination's PHYSICAL cells,
//! and since every store emits there is nothing for the compiler to prepare: a
//! later `s[k] = <checked value>` is a second write of that cell, which is the
//! assertion that pins the hinted value.

use super::*;

impl FnLower<'_> {
    /// `blake2s(a, b, out)`: the digest of the two 256-bit operands lands in the
    /// existing 2-cell run `out` (write-once: if `out` was already written, this
    /// asserts the digest equals it). A heap `out` slice takes the digest via a
    /// fresh stack pair and two `DEREF`s after the hash, the store direction
    /// being the same instruction as the load (write-once fills the unset side).
    /// Keyword arguments set the metadata: `counter=` / `final=` / `last_node=`
    /// build it at compile time, `md=` takes the whole word from a value the
    /// program computed.
    fn lower_blake2s(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 3 {
            self.fail("blake2s takes three positional arguments: (a, b, out)")
        };
        if !(args[first_kw..]
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the three positional blake2s arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in &args[first_kw..] {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate blake2s keyword `{key}`"))
            };
        }
        let allowed = ["cv", "counter", "final", "last_node", "md"];
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            // Sorted: a `HashMap`'s order would make the same mistake report
            // differently between builds.
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown blake2s keyword {bad:?}; the keywords are {allowed:?}"))
        };
        let customized = kwargs.keys().any(|k| matches!(*k, "counter" | "final" | "last_node"));
        // `md=` hands over the whole metadata word as a runtime value, so it
        // replaces the three keywords that would otherwise build it.
        let runtime_md = kwargs.get("md").copied();
        if runtime_md.is_some() && customized {
            self.fail("blake2s md= is the whole metadata word, so counter=, final= and last_node= cannot come with it")
        };
        if kwargs.contains_key("cv") && !customized && runtime_md.is_none() {
            self.fail(
                "blake2s with cv= requires one of counter=, final=, last_node= or md=, since a chained \
                 block is not the default one-block hash",
            )
        };

        let a = self.blake2s_input(&args[0]);
        let b = self.blake2s_input(&args[1]);
        let (c, heap_out) = match self.blake2s_operand(&args[2]) {
            CellRun::Stack { base, .. } => (base, None),
            CellRun::Heap { ptr, lo, .. } => (self.alloc_stack(2), Some((ptr, lo))),
        };
        let cv = if let Some(value) = kwargs.get("cv") {
            self.blake2s_cv(value)
        } else {
            self.default_blake2s_cv()
        };
        let md = match runtime_md {
            // A metadata word the program computes, which is what lets a hash whose
            // block count is only known at run time carry the byte counter the
            // standard asks for (doc §sec:prog-byte-counter). It owes the same
            // canonical embedding as every other operand: the memory interaction
            // carries a literal zero above its two low limbs.
            //
            // Aliasing the digest destination is the one case write-once does not
            // catch: the runner reads the metadata before storing the digest, while
            // the witness reads the finished memory image, so the two disagree and
            // the proof fails its opening rather than saying why.
            Some(expr) => {
                let md = self.expr(expr);
                if md == c || md == c + 1 {
                    self.fail("blake2s md= must not name a cell of the digest destination")
                };
                md
            }
            None => {
                let const_kw = |this: &Self, name: &str, default: u128| -> u128 {
                    kwargs
                        .get(name)
                        .map(|e| {
                            this.try_const_int(e).unwrap_or_else(|| {
                                self.fail(format!(
                                    "BLAKE2s `{name}` must be a compile-time integer, got `{e:?}`; \
                                     a metadata word computed at run time goes through md="
                                ))
                            })
                        })
                        .unwrap_or(default)
                };
                // BLAKE2s metadata is just the cumulative byte counter and two flags, so
                // a multi-block hash is `counter = 64 * blocks_before + bytes_in_this_block`
                // and `final = 1` on the last block. The default is the one-block hash of
                // a full 64-byte input, which is what `vmhash::compress` and every Merkle
                // node use.
                let counter = const_kw(self, "counter", 64);
                let counter = u64::try_from(counter)
                    .unwrap_or_else(|_| self.fail(format!("blake2s counter= {counter} does not fit in u64")));
                let f0 = if const_kw(self, "final", if customized { 0 } else { 1 }) != 0 {
                    lean_vm::hash_flock::FINAL_FLAG
                } else {
                    0
                };
                let f1 = if const_kw(self, "last_node", 0) != 0 {
                    u32::MAX
                } else {
                    0
                };
                // A compile-time metadata is a pooled `SET`: one per distinct value
                // per frame, however many compressions read it.
                self.const_cell(lean_vm::hash_flock::metadata(counter, f0, f1))
            }
        };
        // Each operand is two 128-bit chunk cells; the flexible opcode addresses
        // the four input cells independently (`blake2s_input` forwards the real
        // chunk sources where it can). The digest occupies the two consecutive
        // output cells `c, g·c`.
        self.emit(LOp::Blake2s {
            ins: [a[0], a[1], b[0], b[1]],
            cv,
            c,
            md,
        });
        if let Some((ptr, lo)) = heap_out {
            for k in 0..2 {
                self.deref(ptr, lo + k, c + k, DerefMode::Cell);
            }
        }
    }

    /// The statement-position builtins, `true` if `f` was one of them (else the
    /// caller emits an ordinary call). The `hint_*` ones queue prover-side
    /// advice, re-checked in-circuit by their caller: `hint_decompose_bits`
    /// writes a value's bits into a buffer, `hint_decompose_bits_exponent` the
    /// bits of `n` where the value is `g^n` (a bounded dlog at witness
    /// generation), `hint_f192_limbs` a value's coordinate limbs.
    pub(super) fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                if args.len() != 3 {
                    self.fail(format!(
                        "{f} takes three arguments, `(bits, value, nbits)`, got {}",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(if f == "hint_decompose_bits" {
                    RHint::BitDecompose { value, bits, nbits }
                } else {
                    RHint::BitDecomposeExp { value, bits, nbits }
                }));
            }
            "blake2s" => self.lower_blake2s(args),
            "assert_in_k" => {
                if args.len() != 2 {
                    self.fail("assert_in_k(a, b) takes two scalar cells")
                };
                let a = self.expr(&args[0]);
                let b = self.expr(&args[1]);
                let zero = self.zero();
                self.emit(LOp::Jump { oc: zero, od: a, of: b });
            }
            "hint_f192_limbs" => {
                if args.len() != 2 {
                    self.fail(format!(
                        "hint_f192_limbs takes two arguments, `(dest, value)`, got {}",
                        args.len()
                    ))
                };
                let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
                    self.fail(format!(
                        "hint_f192_limbs writes 1..=3 frame cells, so its destination must be a \
                             StackBuf, got `{:?}`",
                        args[0]
                    ))
                });
                if !((1..=3).contains(&len)) {
                    self.fail("hint_f192_limbs destination must have 1..=3 cells")
                };
                let value = self.expr(&args[1]);
                // Names the physical cells, as the two consumers above do: whatever
                // the program stores into them afterwards is a second write, and so
                // the assertion that pins these limbs.
                self.pending
                    .push(Hint::Resolved(RHint::FieldLimbs { value, base, len }));
            }
            _ => return false,
        }
        true
    }

    /// Resolve a `blake2s` operand: a [`Self::cell_run`] pinned to exactly 2
    /// cells, a 256-bit value being two 128-bit cells. Stack operands are used
    /// in place; heap operands must be bridged through the stack, since
    /// `BLAKE2s` addresses only frame cells (see [`Self::blake2s_input`]).
    fn blake2s_operand(&mut self, e: &Expr) -> CellRun {
        let run = self.cell_run(e);
        if run.cells() != 2 {
            self.fail("a blake2s operand must span exactly 2 cells (two 128-bit words); slice a larger buffer: `buf[lo:lo + 2]`")
        };
        run
    }

    /// A `blake2s` *input* operand as its two independently-addressed 128-bit
    /// chunk bases (each chunk is ONE 128-bit cell): stack runs in place; a heap
    /// slice is pulled into a fresh stack pair first, one `DEREF` per cell
    /// (`m[ptr·g^{lo+k}] == m[fp+t+k]`, the `β` immediate doing the pointer
    /// offset). The heap cells must already be written.
    ///
    /// A LIST LITERAL names its two words directly and allocates nothing. The
    /// opcode addresses its four input chunks independently, so an operand
    /// assembled out of values living elsewhere never has to be gathered into a
    /// consecutive run: `blake2s([a, b], …)` is the spelling that says so.
    pub(super) fn blake2s_input(&mut self, e: &Expr) -> [Off; 2] {
        if let Expr::ListLit(words) = e {
            if words.len() != 2 {
                self.fail(format!(
                    "a blake2s operand written as a list needs exactly 2 words, got {}",
                    words.len()
                ))
            };
            return [self.expr(&words[0]), self.expr(&words[1])];
        }
        match self.blake2s_operand(e) {
            CellRun::Stack { base, .. } => [base, base + 1],
            CellRun::Heap { ptr, lo, .. } => {
                let t = self.alloc_stack(2);
                for k in 0..2 {
                    self.deref(ptr, lo + k, t + k, DerefMode::Cell);
                }
                [t, t + 1]
            }
        }
    }

    fn default_blake2s_cv(&mut self) -> Off {
        if let Some(o) = self.scope.blake2s_iv {
            return o;
        }
        let o = self.alloc_stack(2);
        for (k, value) in lean_vm::hash_flock::IV_CELLS.into_iter().enumerate() {
            self.set_const(o + k as u32, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k as u32);
        }
        self.scope.blake2s_iv = Some(o);
        o
    }

    /// A computed-advice bit buffer's destination ([`BitsDest`]). Not
    /// [`Self::cell_run`]: these builtins take a bare `HeapBuf` and carry the
    /// length in `nbits`, where a cell run would demand a slice.
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> BitsDest {
        match self.stack_of(e) {
            Some((base, len)) => {
                if len < nbits {
                    self.fail(format!(
                        "{what} needs {nbits} cells, its StackBuf destination has {len}"
                    ))
                };
                // The hint names the physical cells, as `hint_f192_limbs` does.
                BitsDest::Stack(base)
            }
            None => {
                // Bounds-checked like the `StackBuf` arm above, and like every
                // other heap consumer. Without this a `HeapBuf` destination wrote
                // `nbits` cells with nothing checking the buffer held them, so the
                // bits ran on into the next buffer while the same call with a
                // `StackBuf` destination was rejected.
                self.check_heap_bound(e, 0, u128::from(nbits));
                BitsDest::Heap(self.expr(e))
            }
        }
    }

    /// `hint_witness(dest, "name")`: resolve `dest` to a run of cells and
    /// queue the witness-fill hint (no instructions: the values are written
    /// by the runner before the next instruction executes, unconstrained).
    pub(super) fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match self.cell_run(dest) {
            CellRun::Stack { base, len } => RHint::WitnessStack { name, base, len },
            CellRun::Heap { ptr, lo, len } => RHint::WitnessHeap { name, ptr, lo, len },
        };
        self.pending.push(Hint::Resolved(hint));
    }
    /// A BLAKE2s chaining value must occupy two consecutive frame cells because
    /// the opcode carries one base offset for both words. Preserve a genuine
    /// consecutive pair, including a heap pair already bridged by
    /// [`Self::blake2s_input`]. A `cv` written as a two-word LIST exposes two
    /// sources that need not be adjacent, so those are copied into a fresh
    /// consecutive pair.
    fn blake2s_cv(&mut self, e: &Expr) -> Off {
        let pair = self.blake2s_input(e);
        if pair[1] == pair[0] + 1 {
            return pair[0];
        }
        let cv = self.alloc_stack(2);
        self.copy(pair[0], cv);
        self.copy(pair[1], cv + 1);
        cv
    }
}
