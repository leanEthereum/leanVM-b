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
//! A word is a [`WireWord`], 32 `F192` values, one per bit, and each gadget
//! comes in a `walk_*` flavour that threads them forwards and a `back_*` that
//! threads the adjoints backwards. The matrices the two describe are never
//! built: forwards gives `uᵀ A₀ w` and `uᵀ B₀ w` (and, kept per row, `A₀ w`
//! and `B₀ w`), backwards gives the column marginal `(A₀ + α B₀)ᵀ u`. The pair is
//! cross-checked by the protocol itself: lincheck's terminal identity is exactly
//! the assertion that the backward walk's marginal, contracted against the
//! column weights, equals the forward walk's bilinear form.

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

/// Where the forward walk sends each row's operand pair
/// `(⟨A_0(k,·), w⟩, ⟨B_0(k,·), w⟩)`.
///
/// [`WalkAcc`] contracts the pairs against row weights as they appear, giving
/// the two bilinear forms; [`RowValues`] keeps them, giving the matrix-vector
/// products `(A_0 w, B_0 w)`. One gadget body feeds both, so the two readings of
/// a row cannot drift.
pub(crate) trait RowSink {
    /// A product row: both sides are walked wire values.
    fn product(&mut self, k: usize, a: F192, b: F192);
    /// A row whose B side is the lone constant wire: free inputs, lin-id words,
    /// and the constant row itself, whose A side is that same entry.
    fn bconst(&mut self, k: usize, a: F192);
}

/// Contracting sink: accumulates `uᵀ A_0 w` and `uᵀ B_0 w`. Rows whose B side is
/// the single constant entry share the factor `w[const_pos]`, so their B side
/// costs one addition here and one multiplication in [`WalkAcc::finish`].
pub(crate) struct WalkAcc<'a> {
    u: &'a [F192],
    wc: F192,
    a: F192,
    b: F192,
    u_bconst: F192,
}

impl<'a> WalkAcc<'a> {
    pub(crate) fn new(u: &'a [F192], wc: F192) -> Self {
        Self {
            u,
            wc,
            a: F192::ZERO,
            b: F192::ZERO,
            u_bconst: F192::ZERO,
        }
    }

    /// `(uᵀ A_0 w, uᵀ B_0 w)`.
    pub(crate) fn finish(self) -> (F192, F192) {
        (self.a, self.b + self.wc * self.u_bconst)
    }
}

impl RowSink for WalkAcc<'_> {
    #[inline]
    fn product(&mut self, k: usize, a: F192, b: F192) {
        let ui = self.u[k];
        self.a += ui * a;
        self.b += ui * b;
    }
    #[inline]
    fn bconst(&mut self, k: usize, a: F192) {
        self.a += self.u[k] * a;
        self.u_bconst += self.u[k];
    }
}

/// Storing sink: keeps every row's operand pair, so the walk returns the
/// matrix-vector products `(A_0 w, B_0 w)` in O(circuit) additions instead of
/// one pass over the nonzeros. Rows with no wire keep their zeros.
pub(crate) struct RowValues {
    pub(crate) a: Vec<F192>,
    pub(crate) b: Vec<F192>,
    wc: F192,
}

impl RowValues {
    pub(crate) fn new(k: usize, wc: F192) -> Self {
        Self {
            a: vec![F192::ZERO; k],
            b: vec![F192::ZERO; k],
            wc,
        }
    }
}

impl RowSink for RowValues {
    #[inline]
    fn product(&mut self, k: usize, a: F192, b: F192) {
        self.a[k] = a;
        self.b[k] = b;
    }
    #[inline]
    fn bconst(&mut self, k: usize, a: F192) {
        self.a[k] = a;
        self.b[k] = self.wc;
    }
}

/// Walk one 32-bit ADD: report the 31
/// carry rows to `sink` and return the sum-bit wires.
///
///   carry row cb+i:  A = X[i] ⊕ cin[i],  B = Y[i] ⊕ cin[i]
///   sum[i]         = X[i] ⊕ Y[i] ⊕ cin[i]
///
/// with `cin[i] = ⊕_{j<i} carry_aux[cb+j]`, a running prefix of `w` reads.
pub(crate) fn walk_add<S: RowSink>(
    sink: &mut S,
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
            sink.product(carry_base + i, a_side, b_side);
            cin += w[carry_base + i];
        }
    }
    out
}

/// Walk one fused three-operand ADD:
/// report the 31 majority rows and the 30 ripple rows to `sink` and
/// return the sum-bit wires.
pub(crate) fn walk_add3_fused<S: RowSink>(
    sink: &mut S,
    w: &[F192],
    x: &WireWord,
    y: &WireWord,
    z: &WireWord,
    base: usize,
) -> WireWord {
    let rip_base = base + CARRY_BITS_PER_ADD;
    let mut maj = [F192::ZERO; CARRY_BITS_PER_ADD];
    for i in 0..CARRY_BITS_PER_ADD {
        sink.product(base + i, x[i] + z[i], y[i] + z[i]);
        maj[i] = w[base + i] + z[i];
    }

    let mut out = [F192::ZERO; WORD_BITS];
    let mut cin = F192::ZERO;
    for i in 0..WORD_BITS {
        let q_i = if i == 0 { F192::ZERO } else { maj[i - 1] };
        let a_side = x[i] + y[i] + z[i] + cin;
        out[i] = a_side + q_i;
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            sink.product(rip_base + i - 1, a_side, q_i + cin);
            cin += w[rip_base + i - 1];
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Backward walk (the marginal side)
//
// The forward walk above evaluates `S(w) = uᵀ(A_0 + α·B_0) w`, which is LINEAR
// in `w`, so `S(w) = ⟨M, w⟩` for the α-batched column marginal
//
//   M[j] = Σ_k (A_0(k,j) + α·B_0(k,j))·u[k],   i.e. M = (A_0 + α·B_0)ᵀ u.
//
// So `M` is the gradient of the forward walk with respect to `w`, and
// reverse-mode differentiation of that walk produces the WHOLE marginal in
// O(circuit) field ops, where the sparse gather pays O(nnz) and needs the
// matrices materialized. Each `back_*` below is the transpose of the matching
// `walk_*`: it takes the adjoint of the gadget's sum word, deposits the
// marginal entries owned by the gadget's own slots, and returns the adjoints of
// its operands. `blake2s::marginal_walk` threads them in reverse topological
// order. Since `\alpha` weights the B side, an operand on the B side of a row
// picks up `α·u[row]` where the A side picks up `u[row]`.
// ---------------------------------------------------------------------------

/// Transpose of [`wire_rotr`]: `wire_rotl(x, n)[i] = x[(i + WORD_BITS - n) % WORD_BITS]`,
/// so that `⟨wire_rotr(x, n), a⟩ = ⟨x, wire_rotl(a, n)⟩`.
#[inline]
pub(crate) fn wire_rotl(x: &WireWord, n: usize) -> WireWord {
    std::array::from_fn(|i| x[(i + WORD_BITS - n) % WORD_BITS])
}

/// Transpose of [`walk_add`], whose rows it must mirror exactly. `adj` is the adjoint of the sum word; deposits the
/// marginal entries of the 31 carry_aux slots into `m` and returns the adjoints
/// of `x` and `y`.
///
/// Row `carry_base+i` has `A = x[i] + cin_i`, `B = y[i] + cin_i`, and
/// `sum[i] = x[i] + y[i] + cin_i`, with `cin_i = ⊕_{j<i} carry_aux[j]`. So
/// slot `carry_base+j` is read by every `cin_i` with `i > j`, and its marginal
/// entry is the suffix sum of the `cin_i` adjoints, walked from the top bit down.
pub(crate) fn back_add(
    m: &mut [F192],
    u: &[F192],
    adj: &WireWord,
    carry_base: usize,
    alpha: F192,
) -> (WireWord, WireWord) {
    let mut ax = [F192::ZERO; WORD_BITS];
    let mut ay = [F192::ZERO; WORD_BITS];
    let mut suffix = F192::ZERO;
    for i in (0..WORD_BITS).rev() {
        let mut cin_adj = adj[i];
        if i < CARRY_BITS_PER_ADD {
            m[carry_base + i] += suffix;
            let p = u[carry_base + i];
            let pa = alpha * p;
            ax[i] = adj[i] + p;
            ay[i] = adj[i] + pa;
            cin_adj += p + pa;
        } else {
            ax[i] = adj[i];
            ay[i] = adj[i];
        }
        suffix += cin_adj;
    }
    (ax, ay)
}

/// Transpose of [`walk_add3_fused`]. Deposits the marginal entries of the 31
/// majority slots and the 30 ripple slots, and returns the adjoints of `x`, `y`
/// and `z`.
///
/// Majority row `base+i` has `A = x[i] + z[i]`, `B = y[i] + z[i]`, and
/// `maj[i] = maj_aux[i] + z[i]` feeds the ripple layer as `q[i+1]`, which is
/// why `z` and the majority slots both pick up that `q` adjoint. Ripple row
/// `rip_base+i-1` has `A = p_i + cin_i`, `B = q_i + cin_i` with
/// `p_i = x[i]+y[i]+z[i]`, and its slots are read by every later `cin`, hence
/// the second suffix sum.
pub(crate) fn back_add3_fused(
    m: &mut [F192],
    u: &[F192],
    adj: &WireWord,
    base: usize,
    alpha: F192,
) -> (WireWord, WireWord, WireWord) {
    let rip_base = base + CARRY_BITS_PER_ADD;
    let mut ax = [F192::ZERO; WORD_BITS];
    let mut ay = [F192::ZERO; WORD_BITS];
    let mut az = [F192::ZERO; WORD_BITS];
    // Ripple row weight at bit `i`, zero where the layer has no row.
    let rip = |i: usize| -> F192 {
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            u[rip_base + i - 1]
        } else {
            F192::ZERO
        }
    };
    // `q_i` is read by `out[i]` and by the ripple row's B side.
    let q_adj = |i: usize| -> F192 { adj[i] + alpha * rip(i) };
    let mut suffix = F192::ZERO;
    for i in (0..WORD_BITS).rev() {
        let ri = rip(i);
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            m[rip_base + i - 1] += suffix;
        }
        suffix += adj[i] + ri + alpha * ri;
        // `p_i = x[i]+y[i]+z[i]` reaches out[i] and the ripple row's A side.
        let common = adj[i] + ri;
        let (mut xi, mut yi, mut zi) = (common, common, common);
        if i < CARRY_BITS_PER_ADD {
            let mi = u[base + i];
            let mia = alpha * mi;
            xi += mi;
            yi += mia;
            zi += mi + mia;
            // maj[i] = maj_aux[i] + z[i] is the ripple layer's q[i+1].
            let qa = q_adj(i + 1);
            m[base + i] += qa;
            zi += qa;
        }
        ax[i] = xi;
        ay[i] = yi;
        az[i] = zi;
    }
    (ax, ay, az)
}
