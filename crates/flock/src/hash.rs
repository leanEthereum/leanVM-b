//! Monolithic `Keccak-f[1600]` R1CS: one R1CS instance per permutation call,
//! encoding all **24** rounds of theta, rho, pi, chi and iota in one system.
//!
//! ## One absorb, not just the permutation
//!
//! The circuit is `permute(prev ^ (msg || 0...0))`: one whole sponge step,
//! taking the running 1600-bit state and a 1088-bit rate block. The XOR is free
//! over GF(2), which is the whole reason it lives here rather than in the
//! caller: a guest absorbing a rate block would otherwise spend nine XOR
//! instructions on it, and seventeen lanes have no 128-bit cell alignment to
//! spend them on anyway. As it stands ONE VM instruction absorbs 136 bytes,
//! which is what keeps hashing a long message affordable.
//!
//! `pad10*1` and the `0x06` domain byte stay out of the R1CS: for a message of
//! KNOWN length they are a constant bit pattern in the last rate block, so the
//! caller supplies them as constants. Every hash in this system has a known
//! length.
//!
//! ## Why the row count is what it is
//!
//! Keccak's only nonlinear step is chi, `a[x] ^= !a[x+1] & a[x+2]`, one AND per
//! bit of the 1600-bit state. That is not reducible: the five outputs of one
//! five-bit chi row have quadratic parts equal to five distinct degree-two
//! monomials, hence linearly independent, while four products of affine forms
//! span at most four dimensions. So the multiplicative complexity of chi is
//! exactly 5 per row, 1,600 AND rows per Keccak round, and
//!
//! ```text
//!   24 rounds x 1,600                                    = 38,400 AND rows
//!   prev state (free) + rate block (free) + out (pinned) =  4,288
//!   constant wire                                        =      1
//!                                              USEFUL_BITS = 42,881 (with pads)
//! ```
//!
//! which needs `K_LOG = 16`. Nothing in the encoding moves that: theta, rho, pi
//! and iota are all affine and cost no rows at all.
//!
//! ## No pins, and no cascade to worry about
//!
//! Unlike the ARX hashes, every chi output IS an AND wire and therefore
//! committed by construction, so between one AND layer and the next the affine
//! depth is a single theta, about eleven terms a bit. There is no support
//! cascade to break and so no pin families: the only lin-id rows in the block
//! are the output state, and they exist so the VM can read the result, not to
//! keep any matrix sparse. (No matrix is built either way; see the walks below.)
//!
//! ## Witness layout per permutation block (`k_log = 16`, `k = 65,536`)
//!
//! Everything is 64-bit lane aligned, because a Keccak lane IS a flock word.
//! That is what makes witness generation a whole-`u64` write per row family
//! with no bit shuffling anywhere.
//!
//! ```text
//!   words   0 ..  25   prev state, lanes 0..25   (free)     13 cells
//!   word         25    zero pad
//!   words  26 ..  43   rate block, lanes 0..17   (free)       9 cells
//!   word         43    zero pad
//!   words  44 ..  69   output state, lanes 0..25 (pinned)    13 cells
//!   word         69    zero pad
//!   words  70 .. 670   24 rounds x 25 lanes of chi ANDs
//!   bit      42,880    constant wire
//!   bits 42,881 .. 65,536   padding (forced to 0 by empty rows)
//! ```
//!
//! The pad words keep every region a whole number of 128-bit VM cells, so the
//! opcode reads and writes whole cells. They are empty rows, so the R1CS forces
//! them to zero and the bus in turn forces the VM's matching lane to zero.
//!
//! ## Constraint shape (`C = I`)
//!
//! Every z slot is the output of exactly one row: the constant wire, a free
//! input, a chi AND, or an output lin-id pin.
//!
//! ## What this does NOT enforce
//!
//! **Input binding**: the input state is free witness bits. Pinning it to a
//! caller's values is the embedding protocol's job, via PCS openings at fixed
//! indices.

use crate::gf2::{MatrixSide, RowValues};
use crate::verifier;
use crate::witness::{drive_witness_packed_and_lincheck, packed_bytes};
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify};
use primitives::field::F192;
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one `Keccak-f[1600]` occupies `2^K_LOG = 65,536` z slots.
pub const K_LOG: usize = 16;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim, must match [`crate::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

// A claim's `2^K_SKIP` slices are a ring-switch claim on `q_flock` only if that
// matches the packing width; otherwise `ring_claim` fails at run time.
const _: () = assert!(
    K_SKIP == LOG_PACKING,
    "the univariate skip must match the PCS packing width"
);

/// Rounds of `Keccak-f[1600]`.
pub const N_ROUNDS: usize = primitives::hash::ROUNDS;
/// Lanes in the state.
pub const STATE_LANES: usize = primitives::hash::STATE_LANES;
/// Bits per lane, which is also the flock word width.
pub const LANE_BITS: usize = 64;

/// The round constants, from the native permutation so the circuit provably
/// encodes the same ones the prover computes.
pub use primitives::hash::{PI, RC, RHO};

// ---------------------------------------------------------------------------
// Layout, in 64-bit words (a Keccak lane is exactly one flock word)
// ---------------------------------------------------------------------------

/// Words a state region occupies: 25 lanes plus one zero pad, so the region is
/// thirteen 128-bit VM cells.
pub const STATE_WORDS: usize = 26;
/// Lanes of the sponge rate, `1088 / 64`.
pub const RATE_LANES: usize = primitives::hash::RATE / 8;
/// Words the rate block occupies: 17 lanes plus one zero pad, so nine cells.
pub const RATE_WORDS: usize = RATE_LANES + 1;

pub const W_PREV: usize = 0;
pub const W_MSG: usize = W_PREV + STATE_WORDS; // 26
pub const W_OUT: usize = W_MSG + RATE_WORDS; // 44
pub const W_AND: usize = W_OUT + STATE_WORDS; // 70
pub const W_CONST: usize = W_AND + N_ROUNDS * STATE_LANES; // 670

pub const PREV_BASE: usize = W_PREV * LANE_BITS; // 0
pub const MSG_BASE: usize = W_MSG * LANE_BITS; // 1,664
pub const OUT_BASE: usize = W_OUT * LANE_BITS; // 2,816
pub const AND_BASE: usize = W_AND * LANE_BITS; // 4,480
pub const Z_CONST_POS: usize = W_CONST * LANE_BITS; // 42,880
pub const USEFUL_BITS: usize = Z_CONST_POS + 1; // 42,881

const _: () = assert!(USEFUL_BITS <= K, "Keccak-f[1600] does not fit the 2^K_LOG block");
const _: () = assert!(STATE_WORDS.is_multiple_of(2), "a state region must be whole VM cells");
const _: () = assert!(RATE_WORDS.is_multiple_of(2), "a rate block must be whole VM cells");

/// Bit base of previous-state lane `i`.
#[inline]
fn prev_lane(i: usize) -> usize {
    debug_assert!(i < STATE_LANES);
    PREV_BASE + LANE_BITS * i
}
/// Bit base of rate-block lane `i`.
#[inline]
fn msg_lane(i: usize) -> usize {
    debug_assert!(i < RATE_LANES);
    MSG_BASE + LANE_BITS * i
}
/// Bit base of output state lane `i`.
#[inline]
fn out_lane(i: usize) -> usize {
    debug_assert!(i < STATE_LANES);
    OUT_BASE + LANE_BITS * i
}
/// Bit base of round `r`'s chi AND wires for lane `i`.
#[inline]
fn and_lane(r: usize, i: usize) -> usize {
    debug_assert!(r < N_ROUNDS && i < STATE_LANES);
    AND_BASE + LANE_BITS * (r * STATE_LANES + i)
}

// ---------------------------------------------------------------------------
// One permutation input: the 1600-bit state.
// ---------------------------------------------------------------------------

/// One sponge step: the running state and the rate block absorbed into it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Compression {
    pub prev: [u64; STATE_LANES],
    pub msg: [u64; RATE_LANES],
}

/// The permutation this circuit's absorb ends in.
pub use primitives::hash::permute;

impl Compression {
    /// The permutation's input, `prev ^ (msg || 0...0)`.
    pub fn absorbed(&self) -> [u64; STATE_LANES] {
        let mut a = self.prev;
        for (a, m) in a.iter_mut().zip(&self.msg) {
            *a ^= m;
        }
        a
    }

    /// The state this step produces.
    pub fn output(&self) -> [u64; STATE_LANES] {
        let mut out = self.absorbed();
        permute(&mut out);
        out
    }
}

/// The padding instance, absorbing a zero block into the zero state. Fills
/// unused trailing slots so every batched block is a valid instance with
/// constant wire 1, as the lincheck const-wire pin requires.
pub fn padding_block() -> Compression {
    Compression {
        prev: [0u64; STATE_LANES],
        msg: [0u64; RATE_LANES],
    }
}

/// Domain separator for this circuit in the Fiat-Shamir seed (`lean_vm::cpu`),
/// baked as an opaque constant.
///
/// **Provenance.** `sha3_256(R1CS_DIGEST_LABEL)`, chosen rather
/// than derived: the matrices this used to be a hash of are never built, both
/// directions being circuit walks, so there is nothing to hash. What it has to
/// do is name this circuit and differ from every other one, and a constant does
/// that. `r1cs_digest_names_this_circuit` recomputes it from the string.
///
/// Mirrored in `python-verifier/verifier.py` and in the recursion guest, so a
/// deliberate circuit change means bumping the string and all three copies.
pub const R1CS_DIGEST_LABEL: &[u8] = b"leanvm-flock-keccak-f1600-v1";

pub const R1CS_DIGEST: [u8; 32] = [
    0x6f, 0x0d, 0x02, 0x8b, 0x4c, 0xf9, 0xec, 0x8f, 0x5f, 0x54, 0xc8, 0x05, 0x52, 0xa6, 0x68, 0x36, 0xf3, 0x97, 0x6c,
    0x0a, 0x4e, 0x83, 0xc6, 0x92, 0x58, 0xe1, 0xe2, 0x50, 0x35, 0xed, 0x63, 0x1d,
];

/// Minimum `n_blocks_log` needed to prove `n_blocks` permutations, subject to
/// the lincheck floor of `n_blocks_log >= 3` (`n_outer >= 8`).
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be >= 1");
    n_blocks.max(8).next_power_of_two().trailing_zeros() as usize
}

// ---------------------------------------------------------------------------
// Lane wires
//
// A lane is 64 F192 values, one per bit, holding that bit's affine form
// evaluated against the column weights. The 32-bit `gf2` helpers do not apply:
// Keccak has no adders and its word is twice as wide, so the whole gadget set
// here is AND, lin-id pin, XOR and rotate, plus their transposes.
// ---------------------------------------------------------------------------

/// One lane's wire values, bit `i` as the F192 combination `<lin_func_i, w>`.
type Lane = [F192; LANE_BITS];

const ZERO_LANE: Lane = [F192::ZERO; LANE_BITS];

#[inline]
fn from_slot(w: &[F192], base: usize) -> Lane {
    std::array::from_fn(|i| w[base + i])
}

/// A 64-bit constant: a set bit reads the constant wire, a clear bit is empty.
#[inline]
fn from_const(w: &[F192], val: u64, const_pos: usize) -> Lane {
    std::array::from_fn(|i| if (val >> i) & 1 == 1 { w[const_pos] } else { F192::ZERO })
}

#[inline]
fn xor(x: &Lane, y: &Lane) -> Lane {
    std::array::from_fn(|i| x[i] + y[i])
}

/// `rotate_left(n)` on the lane: bit `i` of the result is bit `i - n` of the
/// input, matching `u64::rotate_left`.
#[inline]
fn rotl(x: &Lane, n: u32) -> Lane {
    let n = n as usize % LANE_BITS;
    std::array::from_fn(|i| x[(i + LANE_BITS - n) % LANE_BITS])
}

/// Transpose of [`rotl`], so `<rotl(x, n), a> = <x, rotr(a, n)>`.
#[inline]
fn rotr(x: &Lane, n: u32) -> Lane {
    let n = n as usize % LANE_BITS;
    std::array::from_fn(|i| x[(i + n) % LANE_BITS])
}

/// Walk 64 AND rows `x[i] * y[i] = z[base + i]` and return the slot lane they
/// produce. This is chi, the circuit's only nonlinear gadget.
#[inline]
fn walk_and(sink: &mut RowValues, w: &[F192], x: &Lane, y: &Lane, base: usize) -> Lane {
    for i in 0..LANE_BITS {
        sink.product(base + i, x[i], y[i]);
    }
    from_slot(w, base)
}

/// Transpose of [`walk_and`]. `adj` is the adjoint of the slot lane the AND
/// rows produce, which is exactly the marginal entry of those slots.
#[inline]
fn back_and(m: &mut [F192], u: &[F192], adj: &Lane, base: usize, side: MatrixSide) -> (Lane, Lane) {
    let mut ax = ZERO_LANE;
    let mut ay = ZERO_LANE;
    for i in 0..LANE_BITS {
        m[base + i] += adj[i];
        (ax[i], ay[i]) = side.split(u[base + i]);
    }
    (ax, ay)
}

/// Walk 64 `lin_func * 1 = slot` rows, materializing an affine lane into its
/// own slots. The only lin-id rows here are the output state.
#[inline]
fn walk_pin(sink: &mut RowValues, val: &Lane, base: usize) {
    for i in 0..LANE_BITS {
        sink.bconst(base + i, val[i]);
    }
}

/// Transpose of [`walk_pin`]. Nothing inside the block reads the output state,
/// so the pin carries no incoming adjoint and only its own A-side row weights
/// flow back. Returns those and the gadget's share of the B-side constant.
#[inline]
fn back_pin(u: &[F192], base: usize, side: MatrixSide) -> (Lane, F192) {
    let mut aval = ZERO_LANE;
    let mut u_bconst = F192::ZERO;
    for i in 0..LANE_BITS {
        let (a, b) = side.split(u[base + i]);
        aval[i] = a;
        u_bconst += b;
    }
    (aval, u_bconst)
}

// ---------------------------------------------------------------------------
// Circuit-walk evaluation: `(u^T A_0 w, u^T B_0 w)` in O(circuit) field ops,
// over matrices that are never materialized. The row assignment these walks
// encode is specified in doc/leanvm, Annex C "Evaluating the matrices".
// ---------------------------------------------------------------------------

/// One forward pass of the circuit against column weights `w`, storing every
/// row's operand pair.
fn forward_walk(sink: &mut RowValues, w: &[F192]) {
    sink.bconst(Z_CONST_POS, w[Z_CONST_POS]);
    // Free-input rows: A = [slot], B = [Z_CONST]. Both the running state and the
    // rate block are free.
    for s in PREV_BASE..PREV_BASE + STATE_LANES * LANE_BITS {
        sink.bconst(s, w[s]);
    }
    for s in MSG_BASE..MSG_BASE + RATE_LANES * LANE_BITS {
        sink.bconst(s, w[s]);
    }

    // chi's A operand is `1 ^ b1`, so the all-ones lane is a standing operand.
    let ones: Lane = [w[Z_CONST_POS]; LANE_BITS];
    // The absorb: `prev ^ (msg || 0...0)`, affine and so free of rows.
    let mut a: [Lane; STATE_LANES] = std::array::from_fn(|i| {
        let prev = from_slot(w, prev_lane(i));
        if i < RATE_LANES {
            xor(&prev, &from_slot(w, msg_lane(i)))
        } else {
            prev
        }
    });

    for r in 0..N_ROUNDS {
        // theta: C[x] = xor of the column, D[x] = C[x-1] ^ rotl(C[x+1], 1).
        let c: [Lane; 5] =
            std::array::from_fn(|x| xor(&xor(&xor(&a[x], &a[x + 5]), &xor(&a[x + 10], &a[x + 15])), &a[x + 20]));
        let d: [Lane; 5] = std::array::from_fn(|x| xor(&c[(x + 4) % 5], &rotl(&c[(x + 1) % 5], 1)));
        for (i, a) in a.iter_mut().enumerate() {
            *a = xor(a, &d[i % 5]);
        }

        // rho and pi, gathered so the two are one pass.
        let b: [Lane; STATE_LANES] = std::array::from_fn(|i| {
            let src = PI[i];
            rotl(&a[src], RHO[src])
        });

        // chi: the AND wires, and the only rows this round emits.
        for y in 0..5 {
            for x in 0..5 {
                let i = x + 5 * y;
                let n1 = xor(&ones, &b[(x + 1) % 5 + 5 * y]);
                let p = walk_and(sink, w, &n1, &b[(x + 2) % 5 + 5 * y], and_lane(r, i));
                a[i] = xor(&b[i], &p);
            }
        }

        // iota
        a[0] = xor(&a[0], &from_const(w, RC[r], Z_CONST_POS));
    }

    // The output state, the block's only lin-id rows.
    for (i, a) in a.iter().enumerate() {
        walk_pin(sink, a, out_lane(i));
    }

    // The pad words and everything past USEFUL_BITS stay empty: the constraint
    // 0*0 = z[i] forces z[i] = 0.
}

pub fn bilinear_walk_pair(u: &[F192], w: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(w.len(), K);
    let (a, b) = row_values_walk(w);
    let mut va = F192::ZERO;
    let mut vb = F192::ZERO;
    for ((&ui, &ai), &bi) in u.iter().zip(&a).zip(&b) {
        va += ui * ai;
        vb += ui * bi;
    }
    (va, vb)
}

/// The matrix-vector products `(A_0 w, B_0 w)`, i.e. every row's inner product
/// with `w`, by one forward walk. O(circuit) additions instead of one pass over
/// the nonzeros, and neither matrix is materialized.
pub fn row_values_walk(w: &[F192]) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(w.len(), K);
    let mut sink = RowValues::new(K, w[Z_CONST_POS]);
    forward_walk(&mut sink, w);
    (sink.a, sink.b)
}

/// `(u^T A_0 w) + alpha*(u^T B_0 w)`, the alpha-batched form lincheck's
/// verifier consumes, by one circuit walk.
pub fn bilinear_walk(alpha: F192, u: &[F192], w: &[F192]) -> F192 {
    let (va, vb) = bilinear_walk_pair(u, w);
    va + alpha * vb
}

/// One matrix's column marginal, by one backward walk of the circuit.
///
/// ```text
///   M[j] = sum_k D_0(k,j)*u[k],   j < K
/// ```
///
/// Reverse topological order is the forward walk read bottom-up: the output
/// pins, then the 24 rounds backwards (iota, chi, rho/pi, theta), then the free
/// input state. Each round's transpose is mechanical because chi's outputs are
/// committed, so no adjoint has to be carried across a round boundary except
/// through the state itself.
fn marginal_walk_side(side: MatrixSide, u: &[F192]) -> Vec<F192> {
    assert_eq!(u.len(), K);
    let mut m = vec![F192::ZERO; K];
    // Sum of u[row] over rows whose B side is the lone constant wire: the free
    // inputs and the output pins, folded in once at the end.
    let mut u_bconst = F192::ZERO;
    // Adjoints reaching the constant wire: iota's set bits, and chi's `1 ^ b1`.
    let mut const_adj = F192::ZERO;

    for s in (PREV_BASE..PREV_BASE + STATE_LANES * LANE_BITS).chain(MSG_BASE..MSG_BASE + RATE_LANES * LANE_BITS) {
        let (a, b) = side.split(u[s]);
        m[s] += a;
        u_bconst += b;
    }

    // The output pins are where the backward walk starts.
    let mut adj: [Lane; STATE_LANES] = std::array::from_fn(|i| {
        let (aval, ub) = back_pin(u, out_lane(i), side);
        u_bconst += ub;
        aval
    });

    for r in (0..N_ROUNDS).rev() {
        // iota: a[0] ^= RC[r], so the set bits read the constant wire and the
        // adjoint passes through otherwise unchanged.
        for i in 0..LANE_BITS {
            if (RC[r] >> i) & 1 == 1 {
                const_adj += adj[0][i];
            }
        }

        // chi: a[i] = b[i] ^ AND(1 ^ b[i+1], b[i+2]), so lane b[i] collects the
        // direct term and the two operand adjoints of its two neighbours.
        let mut adj_b: [Lane; STATE_LANES] = [ZERO_LANE; STATE_LANES];
        for y in 0..5 {
            for x in 0..5 {
                let i = x + 5 * y;
                adj_b[i] = xor(&adj_b[i], &adj[i]);
                let (ax, ay) = back_and(&mut m, u, &adj[i], and_lane(r, i), side);
                // The A operand is `1 ^ b1`, so its adjoint also reaches the
                // constant wire, once per bit.
                for &v in ax.iter() {
                    const_adj += v;
                }
                let i1 = (x + 1) % 5 + 5 * y;
                let i2 = (x + 2) % 5 + 5 * y;
                adj_b[i1] = xor(&adj_b[i1], &ax);
                adj_b[i2] = xor(&adj_b[i2], &ay);
            }
        }

        // rho and pi: b[i] = rotl(ap[PI[i]], RHO[PI[i]]), a permutation, so each
        // post-theta lane receives exactly one rotated adjoint.
        let mut adj_ap: [Lane; STATE_LANES] = [ZERO_LANE; STATE_LANES];
        for (i, adj_b) in adj_b.iter().enumerate() {
            let src = PI[i];
            adj_ap[src] = rotr(adj_b, RHO[src]);
        }

        // theta: ap[i] = a[i] ^ D[i%5], D[x] = C[x-1] ^ rotl(C[x+1], 1),
        // C[x] = xor over the column. The direct term keeps `a`'s own adjoint;
        // the rest arrives through D and C.
        let mut adj_d: [Lane; 5] = [ZERO_LANE; 5];
        for (i, adj_ap) in adj_ap.iter().enumerate() {
            adj_d[i % 5] = xor(&adj_d[i % 5], adj_ap);
        }
        let mut adj_c: [Lane; 5] = [ZERO_LANE; 5];
        for (x, adj_d) in adj_d.iter().enumerate() {
            adj_c[(x + 4) % 5] = xor(&adj_c[(x + 4) % 5], adj_d);
            adj_c[(x + 1) % 5] = xor(&adj_c[(x + 1) % 5], &rotr(adj_d, 1));
        }
        adj = adj_ap;
        for (i, adj) in adj.iter_mut().enumerate() {
            *adj = xor(adj, &adj_c[i % 5]);
        }
    }

    // The absorb, transposed: lane `i` of the permutation's input is
    // `prev[i] ^ msg[i]`, so its adjoint reaches both free regions.
    for (i, adj) in adj.iter().enumerate() {
        for (j, &v) in adj.iter().enumerate() {
            m[prev_lane(i) + j] += v;
            if i < RATE_LANES {
                m[msg_lane(i) + j] += v;
            }
        }
    }

    // The constant row itself plus the B-side constant shared by every
    // non-product row.
    m[Z_CONST_POS] += const_adj + u[Z_CONST_POS] + u_bconst;
    m
}

/// The two column marginals `(A_0^T u, B_0^T u)`, by one backward walk per
/// matrix. Neither matrix is materialized.
pub fn marginal_walk_pair(u: &[F192]) -> (Vec<F192>, Vec<F192>) {
    (
        marginal_walk_side(MatrixSide::A, u),
        marginal_walk_side(MatrixSide::B, u),
    )
}

/// The alpha-batched column marginal `(A_0 + alpha B_0)^T u` used by lincheck.
pub fn marginal_walk(alpha: F192, u: &[F192]) -> Vec<F192> {
    let (mut a, b) = marginal_walk_pair(u);
    for (a, b) in a.iter_mut().zip(b) {
        *a += alpha * b;
    }
    a
}

/// Does `z` satisfy the block-diagonal R1CS, `(A_0 z) . (B_0 z) = z` per block?
///
/// Checked through [`row_values_walk`], which returns exactly the two row values
/// the relation compares, so no matrix is needed. `z` is the whole batch,
/// `2^n_blocks_log` blocks of `K` bits.
pub fn satisfies(z: &[bool], n_blocks_log: usize) -> bool {
    assert_eq!(z.len(), K << n_blocks_log, "z must be one K-bit block per instance");
    let bit = |b: bool| if b { F192::ONE } else { F192::ZERO };
    (0..1usize << n_blocks_log).all(|t| {
        let block: Vec<F192> = z[t * K..(t + 1) * K].iter().map(|&b| bit(b)).collect();
        let (a, b) = row_values_walk(&block);
        (0..K).all(|k| a[k] * b[k] == block[k])
    })
}

/// Walk-capable [`crate::lincheck::LincheckCircuit`] over the Keccak R1CS: it
/// walks the circuit in both directions, forwards for the verifier's
/// `bilinear_form` and backwards for the prover's marginal, so neither side
/// ever reads a matrix entry.
pub struct WalkLincheckCircuit;

impl crate::lincheck::LincheckCircuit for WalkLincheckCircuit {
    fn n_cols(&self) -> usize {
        K
    }
    fn const_pin_col(&self) -> usize {
        Z_CONST_POS
    }
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        marginal_walk(alpha, eq_inner)
    }
    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        Some(bilinear_walk(alpha, u, w))
    }
}

// ---------------------------------------------------------------------------
// Witness generation: emits the R1CS row-witnesses directly from the Keccak
// computation, as bit-packed u64 words. Row-witness semantics match the row
// assignment of doc/leanvm, Annex C, the same one the walks above encode.
//
// Every row family is a whole 64-bit lane at a word-aligned position, so this
// is a sequence of `u64` stores with no bit shuffling: the layout was chosen
// for exactly that.
// ---------------------------------------------------------------------------

/// Build the (z, a, b) blocks for ONE permutation instance, into this
/// instance's `K / 64` words of each packed table. Buffers must be zero on
/// entry.
///
/// **No c buffer.** Since `C = I`, `c == z` word for word; callers use
/// `z_packed` directly as the c-side input to zerocheck.
fn build_block_witness_ab_packed_into(input: &Compression, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    // The constant wire: z*z = z, trivially satisfied for any boolean.
    z[W_CONST] |= 1;
    a[W_CONST] |= 1;
    b[W_CONST] |= 1;

    // Free inputs: A = [slot], B = [const], so a == z and b is all ones.
    for (i, &lane) in input.prev.iter().enumerate() {
        z[W_PREV + i] = lane;
        a[W_PREV + i] = lane;
        b[W_PREV + i] = u64::MAX;
    }
    for (i, &lane) in input.msg.iter().enumerate() {
        z[W_MSG + i] = lane;
        a[W_MSG + i] = lane;
        b[W_MSG + i] = u64::MAX;
    }

    let mut s = input.absorbed();
    for r in 0..N_ROUNDS {
        // theta
        let mut c = [0u64; 5];
        for (x, c) in c.iter_mut().enumerate() {
            *c = s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20];
        }
        let mut d = [0u64; 5];
        for (x, d) in d.iter_mut().enumerate() {
            *d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for (i, s) in s.iter_mut().enumerate() {
            *s ^= d[i % 5];
        }

        // rho and pi
        let mut t = [0u64; STATE_LANES];
        for (i, t) in t.iter_mut().enumerate() {
            let src = PI[i];
            *t = s[src].rotate_left(RHO[src]);
        }

        // chi: one AND row family per lane, `(!t1) * t2 = p`.
        let base = W_AND + r * STATE_LANES;
        for y in 0..5 {
            for x in 0..5 {
                let i = x + 5 * y;
                let left = !t[(x + 1) % 5 + 5 * y];
                let right = t[(x + 2) % 5 + 5 * y];
                let p = left & right;
                z[base + i] = p;
                a[base + i] = left;
                b[base + i] = right;
                s[i] = t[i] ^ p;
            }
        }

        // iota
        s[0] ^= RC[r];
    }

    // The output pins: A = the affine lane, B = [const].
    for (i, &lane) in s.iter().enumerate() {
        z[W_OUT + i] = lane;
        a[W_OUT + i] = lane;
        b[W_OUT + i] = u64::MAX;
    }
}

/// Produce `(z, a, b, z_lincheck)` for `blocks.len()` permutations padded to
/// `2^n_blocks_log` slots.
pub fn generate_witness_with_ab_packed_and_lincheck(
    blocks: &[Compression],
    n_blocks_log: usize,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
    let padding = padding_block();
    drive_witness_packed_and_lincheck(blocks, Some(&padding), n_blocks_log, K_LOG, |input, z, a, b| {
        build_block_witness_ab_packed_into(input, z, a, b)
    })
}

// ---------------------------------------------------------------------------
// Convenience API: Sha3Setup
// ---------------------------------------------------------------------------

/// Bundles the monolithic `Keccak-f[1600]` R1CS for the smallest supported
/// power-of-two shape that can hold `n_blocks` compressions.
#[derive(Clone, Debug)]
pub struct Sha3Setup {
    /// The only thing a setup varies: `K_LOG`, `K_SKIP` and `USEFUL_BITS` are
    /// fixed by the circuit, and there is nothing to precompute, both prove and
    /// verify reading the matrices' forms off the circuit walks. The prove-cycle
    /// buffers need no pre-faulting either, coming from the arena, which keeps
    /// its pages resident across proofs (see `zk_alloc`).
    n_blocks_log: usize,
}

impl Sha3Setup {
    /// Build a setup for `n_blocks` Keccak permutations.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        Self {
            n_blocks_log: min_n_blocks_log(n_blocks),
        }
    }

    pub fn m(&self) -> usize {
        K_LOG + self.n_blocks_log
    }
    pub fn n_blocks_log(&self) -> usize {
        self.n_blocks_log
    }
    pub fn n_block_slots(&self) -> usize {
        1usize << self.n_blocks_log()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// The zerocheck, lincheck, and ring-switch scalars use the shared transcript;
// the caller carries the WHIR opening.

/// The one claim on the committed witness `q_flock` left by the Flock Keccak
/// zerocheck + lincheck reduction, for the PCS to discharge: the `2^k_skip`
/// bit-slice values of `z` at `suffix_point`, transmitted and pinned inside the
/// reduction by lincheck's terminal identity (which batches A, B, the
/// constant-wire pin and C), so the PCS only has to bind them to the
/// commitment.
///
/// This is the clean seam between Flock's reduction and the PCS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Vec<F192>,
}

/// The variable count (`log2` length) of the committed `q_flock` column for
/// `n_blocks` executed permutations: `K_LOG + min_n_blocks_log − LOG_PACKING`.
/// Always at least one instance: `n_blocks = 0` still commits one padding
/// instance, keeping the proof shape uniform.
pub fn qflock_kappa(n_blocks: usize) -> usize {
    K_LOG + min_n_blocks_log(n_blocks.max(1)) - LOG_PACKING
}

/// One reduction claim as a tower [`RingSwitchClaim`]: the `2^k_skip` slices and
/// the suffix point they live at, which is the WHOLE multilinear tail of the
/// quirky point (`q_flock` has `2^qflock_vars` words, and the packing prefix is
/// exactly the skipped coordinates, so nothing is split off into it).
fn ring_claim(claim: &SliceClaim, qflock_vars: usize) -> RingSwitchClaim {
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    assert_eq!(claim.s_hat_v.len(), PACKING_WIDTH);
    RingSwitchClaim {
        suffix_point: claim.suffix_point.clone(),
        s_hat_v: Some(claim.s_hat_v.clone()),
    }
}

/// Package the prover's reduction claim as a [`RingSwitchOpen`], so the PCS
/// discharges flock's validity in the same opening as the embedder's own point
/// claims. `offset` is `q_flock`'s slot in the committed stack; the opener
/// slices `q_flock` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &SliceClaim) -> RingSwitchOpen {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchOpen {
        offset,
        qflock_vars,
        claims: vec![ring_claim(reduced, qflock_vars)],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered claim as
/// a [`RingSwitchVerify`], the same statement data. The transmitted opening
/// travels separately.
pub fn ring_switch_verify(n_blocks: usize, offset: usize, claim: &SliceClaim) -> RingSwitchVerify {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchVerify {
        offset,
        qflock_vars,
        claims: vec![ring_claim(claim, qflock_vars)],
    }
}

/// Everything [`Sha3Setup::verify_reduction`] recovers: the z-claim for the
/// PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub claim: SliceClaim,
    pub zc_claim: crate::zerocheck::ZerocheckClaim,
    pub lc_claim: crate::lincheck::LincheckClaim,
}

/// The lincheck input point carried over from the zerocheck claim: the
/// univariate-skip coordinate, then the multilinear challenges split at
/// `inner_rest_len` into the inner-rest and outer halves.
fn x_ab_of(zc: &crate::zerocheck::ZerocheckClaim, inner_rest_len: usize) -> crate::lincheck::QuirkyPoint {
    crate::lincheck::QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

/// The claim the reduction leaves for the PCS: lincheck's output point, whose
/// 64 slice values are `lc.s_hat_v`. Prover and verifier must derive it
/// identically, so they share this one derivation.
fn reduction_claim(lc: &crate::lincheck::LincheckClaim, x_outer: &[F192]) -> SliceClaim {
    let mut suffix_point = lc.r_inner_rest.clone();
    suffix_point.extend_from_slice(x_outer);
    SliceClaim {
        suffix_point,
        s_hat_v: lc.s_hat_v.clone(),
    }
}

/// What the zerocheck stage hands the lincheck stage: the zerocheck claim and
/// the quirky point lincheck runs at. Opaque; the two stages of
/// [`Sha3Setup::prove_reduction_precomputed`] are split only so a caller can
/// time or profile them apart.
#[derive(Clone, Debug)]
pub struct ZerocheckStage {
    x_ab: crate::lincheck::QuirkyPoint,
}

/// One `FLOCK_PROVE_TRACE` line. `label` carries its own colon so the stages
/// line up.
fn trace_stage(label: &str, t: std::time::Instant) {
    if std::env::var_os("FLOCK_PROVE_TRACE").is_some() {
        eprintln!("[flock prove] {label:<11}{:8.2} ms", t.elapsed().as_secs_f64() * 1e3);
    }
}

impl Sha3Setup {
    /// **Flock reduction (prover).** Run the Keccak zerocheck and lincheck on
    /// the shared transcript, reducing R1CS validity of `blocks` to ONE
    /// evaluation claim on the committed packed witness `q_flock`. (The
    /// statement is already transcript-bound: the embedding protocol seeds
    /// with the R1CS digest and announces the count.) Returns:
    /// - `z_packed`: the regenerated packed witness the PCS later opens against;
    /// - the [`SliceClaim`] on `q_flock`, with its ring-switch weights.
    ///
    /// Does NOT open the PCS; the caller discharges the returned claim in the
    /// one stacked opening (`lean_vm`'s `pcs::open`).
    pub fn prove_reduction(
        &self,
        blocks: &[Compression],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> (ArenaVec<u64>, SliceClaim) {
        assert!(
            blocks.len() <= self.n_block_slots(),
            "{} permutations exceed this setup's {} slots",
            blocks.len(),
            self.n_block_slots()
        );
        let n_log = self.n_blocks_log();
        let t_witness = std::time::Instant::now();
        let (z_packed, a_packed_words, b_packed_words, z_packed_lincheck) =
            generate_witness_with_ab_packed_and_lincheck(blocks, n_log);
        trace_stage("witness:", t_witness);
        let reduced =
            self.prove_reduction_precomputed(&z_packed, &a_packed_words, &b_packed_words, &z_packed_lincheck, ps);
        (z_packed, reduced)
    }

    /// **Flock reduction from a prepared witness (prover).** This is the
    /// witness-generation-free counterpart of [`Self::prove_reduction`] for
    /// embedders that already generated the packed `z`, `A·z`, `B·z`, and
    /// lincheck-stripe buffers before committing the flattened witness. It is
    /// [`Self::prove_zerocheck`] then [`Self::prove_lincheck`].
    pub fn prove_reduction_precomputed(
        &self,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> SliceClaim {
        let stage = self.prove_zerocheck(z_packed, a_packed_words, b_packed_words, ps);
        self.prove_lincheck(stage, z_packed_lincheck, ps)
    }

    /// **Flock reduction, first stage (prover): the zerocheck.** Reduces
    /// `a·b ⊕ c = 0` over the cube to evaluation claims on `(â, b̂, ĉ)`, all
    /// three at one point.
    pub fn prove_zerocheck(
        &self,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> ZerocheckStage {
        let t_zerocheck = std::time::Instant::now();

        // The fused generator packs 64 Boolean coordinates per word.
        let packed_len = 1usize << (self.m() - 6);
        assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
        assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
        assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");

        // No bind_statement here: the embedding protocol (leanVM-b) seeds its
        // transcript with the R1CS digest and binds the instance
        // count and commitment root before any challenge, so the statement is
        // already fully transcript-bound.

        let padding = crate::zerocheck::PaddingSpec {
            k_log: K_LOG,
            useful_bits_per_block: USEFUL_BITS,
        };
        let zc_claim = crate::zerocheck::prove_packed_padded(
            packed_bytes(a_packed_words),
            packed_bytes(b_packed_words),
            packed_bytes(z_packed), // C = I, so c == z
            self.m(),
            &padding,
            ps,
        );

        let x_ab = x_ab_of(&zc_claim, K_LOG - K_SKIP);
        trace_stage("zerocheck:", t_zerocheck);
        ZerocheckStage { x_ab }
    }

    /// **Flock reduction, second stage (prover): the lincheck.** Reduces the
    /// zerocheck's `(â, b̂, ĉ)` claims to the `2^k_skip` bit slices of `z` at
    /// one point, against the per-block matrices.
    pub fn prove_lincheck(
        &self,
        stage: ZerocheckStage,
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> SliceClaim {
        let t_lincheck = std::time::Instant::now();
        let packed_len = 1usize << (self.m() - 6);
        assert_eq!(z_packed_lincheck.len(), packed_len * 8, "wrong lincheck stripe length");

        let ZerocheckStage { x_ab } = stage;
        let lc_claim = crate::lincheck::prove_padded_capture_s_hat_v(
            z_packed_lincheck,
            self.m(),
            K_LOG,
            K_SKIP,
            USEFUL_BITS,
            &WalkLincheckCircuit,
            &x_ab,
            ps,
        );

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        trace_stage("lincheck:", t_lincheck);
        claim
    }

    /// **Flock reduction (verifier).** Replay the Keccak zerocheck and
    /// lincheck straight off the shared transcript stream, recovering the one
    /// evaluation claim on the committed witness `q_flock`. Mirror of
    /// [`Self::prove_reduction`]; the PCS then discharges the returned claim.
    pub fn verify_reduction(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (R1CS digest) + announced count + commitment root.

        let zc_claim = crate::zerocheck::verify(self.m(), vs).map_err(verifier::VerifyError::Zerocheck)?;

        let inner_rest_len = K_LOG - K_SKIP;
        let x_ab = x_ab_of(&zc_claim, inner_rest_len);
        // Walk-capable circuit: the verifier's lincheck consistency check is
        // one circuit walk (O(circuit) field ops) instead of the ∝ NNZ CSC
        // marginal fold. Same transcript, same accept/reject.
        let lc_claim = crate::lincheck::verify(
            self.m(),
            K_LOG,
            K_SKIP,
            &WalkLincheckCircuit,
            &x_ab,
            zc_claim.a_eval,
            zc_claim.b_eval,
            zc_claim.c_eval,
            vs,
        )
        .map_err(verifier::VerifyError::Lincheck)?;

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        Ok(ReductionReplay {
            claim,
            zc_claim,
            lc_claim,
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Unpack the first `n_bits` logical bits of a packed witness.
    fn unpack_bits(z: &[u64], n_bits: usize) -> Vec<bool> {
        (0..n_bits).map(|i| (z[i / 64] >> (i % 64)) & 1 == 1).collect()
    }

    fn generate_witness(blocks: &[Compression], n_blocks_log: usize) -> Vec<bool> {
        let z = generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log).0;
        unpack_bits(&z, (1usize << n_blocks_log) * K)
    }

    /// Read a 64-bit lane back out of the unpacked witness.
    fn read_lane(z: &[bool], base: usize) -> u64 {
        (0..LANE_BITS).fold(0u64, |acc, j| acc | ((z[base + j] as u64) << j))
    }

    fn rand_vec(rng: &mut Rng) -> Vec<F192> {
        (0..K)
            .map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
            .collect()
    }

    fn rand_state(rng: &mut Rng) -> Compression {
        Compression {
            prev: std::array::from_fn(|_| rng.next_u64()),
            msg: std::array::from_fn(|_| rng.next_u64()),
        }
    }

    #[test]
    fn r1cs_digest_names_this_circuit() {
        assert_eq!(primitives::hash::hash(R1CS_DIGEST_LABEL), R1CS_DIGEST);
    }

    /// Every slot a layout region claims is the output of one non-degenerate
    /// row, and every slot outside is padding, the two zero pad words included.
    /// Guards the tiling: an overlap would leave a chi product unconstrained,
    /// and the overwritten row stays non-empty, so only the whole tiling
    /// catches it.
    #[test]
    fn constrained_rows_tile_the_layout() {
        let mut rng = Rng::new(0x7113D);
        let w = rand_vec(&mut rng);
        let (va, vb) = row_values_walk(&w);
        let mut expected = vec![false; K];
        let mut claim = |base: usize, len: usize| {
            for s in base..base + len {
                assert!(!expected[s], "slot {s} is claimed by two layout regions");
                expected[s] = true;
            }
        };
        claim(PREV_BASE, STATE_LANES * LANE_BITS);
        claim(MSG_BASE, RATE_LANES * LANE_BITS);
        claim(OUT_BASE, STATE_LANES * LANE_BITS);
        claim(AND_BASE, N_ROUNDS * STATE_LANES * LANE_BITS);
        claim(Z_CONST_POS, 1);
        for s in 0..K {
            // A row is empty exactly when it sums nothing; at a random `w` a
            // non-empty row is nonzero but for a `2^-192` accident.
            let constrained = va[s] != F192::ZERO || vb[s] != F192::ZERO;
            assert_eq!(
                constrained, expected[s],
                "slot {s} constrained={constrained}, want {}",
                expected[s]
            );
        }
        // The two alignment pads sit inside USEFUL_BITS and must be empty rows,
        // which is what forces the VM's thirteenth cell high lane to zero.
        for pad in [
            (W_PREV + STATE_LANES) * LANE_BITS,
            (W_MSG + RATE_LANES) * LANE_BITS,
            (W_OUT + STATE_LANES) * LANE_BITS,
        ] {
            assert!(!expected[pad], "pad word at bit {pad} must be unclaimed");
        }
    }

    /// The witness's output region holds `permute(prev ^ msg)`. Pins the round
    /// constants, the rho offsets, the pi permutation and chi against
    /// `primitives::hash`, which is itself pinned by the FIPS 202 vectors, and
    /// pins the absorb.
    #[test]
    fn witness_encodes_the_absorb_and_permutation() {
        let mut rng = Rng::new(0x5A3C_0DE5);
        for trial in 0..3 {
            let input = rand_state(&mut rng);
            let z = generate_witness(&[input], 3);
            let expected = input.output();
            for i in 0..STATE_LANES {
                assert_eq!(read_lane(&z, out_lane(i)), expected[i], "trial {trial}, out lane {i}");
                assert_eq!(read_lane(&z, prev_lane(i)), input.prev[i], "trial {trial}, prev {i}");
            }
            for i in 0..RATE_LANES {
                assert_eq!(read_lane(&z, msg_lane(i)), input.msg[i], "trial {trial}, msg {i}");
            }
        }
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        let mut rng = Rng::new(0x5A7157);
        for n_blocks in [1usize, 5, 8] {
            let blocks: Vec<Compression> = (0..n_blocks).map(|_| rand_state(&mut rng)).collect();
            let z = generate_witness(&blocks, 3);
            assert_eq!(z.len(), K << 3);
            assert!(satisfies(&z, 3), "witness for {n_blocks} permutations fails R1CS");
        }
    }

    #[test]
    fn mutated_witness_fails() {
        let mut rng = Rng::new(0xDEAD);
        let mut z = generate_witness(&[rand_state(&mut rng)], 3);
        assert!(satisfies(&z, 3));
        // A chi product in the first round, in the last round, and an output
        // pin: the three row kinds that carry the computation.
        for bit in [and_lane(0, 7) + 5, and_lane(N_ROUNDS - 1, 23) + 61, out_lane(4) + 9] {
            z[bit] ^= true;
            assert!(!satisfies(&z, 3), "tampered bit {bit} should violate R1CS");
            z[bit] ^= true;
        }
        assert!(satisfies(&z, 3), "restoring every bit should re-satisfy");
    }

    /// The backward walk really is the forward walk's transpose:
    /// `<D_0^T u, w> = u^T D_0 w` for both matrices, at random weights. Since
    /// neither direction materializes a matrix to be compared against, this is
    /// what pins them together, and the reduction as a whole relies on it: the
    /// prover folds with the marginal and the verifier answers with the
    /// bilinear form.
    #[test]
    fn marginal_walk_transposes_the_forward_walk() {
        let mut rng = Rng::new(0x11A1C);
        let dot = |x: &[F192], y: &[F192]| x.iter().zip(y).fold(F192::ZERO, |acc, (a, b)| acc + *a * *b);
        for trial in 0..2 {
            let u = rand_vec(&mut rng);
            let w = rand_vec(&mut rng);
            let (va, vb) = bilinear_walk_pair(&u, &w);
            let (ma, mb) = marginal_walk_pair(&u);
            assert_eq!(dot(&ma, &w), va, "A marginal, trial {trial}");
            assert_eq!(dot(&mb, &w), vb, "B marginal, trial {trial}");
            let alpha = F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
            assert_eq!(bilinear_walk(alpha, &u, &w), va + alpha * vb, "batched, trial {trial}");
            assert_eq!(dot(&marginal_walk(alpha, &u), &w), va + alpha * vb, "batched marginal");
        }
    }

    /// The all-zero witness must not satisfy the system: the constant-wire pin
    /// is what rules it out, and it is the reason padding slots carry a real
    /// permutation.
    #[test]
    fn const_pin_all_zero_rejected() {
        use crate::lincheck::LincheckCircuit;
        assert_eq!(WalkLincheckCircuit.const_pin_col(), Z_CONST_POS);
        let z_zero = vec![false; K << 3];
        assert!(satisfies(&z_zero, 3), "homogeneous rows accept zero without the pin");
        let z = generate_witness(&[padding_block()], 3);
        assert!(z[Z_CONST_POS], "the pinned constant wire must be 1 in every block");
    }

    /// The AND row count is the whole cost story, so it gets asserted rather
    /// than left to the module docs.
    #[test]
    fn layout_is_the_documented_size() {
        assert_eq!(N_ROUNDS * STATE_LANES * LANE_BITS, 38_400, "chi rows");
        assert_eq!(USEFUL_BITS, 42_881);
        assert_eq!(K_LOG, 16);
        assert_eq!(W_CONST, 670);
        assert_eq!(RATE_LANES, 17);
    }

    /// The whole reduction, prover and verifier, on one transcript: zerocheck
    /// then lincheck at `k_log = 16`. The verifier answers lincheck through the
    /// forward walk while the prover folded with the backward one, so this is
    /// also the protocol-level cross-check of the two directions.
    #[test]
    fn reduction_roundtrip() {
        let (setup, claim, proof) = prove_reduction_for(8, None);
        let mut vs = fiat_shamir::transcript::VerifierState::new(LABEL, &proof, &[]);
        let replay = setup.verify_reduction(&mut vs).expect("honest reduction must verify");
        assert_eq!(replay.claim, claim);
        assert!(vs.finish().is_ok(), "the transcript must be fully consumed");
    }

    /// One flipped committed bit must not survive, in each row kind the block
    /// has: a free input, a chi product, an output pin and the constant wire.
    #[test]
    fn reduction_rejects_tampering() {
        for bit in [
            prev_lane(3) + 11,
            msg_lane(2) + 5,
            and_lane(5, 12) + 40,
            out_lane(0) + 1,
            Z_CONST_POS,
        ] {
            let (setup, _, proof) = prove_reduction_for(8, Some(bit));
            let mut vs = fiat_shamir::transcript::VerifierState::new(LABEL, &proof, &[]);
            let rejected = setup.verify_reduction(&mut vs).is_err() || vs.finish().is_err();
            assert!(rejected, "flipping witness bit {bit} must make the reduction reject");
        }
    }

    const LABEL: &[u8] = b"flock-sha3-reduction-test";

    /// Prove `n` permutations, optionally flipping one committed bit of the
    /// first block first, in both views the prover feeds in.
    fn prove_reduction_for(n: usize, tamper: Option<usize>) -> (Sha3Setup, SliceClaim, fiat_shamir::transcript::Proof) {
        let mut rng = Rng::new(0xF10C ^ n as u64);
        let blocks: Vec<Compression> = (0..n).map(|_| rand_state(&mut rng)).collect();
        let setup = Sha3Setup::new(n);
        let n_log = setup.n_blocks_log();
        let mut ps = fiat_shamir::transcript::ProverState::new(LABEL, &[]);
        let claim = match tamper {
            None => setup.prove_reduction(&blocks, &mut ps).1,
            Some(bit) => {
                let (mut z, a, b, mut z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
                z[bit / 64] ^= 1u64 << (bit % 64);
                let (inner, outer) = (bit % K, bit >> K_LOG);
                z_lincheck[(outer / 8) * K + inner] ^= 1u8 << (outer % 8);
                setup.prove_reduction_precomputed(&z, &a, &b, &z_lincheck, &mut ps)
            }
        };
        (setup, claim, ps.into_proof())
    }
}
