//! Monolithic BLAKE2s compression-function R1CS: one R1CS instance per
//! `compress(h, m, t, f0, f1) → h'` call, encoding the 16-word state init, all
//! **ten** rounds, and the finalization XORs in one sparse system.
//!
//! ## Why this fits where the naive encoding does not
//!
//! BLAKE2s's G is BLAKE3's G (same lane schedule, same rotations 16/12/8/7),
//! so the only difference that matters here is 10 rounds against 7: 80 G
//! calls instead of 56. The block dimension is the same `k_log = 14`, and the
//! slot budget is unforgiving:
//!
//! ```text
//!   16,384 slots − 1,280 prefix                        = 15,104 for G blocks
//!   80 G × 250 (blake3's pinned stride)                = 20,000   over by 4,896
//!   80 G × 186 (unpinned, chained three-operand adds)  = 14,880   fits, 224 spare
//!   80 G × 184 (unpinned, fused three-operand adds)    = 14,720   fits, 384 spare
//! ```
//!
//! `184 = 61 + 31 + 61 + 31` is the multiplicative-complexity floor for the
//! four ADDs of one G (31 products is the optimum for a 32-bit two-operand
//! add, 61 for a three-operand one), so this encoding is not merely tight, it
//! is the smallest possible at 10 rounds.
//!
//! ## No lin-id pins, unlike `blake3`
//!
//! `blake3` materializes `b_new`/`d_new` per G (64 slots) to break the affine
//! cascade for half the lanes, which costs 250 slots per G but keeps the
//! substituted matrices at ~16.7M nonzeros. That is unaffordable here: at 80 G
//! it needs 19,840 slots. Nor is a cheaper partial break available. Resetting
//! the cascade means materializing all 16 lanes at some round boundary, which
//! costs 512 slots against the 384 spare, so **every** lane cascades through
//! all ten rounds and the matrices carry ~89M nonzeros.
//!
//! That is affordable because nonzeros are nearly free in this proof system.
//! The committed block is 2^14 bits either way, so nothing the PCS commits or
//! opens changes; the verifier evaluates the matrix forms by walking the
//! circuit structure ([`bilinear_walk_pair`]), not the nonzeros; and the one
//! O(nnz) per-proof cost, lincheck's `fold_alpha_batched`, is milliseconds.
//! What the density does cost is one-time setup: building and transposing the
//! matrices.
//!
//! ## Witness layout per compression block (`k_log = 14`, `k = 16,384`)
//!
//! ```text
//!   z[0      ..    256)        = h[0..8]    (input chaining value, free)
//!   z[256    ..    512)        = out[0..8]  = h[i] ^ v[i] ^ v[i+8]
//!   z[512]                     = 1                    (constant wire)
//!   z[513    ..    640)        = padding (forced to 0 by empty rows)
//!   z[640    ..  1,152)        = m[0..16]   (16 × 32-bit words, free)
//!   z[1,152  ..  1,184)        = t_lo       (free input)
//!   z[1,184  ..  1,216)        = t_hi       (free input)
//!   z[1,216  ..  1,248)        = f0         (free input)
//!   z[1,248  ..  1,280)        = f1         (free input)
//!   z[1,280  .. 16,000)        = 80 G blocks × 184 bits each
//!   z[16,000 .. 16,384)        = padding (forced to 0 by empty rows)
//! ```
//!
//! Per G block layout (184 bits), all products, no materialized words:
//! ```text
//!   [0   .. 31)    majority products, ADD3_A1 = a + b + mx        (→ a_1)
//!   [31  .. 61)    ripple products,   ADD3_A1
//!   [61  .. 92)    carry_aux for ADD_C1      = c + d_1            (→ c_1)
//!   [92  .. 123)   majority products, ADD3_A2 = a_1 + b_1 + my    (→ a_new)
//!   [123 .. 153)   ripple products,   ADD3_A2
//!   [153 .. 184)   carry_aux for ADD_C2      = c_1 + d_2          (→ c_new)
//! ```
//!
//! `h` and `out` each fill one clean 256-bit slot, the same I/O alignment
//! `blake3` uses, so an embedding protocol can fold a chaining step with a
//! single tensor opening. Nothing else is materialized: every intermediate
//! word, every state write and the whole message schedule stay symbolic
//! affine forms substituted into their consumers.
//!
//! ## Constraint shape (`C = I`)
//!
//! Identical to `blake3`: every z slot is the output of exactly one row, with
//! the row kinds being the constant wire, free inputs, lin-id words (only
//! `out` here) and the ADD product rows. See the `gf2` module for the adder row
//! algebra, which both circuits share.
//!
//! ## What this does NOT enforce
//!
//! **Input binding**: `h`, `m`, `t` and the finalization flags are free
//! witness bits. Pinning them to a caller's values is the embedding
//! protocol's job, via PCS openings at fixed indices.

use crate::blake3_witness::{
    BitRecord, add_carry_parts, add3_fused_parts, drive_witness_packed_and_lincheck, or_bit_at,
    write_lin_word_ab_packed,
};
use crate::gf2::{
    ADD3_BITS, CARRY_BITS_PER_ADD, WalkAcc, WireWord, Word, walk_add, walk_add3_fused, wire_from_const,
    wire_from_slot_base, wire_rotr, wire_xor, write_add_carry_rows, write_add3_fused_rows, write_lin_word_rows,
};
use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};
use primitives::field::F192;
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one BLAKE2s compression occupies `2^K_LOG = 16,384` z slots.
pub const K_LOG: usize = 14;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim, must match [`crate::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

/// Number of BLAKE2s rounds. The whole point of this module: three more than
/// BLAKE3, at the same block dimension.
pub const N_ROUNDS: usize = 10;
/// Number of G calls per round (4 column + 4 diagonal).
pub const N_G_PER_ROUND: usize = 8;
/// Total G calls per compression.
pub const N_G: usize = N_ROUNDS * N_G_PER_ROUND; // 80
/// Bits per BLAKE2s word.
pub const WORD_BITS: usize = crate::gf2::WORD_BITS;

/// Bits per G block: two fused three-operand ADDs and two two-operand ADDs,
/// nothing materialized.
pub const G_STRIDE: usize = 2 * ADD3_BITS + 2 * CARRY_BITS_PER_ADD; // 184

/// BLAKE2s initial values, the SHA-256 IV. Identical to BLAKE3's.
pub const BLAKE2S_IV: [u32; 8] = crate::blake3::BLAKE3_IV;

/// BLAKE2s message schedule: `SIGMA[r][i]` is the message word feeding
/// position `i` of round `r`. Cross-checked against `hashlib.blake2s` through
/// the reference implementation in this module's tests.
pub const SIGMA: [[usize; 16]; N_ROUNDS] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// Lanes touched by G index `g` within a round: `[a, b, c, d]`. BLAKE2s and
/// BLAKE3 run the same eight G's over the same lanes, so this is deliberately
/// the same table rather than a second copy that could drift.
pub use crate::blake3::G_LANES;

// ---------------------------------------------------------------------------
// Layout positions (bit indices into the per-block z slice of length K)
// ---------------------------------------------------------------------------

/// One 256-bit chaining value, `2^8`, so `h` and `out` are aligned slots.
pub const SLOT_BITS: usize = 256;
pub const H_BASE: usize = 0; // input region, slot 0: [0, 256)
pub const OUT_BASE: usize = SLOT_BITS; // output region, slot 1: [256, 512)
pub const Z_CONST_POS: usize = 2 * SLOT_BITS; // 512
pub const M_BASE: usize = (Z_CONST_POS + 1).div_ceil(128) * 128; // 640 (128-aligned)
pub const T_LO_BASE: usize = M_BASE + 16 * WORD_BITS; // 1152
pub const T_HI_BASE: usize = T_LO_BASE + WORD_BITS; // 1184
pub const F0_BASE: usize = T_HI_BASE + WORD_BITS; // 1216
pub const F1_BASE: usize = F0_BASE + WORD_BITS; // 1248
pub const GS_BASE: usize = F1_BASE + WORD_BITS; // 1280
pub const USEFUL_BITS: usize = GS_BASE + N_G * G_STRIDE; // 16,000

const _: () = assert!(USEFUL_BITS <= K, "BLAKE2s does not fit the 2^K_LOG block");

// Sub-block offsets within one G's `G_STRIDE` slots. A fused ADD owns two
// consecutive runs (majorities then ripple); a two-operand ADD owns one.
const G_ADD3_A1: usize = 0; // h + b + mx  → a_1
const G_ADD_C1: usize = G_ADD3_A1 + ADD3_BITS; // c + d_1 → c_1
const G_ADD3_A2: usize = G_ADD_C1 + CARRY_BITS_PER_ADD; // a_1 + b_1 + my → a_new
const G_ADD_C2: usize = G_ADD3_A2 + ADD3_BITS; // c_1 + d_2 → c_new

#[inline]
fn h_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    H_BASE + WORD_BITS * w + b
}
#[inline]
fn m_bit(i: usize, b: usize) -> usize {
    debug_assert!(i < 16 && b < WORD_BITS);
    M_BASE + WORD_BITS * i + b
}
#[inline]
fn out_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    OUT_BASE + WORD_BITS * w + b
}
/// Base slot of the sub-block at offset `off` (one of the `G_*` constants)
/// within G `g`'s block.
#[inline]
fn g_slot(g: usize, off: usize) -> usize {
    debug_assert!(g < N_G && off < G_STRIDE);
    GS_BASE + G_STRIDE * g + off
}

// ---------------------------------------------------------------------------
// Reference BLAKE2s compression, the witness oracle.
// ---------------------------------------------------------------------------

#[inline]
fn g_fn(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(mx);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(12);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(my);
    v[d] = (v[d] ^ v[a]).rotate_right(8);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(7);
}

/// The 16-word working state a compression starts from: the chaining value,
/// the first four IV words, and the last four IV words XOR'd with the counter
/// and the finalization flags.
fn initial_state(h: &[u32; 8], t: u64, f0: u32, f1: u32) -> [u32; 16] {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..12].copy_from_slice(&BLAKE2S_IV[..4]);
    v[12] = BLAKE2S_IV[4] ^ (t as u32);
    v[13] = BLAKE2S_IV[5] ^ ((t >> 32) as u32);
    v[14] = BLAKE2S_IV[6] ^ f0;
    v[15] = BLAKE2S_IV[7] ^ f1;
    v
}

/// BLAKE2s compression function (RFC 7693 §3.2). Returns the new chaining
/// value `h'[i] = h[i] ^ v[i] ^ v[i+8]`.
pub fn blake2s_compress(h: &[u32; 8], m: &[u32; 16], t: u64, f0: u32, f1: u32) -> [u32; 8] {
    let mut v = initial_state(h, t, f0, f1);
    for r in 0..N_ROUNDS {
        for g in 0..N_G_PER_ROUND {
            let [la, lb, lc, ld] = G_LANES[g];
            g_fn(&mut v, la, lb, lc, ld, m[SIGMA[r][2 * g]], m[SIGMA[r][2 * g + 1]]);
        }
    }
    std::array::from_fn(|i| h[i] ^ v[i] ^ v[i + 8])
}

/// One BLAKE2s compression input: `(h, m, t, f0, f1)`.
pub type Compression = ([u32; 8], [u32; 16], u64, u32, u32);

/// BLAKE2s-256's initial chaining value: the IV with the parameter block
/// (digest length 32, no key, fanout/depth 1) folded into word 0.
pub fn param_iv() -> [u32; 8] {
    let mut h = BLAKE2S_IV;
    h[0] ^= 0x0101_0000 ^ 32;
    h
}

/// The padding instance: one full non-final block of zeros from the standard
/// initial chaining value. Fills unused trailing slots so every batched block
/// is a valid instance with constant wire 1, as the lincheck const-wire pin
/// requires.
pub fn padding_block() -> Compression {
    (param_iv(), [0u32; 16], 64, 0, 0)
}

// ---------------------------------------------------------------------------
// Matrix builder
// ---------------------------------------------------------------------------

/// The initial 16 lane words as symbolic affine forms.
fn initial_lane_words() -> [Word; 16] {
    let mut v: [Word; 16] = std::array::from_fn(|_| Word::zero());
    for w in 0..8 {
        v[w] = Word::from_slot_base(h_bit(w, 0));
    }
    for i in 0..4 {
        v[8 + i] = Word::from_const(BLAKE2S_IV[i], Z_CONST_POS);
    }
    // v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1): affine, no rows.
    for (i, base) in [T_LO_BASE, T_HI_BASE, F0_BASE, F1_BASE].into_iter().enumerate() {
        v[12 + i] = Word::from_const(BLAKE2S_IV[4 + i], Z_CONST_POS)
            .xor(&Word::from_slot_base(base))
            .dedup();
    }
    v
}

/// The fixed per-block R1CS matrices `(A_0, B_0)`, built once per process and
/// cached: verifiers and aggregation provers treat them as setup constants,
/// not per-proof work.
pub fn matrices() -> &'static (SparseBinaryMatrix, SparseBinaryMatrix) {
    static MATRICES: std::sync::OnceLock<(SparseBinaryMatrix, SparseBinaryMatrix)> = std::sync::OnceLock::new();
    MATRICES.get_or_init(build_matrices)
}

/// Build the per-block base matrices `(A_0, B_0)`. `C_0 = I_k` (circuit-shape
/// R1CS: every z slot is the output of its row).
fn build_matrices() -> (SparseBinaryMatrix, SparseBinaryMatrix) {
    let mut a_rows: Vec<Vec<usize>> = vec![Vec::new(); K];
    let mut b_rows: Vec<Vec<usize>> = vec![Vec::new(); K];

    // Constant z[Z_CONST_POS]: z·z = z. Trivially satisfied for any boolean.
    a_rows[Z_CONST_POS] = vec![Z_CONST_POS];
    b_rows[Z_CONST_POS] = vec![Z_CONST_POS];

    // Free-input rows (unconstrained when the constant wire is 1).
    let mut input_emit = |base: usize, len: usize| {
        for j in 0..len {
            let s = base + j;
            a_rows[s] = vec![s];
            b_rows[s] = vec![Z_CONST_POS];
        }
    };
    input_emit(H_BASE, 8 * WORD_BITS);
    input_emit(M_BASE, 16 * WORD_BITS);
    input_emit(T_LO_BASE, 4 * WORD_BITS);

    let mut state = initial_lane_words();
    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let a = state[la].clone();
            let b = state[lb].clone();
            let c = state[lc].clone();
            let d = state[ld].clone();
            let mx = Word::from_slot_base(m_bit(SIGMA[r][2 * g_in_round], 0));
            let my = Word::from_slot_base(m_bit(SIGMA[r][2 * g_in_round + 1], 0));

            // a_1 = a + b + mx   (fused; mx is the sparse operand, so it takes
            // the majority layer's doubled `z` position)
            let a_1 = write_add3_fused_rows(&mut a_rows, &mut b_rows, &a, &b, &mx, g_slot(g, G_ADD3_A1));
            let d_1 = d.xor(&a_1).dedup().rotr(16);
            let c_1 = write_add_carry_rows(&mut a_rows, &mut b_rows, &c, &d_1, g_slot(g, G_ADD_C1));
            let b_1 = b.xor(&c_1).dedup().rotr(12);
            // a_2 = a_1 + b_1 + my   (fused)
            let a_2 = write_add3_fused_rows(&mut a_rows, &mut b_rows, &a_1, &b_1, &my, g_slot(g, G_ADD3_A2));
            let d_2 = d_1.xor(&a_2).dedup().rotr(8);
            let c_2 = write_add_carry_rows(&mut a_rows, &mut b_rows, &c_1, &d_2, g_slot(g, G_ADD_C2));
            let b_2 = b_1.xor(&c_2).dedup().rotr(7);

            // Every lane cascades: no lin-id slots anywhere (see module docs).
            state[la] = a_2;
            state[lb] = b_2;
            state[lc] = c_2;
            state[ld] = d_2;
        }
    }

    // Finalization: out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for w in 0..8 {
        let out = state[w]
            .xor(&state[w + 8])
            .xor(&Word::from_slot_base(h_bit(w, 0)))
            .dedup();
        write_lin_word_rows(&mut a_rows, &mut b_rows, &out, out_bit(w, 0), Z_CONST_POS);
    }

    // Padding rows (the 127-bit alignment gap and [USEFUL_BITS, K)) stay
    // empty: the constraint 0·0 = z[i] forces z[i] = 0.

    let to_mat = |rows| SparseBinaryMatrix {
        num_rows: K,
        num_cols: K,
        rows,
    };
    (to_mat(a_rows), to_mat(b_rows))
}

/// Build a [`BlockR1cs`] batching `2^n_blocks_log` independent BLAKE2s
/// compressions. `n_blocks_log ≥ 3` is required (lincheck needs `n_outer ≥ 8`).
pub fn build_block_r1cs(n_blocks_log: usize) -> BlockR1cs {
    assert!(n_blocks_log >= 3, "lincheck needs n_outer ≥ 8, pick n_blocks_log ≥ 3");
    let (a_0, b_0) = matrices().clone();
    BlockR1cs {
        m: K_LOG + n_blocks_log,
        k_log: K_LOG,
        k_skip: K_SKIP,
        useful_bits: USEFUL_BITS,
        a_0,
        b_0,
        c_0: crate::blake3_witness::identity(K),
        layout: crate::r1cs::WitnessLayout::RowMajor,
        const_pin: Some(Z_CONST_POS),
        csc_cache: std::sync::OnceLock::new(),
    }
}

/// Minimum `n_blocks_log` needed to prove `n_blocks` compressions, subject to
/// the lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    n_blocks.max(8).next_power_of_two().trailing_zeros() as usize
}

// ---------------------------------------------------------------------------
// Circuit-walk evaluation: `(uᵀ A_0 w, uᵀ B_0 w)` in O(circuit) field ops,
// over the exact matrices `build_matrices` emits, never materialized. See
// the `gf2` module for why this exists and what it mirrors.
// ---------------------------------------------------------------------------

pub fn bilinear_walk_pair(u: &[F192], w: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(w.len(), K);
    let mut acc = WalkAcc::zero();
    // Σ u[row] over rows with A = B = [Z_CONST]: just the constant row.
    let u_abconst = u[Z_CONST_POS];
    acc.free_input_rows(u, w, H_BASE, 8 * WORD_BITS);
    acc.free_input_rows(u, w, M_BASE, 16 * WORD_BITS);
    acc.free_input_rows(u, w, T_LO_BASE, 4 * WORD_BITS);

    let mut state: [WireWord; 16] = std::array::from_fn(|_| [F192::ZERO; WORD_BITS]);
    for wd in 0..8 {
        state[wd] = wire_from_slot_base(w, h_bit(wd, 0));
    }
    for i in 0..4 {
        state[8 + i] = wire_from_const(w, BLAKE2S_IV[i], Z_CONST_POS);
    }
    for (i, base) in [T_LO_BASE, T_HI_BASE, F0_BASE, F1_BASE].into_iter().enumerate() {
        state[12 + i] = wire_xor(
            &wire_from_const(w, BLAKE2S_IV[4 + i], Z_CONST_POS),
            &wire_from_slot_base(w, base),
        );
    }

    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let (a, b, c, d) = (state[la], state[lb], state[lc], state[ld]);
            let mx = wire_from_slot_base(w, m_bit(SIGMA[r][2 * g_in_round], 0));
            let my = wire_from_slot_base(w, m_bit(SIGMA[r][2 * g_in_round + 1], 0));

            let a_1 = walk_add3_fused(&mut acc, u, w, &a, &b, &mx, g_slot(g, G_ADD3_A1));
            let d_1 = wire_rotr(&wire_xor(&d, &a_1), 16);
            let c_1 = walk_add(&mut acc, u, w, &c, &d_1, g_slot(g, G_ADD_C1));
            let b_1 = wire_rotr(&wire_xor(&b, &c_1), 12);
            let a_2 = walk_add3_fused(&mut acc, u, w, &a_1, &b_1, &my, g_slot(g, G_ADD3_A2));
            let d_2 = wire_rotr(&wire_xor(&d_1, &a_2), 8);
            let c_2 = walk_add(&mut acc, u, w, &c_1, &d_2, g_slot(g, G_ADD_C2));
            let b_2 = wire_rotr(&wire_xor(&b_1, &c_2), 7);

            state[la] = a_2;
            state[lb] = b_2;
            state[lc] = c_2;
            state[ld] = d_2;
        }
    }

    for wd in 0..8 {
        let out = wire_xor(
            &wire_xor(&state[wd], &state[wd + 8]),
            &wire_from_slot_base(w, h_bit(wd, 0)),
        );
        acc.lin_word_rows(u, &out, out_bit(wd, 0));
    }

    acc.finish(w, Z_CONST_POS, u_abconst)
}

/// `α·(uᵀ A_0 w) + (uᵀ B_0 w)`, the α-batched form lincheck's verifier
/// consumes, by one circuit walk.
pub fn bilinear_walk(alpha: F192, u: &[F192], w: &[F192]) -> F192 {
    let (va, vb) = bilinear_walk_pair(u, w);
    alpha * va + vb
}

/// Walk-capable [`crate::lincheck::LincheckCircuit`] over the BLAKE2s R1CS:
/// `bilinear_form` answers lincheck's verifier in O(circuit) field ops, so the
/// verifier never materializes the ~89M-nonzero substituted matrices' column
/// marginal. The prover-side `fold_alpha_batched` delegates to the (lazily
/// built) CSC fold; the verifier's fast path never calls it.
pub struct WalkLincheckCircuit<'a> {
    r1cs: &'a BlockR1cs,
}

impl<'a> WalkLincheckCircuit<'a> {
    pub fn new(r1cs: &'a BlockR1cs) -> Self {
        Self { r1cs }
    }
}

impl crate::lincheck::LincheckCircuit for WalkLincheckCircuit<'_> {
    fn n_cols(&self) -> usize {
        K
    }
    fn const_pin_col(&self) -> Option<usize> {
        self.r1cs.const_pin
    }
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        self.r1cs.csc_lincheck_circuit().fold_alpha_batched(alpha, eq_inner)
    }
    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        Some(bilinear_walk(alpha, u, w))
    }
}

// ---------------------------------------------------------------------------
// Witness generation: emits the R1CS row-witnesses directly from the BLAKE2s
// computation, as bit-packed u64 words. Row-witness semantics match
// `build_matrices`, and are the same shapes `blake3` documents.
// ---------------------------------------------------------------------------

// Record-relative positions, mirroring the `G_*` sub-block offsets.
const REC_MAJ_A1: usize = G_ADD3_A1;
const REC_RIP_A1: usize = G_ADD3_A1 + CARRY_BITS_PER_ADD;
const REC_C1: usize = G_ADD_C1;
const REC_MAJ_A2: usize = G_ADD3_A2;
const REC_RIP_A2: usize = G_ADD3_A2 + CARRY_BITS_PER_ADD;
const REC_C2: usize = G_ADD_C2;

/// Build the (z, a, b) blocks for ONE compression instance, into this
/// instance's `K / 64` words of each packed table. Buffers must be zero on
/// entry.
///
/// **No c buffer.** Since `C = I`, `c == z` byte-for-byte; callers use
/// `z_packed` directly as the c-side input to zerocheck.
fn build_block_witness_ab_packed_into(
    h: &[u32; 8],
    m: &[u32; 16],
    t: u64,
    f0: u32,
    f1: u32,
    z: &mut [u64],
    a: &mut [u64],
    b: &mut [u64],
) {
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    or_bit_at(z, Z_CONST_POS);
    or_bit_at(a, Z_CONST_POS);
    or_bit_at(b, Z_CONST_POS);

    for w in 0..8 {
        write_lin_word_ab_packed(h_bit(w, 0), h[w], z, a, b);
    }
    for i in 0..16 {
        write_lin_word_ab_packed(m_bit(i, 0), m[i], z, a, b);
    }
    write_lin_word_ab_packed(T_LO_BASE, t as u32, z, a, b);
    write_lin_word_ab_packed(T_HI_BASE, (t >> 32) as u32, z, a, b);
    write_lin_word_ab_packed(F0_BASE, f0, z, a, b);
    write_lin_word_ab_packed(F1_BASE, f1, z, a, b);

    let mut v = initial_state(h, t, f0, f1);
    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let mx = m[SIGMA[r][2 * g_in_round]];
            let my = m[SIGMA[r][2 * g_in_round + 1]];
            let (a_val, b_val, c_val, d_val) = (v[la], v[lb], v[lc], v[ld]);

            // `G_STRIDE = 184` fits a 192-bit record.
            let mut rz = BitRecord::<3>::new();
            let mut ra = BitRecord::<3>::new();
            let mut rb = BitRecord::<3>::new();

            macro_rules! add_into {
                ($pos:ident, $x:expr, $y:expr) => {{
                    let (sum, left, right, carry) = add_carry_parts($x, $y);
                    rz.push::<$pos>(carry);
                    ra.push::<$pos>(left);
                    rb.push::<$pos>(right);
                    sum
                }};
            }
            macro_rules! add3_into {
                ($maj:ident, $rip:ident, $x:expr, $y:expr, $z:expr) => {{
                    let (sum, maj, rip) = add3_fused_parts($x, $y, $z);
                    rz.push::<$maj>(maj.2);
                    ra.push::<$maj>(maj.0);
                    rb.push::<$maj>(maj.1);
                    rz.push::<$rip>(rip.2);
                    ra.push::<$rip>(rip.0);
                    rb.push::<$rip>(rip.1);
                    sum
                }};
            }

            let a_1 = add3_into!(REC_MAJ_A1, REC_RIP_A1, a_val, b_val, mx);
            let d_1 = (d_val ^ a_1).rotate_right(16);
            let c_1 = add_into!(REC_C1, c_val, d_1);
            let b_1 = (b_val ^ c_1).rotate_right(12);
            let a_2 = add3_into!(REC_MAJ_A2, REC_RIP_A2, a_1, b_1, my);
            let d_2 = (d_1 ^ a_2).rotate_right(8);
            let c_2 = add_into!(REC_C2, c_1, d_2);
            let b_2 = (b_1 ^ c_2).rotate_right(7);

            let g_base = GS_BASE + G_STRIDE * g;
            rz.flush(z, g_base);
            ra.flush(a, g_base);
            rb.flush(b, g_base);

            v[la] = a_2;
            v[lb] = b_2;
            v[lc] = c_2;
            v[ld] = d_2;
        }
    }

    for w in 0..8 {
        write_lin_word_ab_packed(out_bit(w, 0), h[w] ^ v[w] ^ v[w + 8], z, a, b);
    }
}

/// Produce `(z, a, b, z_lincheck)` for `blocks.len()` compressions padded to
/// `2^n_blocks_log` slots. Mirror of `blake3`'s generator; see it for the
/// buffer shapes and the lincheck stripe indexing.
pub fn generate_witness_with_ab_packed_and_lincheck(
    blocks: &[Compression],
    n_blocks_log: usize,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
    let padding = padding_block();
    drive_witness_packed_and_lincheck(
        blocks,
        Some(&padding),
        n_blocks_log,
        K_LOG,
        |&(ref h, ref m, t, f0, f1), z, a, b| build_block_witness_ab_packed_into(h, m, t, f0, f1, z, a, b),
    )
}

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

    /// Full BLAKE2s-256 over the compression function, so the known-answer
    /// vectors below exercise `blake2s_compress` end to end (multi-block,
    /// counter, and the final-block flag).
    fn blake2s_256(data: &[u8]) -> [u8; 32] {
        let mut h = param_iv();
        let n_blocks = data.len().div_ceil(64).max(1);
        for i in 0..n_blocks {
            let chunk = &data[i * 64..data.len().min((i + 1) * 64)];
            let mut block = [0u8; 64];
            block[..chunk.len()].copy_from_slice(chunk);
            let m: [u32; 16] = std::array::from_fn(|w| u32::from_le_bytes(block[4 * w..4 * w + 4].try_into().unwrap()));
            let t = (i * 64 + chunk.len()) as u64;
            let last = i + 1 == n_blocks;
            h = blake2s_compress(&h, &m, t, if last { u32::MAX } else { 0 }, 0);
        }
        let mut out = [0u8; 32];
        for (w, word) in h.iter().enumerate() {
            out[4 * w..4 * w + 4].copy_from_slice(&word.to_le_bytes());
        }
        out
    }

    /// RFC 7693 BLAKE2s-256 vectors, cross-checked against `hashlib.blake2s`.
    /// Pins SIGMA, the lane schedule, the state init and the finalization: a
    /// single wrong entry in any of them changes these digests.
    #[test]
    fn compress_matches_blake2s_vectors() {
        assert_eq!(
            hex(&blake2s_256(b"")),
            "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
        );
        assert_eq!(
            hex(&blake2s_256(b"abc")),
            "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
        );
        // Exactly one full block, and one block plus a byte: both exercise the
        // counter and the non-final flag path.
        assert_eq!(
            hex(&blake2s_256(&[b'a'; 64])),
            "651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252"
        );
        assert_eq!(
            hex(&blake2s_256(&[b'a'; 65])),
            "045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497"
        );
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn layout_fits_the_block() {
        assert_eq!(G_STRIDE, 184);
        assert_eq!(N_G, 80);
        assert_eq!(USEFUL_BITS, 16_000);
        #[allow(clippy::assertions_on_constants)]
        {
            // The whole point: ten rounds inside one 2^14 block, with room.
            assert!(USEFUL_BITS <= K);
            assert_eq!(K - USEFUL_BITS, 384);
            // The per-G record is composed in a `BitRecord<3>` (192 bits).
            assert!(G_STRIDE <= 3 * 64 && REC_C2 < 3 * 64);
        }
    }

    /// Every slot a layout region claims is the output of one non-degenerate
    /// row, and every slot outside is padding. Guards the sub-block tiling:
    /// an overlap would leave a product unconstrained, and the overwritten row
    /// stays non-empty, so only the whole tiling catches it.
    #[test]
    fn constrained_rows_tile_the_layout() {
        let (a_0, b_0) = matrices();
        let mut expected = vec![false; K];
        let mut claim = |base: usize, len: usize| {
            for s in base..base + len {
                assert!(!expected[s], "slot {s} is claimed by two layout regions");
                expected[s] = true;
            }
        };
        claim(H_BASE, 8 * WORD_BITS);
        claim(OUT_BASE, 8 * WORD_BITS);
        claim(Z_CONST_POS, 1);
        claim(M_BASE, 16 * WORD_BITS);
        claim(T_LO_BASE, 4 * WORD_BITS);
        claim(GS_BASE, N_G * G_STRIDE);
        for s in 0..K {
            let constrained = !a_0.rows[s].is_empty() || !b_0.rows[s].is_empty();
            assert_eq!(
                constrained, expected[s],
                "slot {s} constrained={constrained}, want {}",
                expected[s]
            );
        }
    }

    #[test]
    fn witness_encodes_correct_output() {
        let mut rng = Rng::new(0xB25C0DE);
        let h: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
        let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
        let blocks = vec![(h, m, 0x1234_5678_9ABC_DEF0u64, u32::MAX, 0u32)];
        let z = generate_witness(&blocks, 3);
        let expected = blake2s_compress(&h, &m, 0x1234_5678_9ABC_DEF0, u32::MAX, 0);
        for w in 0..8 {
            let got = (0..WORD_BITS).fold(0u32, |acc, b| acc | ((z[out_bit(w, b)] as u32) << b));
            assert_eq!(got, expected[w], "out[{w}] mismatch");
        }
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        let mut rng = Rng::new(0xB25A7157);
        let r1cs = build_block_r1cs(3);
        for n_blocks in [1usize, 5, 8] {
            let blocks: Vec<Compression> = (0..n_blocks)
                .map(|i| {
                    (
                        std::array::from_fn(|_| rng.next_u32()),
                        std::array::from_fn(|_| rng.next_u32()),
                        64 * (i as u64 + 1),
                        if i % 2 == 0 { u32::MAX } else { 0 },
                        0,
                    )
                })
                .collect();
            let z = generate_witness(&blocks, 3);
            assert_eq!(z.len(), r1cs.n());
            assert!(r1cs.satisfies(&z), "witness for {n_blocks} compressions fails R1CS");
        }
    }

    #[test]
    fn mutated_witness_fails() {
        let mut rng = Rng::new(0xB2DEAD);
        let r1cs = build_block_r1cs(3);
        let blocks = vec![(param_iv(), std::array::from_fn(|_| rng.next_u32()), 64, 0, 0)];
        let mut z = generate_witness(&blocks, 3);
        assert!(r1cs.satisfies(&z));
        // One bit in each layer of a fused ADD, and one in a two-operand ADD,
        // in the last round where the affine cascade is deepest.
        for off in [G_ADD3_A2 + 5, G_ADD3_A2 + CARRY_BITS_PER_ADD + 5, G_ADD_C2 + 7] {
            z[g_slot(79, off)] ^= true;
            assert!(!r1cs.satisfies(&z), "tampered product bit at {off} should violate R1CS");
            z[g_slot(79, off)] ^= true;
        }
        assert!(r1cs.satisfies(&z), "restoring every bit should re-satisfy");
    }

    /// The circuit walk agrees with the built matrices on random weights. This
    /// is what pins the two representations of every gadget together.
    #[test]
    fn bilinear_walk_matches_matrices() {
        let (a_0, b_0) = matrices();
        let mut rng = Rng::new(0xB211A1C);
        let rand_vec = |rng: &mut Rng| -> Vec<F192> {
            (0..K)
                .map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
                .collect()
        };
        let direct = |m: &SparseBinaryMatrix, u: &[F192], w: &[F192]| {
            m.rows.iter().enumerate().fold(F192::ZERO, |acc, (i, row)| {
                acc + u[i] * row.iter().fold(F192::ZERO, |s, &j| s + w[j])
            })
        };
        for trial in 0..2 {
            let u = rand_vec(&mut rng);
            let w = rand_vec(&mut rng);
            let (va, vb) = bilinear_walk_pair(&u, &w);
            assert_eq!(va, direct(a_0, &u, &w), "A form, trial {trial}");
            assert_eq!(vb, direct(b_0, &u, &w), "B form, trial {trial}");
            let alpha = F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
            assert_eq!(bilinear_walk(alpha, &u, &w), alpha * va + vb, "batched, trial {trial}");
        }
    }

    /// The all-zero witness must not satisfy the system: the constant-wire pin
    /// is what rules it out, and it is the reason padding slots carry a real
    /// compression.
    #[test]
    fn const_pin_all_zero_rejected() {
        let r1cs = build_block_r1cs(3);
        assert_eq!(r1cs.const_pin, Some(Z_CONST_POS));
        let z_zero = vec![false; r1cs.n()];
        assert!(r1cs.satisfies(&z_zero), "homogeneous rows accept zero without the pin");
        let z = generate_witness(&[padding_block()], 3);
        assert!(z[Z_CONST_POS], "the pinned constant wire must be 1 in every block");
    }
}
