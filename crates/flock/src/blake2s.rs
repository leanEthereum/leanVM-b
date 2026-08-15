//! Monolithic BLAKE2s compression-function R1CS: one R1CS instance per
//! `compress(h, m, t, f0, f1) → h'` call, encoding the 16-word state init, all
//! **ten** rounds, and the finalization XORs in one sparse system.
//!
//! ## Why this fits where the naive encoding does not
//!
//! BLAKE2s's G is BLAKE2s's G (same lane schedule, same rotations 16/12/8/7),
//! so the only difference that matters here is 10 rounds against 7: 80 G
//! calls instead of 56. The block dimension is the same `k_log = 14`, and the
//! slot budget is unforgiving:
//!
//! ```text
//!   16,384 slots − 1,280 prefix                        = 15,104 for G blocks
//!   80 G × 250 (blake2s's pinned stride)                = 20,000   over by 4,896
//!   80 G × 186 (unpinned, chained three-operand adds)  = 14,880   fits, 224 spare
//!   80 G × 184 (unpinned, fused three-operand adds)    = 14,720   fits, 384 spare
//! ```
//!
//! `184 = 61 + 31 + 61 + 31` is the multiplicative-complexity floor for the
//! four ADDs of one G (31 products is the optimum for a 32-bit two-operand
//! add, 61 for a three-operand one), so this encoding is not merely tight, it
//! is the smallest possible at 10 rounds.
//!
//! ## No lin-id pins, unlike `blake2s`
//!
//! `blake2s` materializes `b_new`/`d_new` per G (64 slots) to break the affine
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
//! `blake2s` uses, so an embedding protocol can fold a chaining step with a
//! single tensor opening. Nothing else is materialized: every intermediate
//! word, every state write and the whole message schedule stay symbolic
//! affine forms substituted into their consumers.
//!
//! ## Constraint shape (`C = I`)
//!
//! Identical to `blake2s`: every z slot is the output of exactly one row, with
//! the row kinds being the constant wire, free inputs, lin-id words (only
//! `out` here) and the ADD product rows. See the `gf2` module for the adder row
//! algebra, which both circuits share.
//!
//! ## What this does NOT enforce
//!
//! **Input binding**: `h`, `m`, `t` and the finalization flags are free
//! witness bits. Pinning them to a caller's values is the embedding
//! protocol's job, via PCS openings at fixed indices.

use crate::gf2::{
    ADD3_BITS, CARRY_BITS_PER_ADD, WalkAcc, WireWord, Word, walk_add, walk_add3_fused, wire_from_const,
    wire_from_slot_base, wire_rotr, wire_xor, write_add_carry_rows, write_add3_fused_rows, write_lin_word_rows,
};
use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};
use crate::verifier;
use crate::witness::packed_bytes;
use crate::witness::{
    BitRecord, add_carry_parts, add3_fused_parts, drive_witness_packed_and_lincheck, or_bit_at,
    write_lin_word_ab_packed,
};
use fiat_shamir::transcript::{Receiver, Transmitter};
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify};
use primitives::field::F192;
use primitives::multilinear::lagrange_weights_naive;
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

/// Number of BLAKE2s rounds.
pub const N_ROUNDS: usize = primitives::blake2s::ROUNDS;
/// Number of G calls per round (4 column + 4 diagonal).
pub const N_G_PER_ROUND: usize = 8;
/// Total G calls per compression.
pub const N_G: usize = N_ROUNDS * N_G_PER_ROUND; // 80
/// Bits per BLAKE2s word.
pub const WORD_BITS: usize = crate::gf2::WORD_BITS;

/// Bits per G block: two fused three-operand ADDs and two two-operand ADDs,
/// nothing materialized.
pub const G_STRIDE: usize = 2 * ADD3_BITS + 2 * CARRY_BITS_PER_ADD; // 184

/// BLAKE2s initial values, the SHA-256 IV.
pub use primitives::blake2s::IV as BLAKE2S_IV;

/// BLAKE2s message schedule and per-G lane assignment, from the native hash so
/// the circuit provably encodes the same schedule the prover computes.
pub use primitives::blake2s::{G_LANES, SIGMA};

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
pub const fn param_iv() -> [u32; 8] {
    primitives::blake2s::PARAM_IV
}

/// The byte counter of a single 64-byte block.
pub const PINNED_T: u64 = 64;
/// The final-block flag `f0`: a one-block message is also its last block.
pub const PINNED_F0: u32 = u32::MAX;

/// A convenient one-block standard hash [`Compression`] of `m`: exactly
/// `blake2s(m)` for a 64-byte message, which is the configuration the VM's
/// `Blake2s` opcode and `fiat_shamir::sponge::compress` use. The circuit itself
/// accepts arbitrary chaining values, counters and flags.
pub fn pinned_compression(m: [u32; 16]) -> Compression {
    (param_iv(), m, PINNED_T, PINNED_F0, 0)
}

/// The padding instance: `blake2s(0^64)`. Fills unused trailing slots so every
/// batched block is a valid instance with constant wire 1, as the lincheck
/// const-wire pin requires.
pub fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
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

/// [`BlockR1cs::r1cs_digest`] of this module's circuit, baked as a constant:
/// recomputing it means building ~89M matrix entries and hashing their 96 MiB
/// bit image, which embedding protocols would otherwise pay inside their first
/// prove. The `r1cs_digest_matches_baked` test recomputes and compares: a
/// circuit change fails it until this constant is updated alongside. The same
/// digest is mirrored in `python-verifier/verifier.py`, which cannot rebuild
/// the matrices at all.
pub const R1CS_DIGEST: [u8; 32] = [
    0xec, 0x91, 0xe9, 0xd8, 0xd9, 0xca, 0x4e, 0x30, 0x62, 0x05, 0x90, 0x7a, 0x0d, 0x23, 0x6e, 0x53, 0xa6, 0xcd, 0xbd,
    0xa0, 0x38, 0x2e, 0xf6, 0xc4, 0x33, 0xef, 0x93, 0x63, 0xed, 0xfe, 0x04, 0x2e,
];

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
        c_0: crate::witness::identity(K),
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
// `build_matrices`, and are the same shapes `blake2s` documents.
// ---------------------------------------------------------------------------

// Record-relative positions, mirroring the `G_*` sub-block offsets.
const REC_MAJ_A1: usize = G_ADD3_A1;
const REC_RIP_A1: usize = G_ADD3_A1 + CARRY_BITS_PER_ADD;
const REC_C1: usize = G_ADD_C1;
const REC_MAJ_A2: usize = G_ADD3_A2;
const REC_RIP_A2: usize = G_ADD3_A2 + CARRY_BITS_PER_ADD;
const REC_C2: usize = G_ADD_C2;
/// One G's rows are composed in a `BitRecord<3>`, so its whole stride, and the
/// last sub-block offset within it, must fit 192 bits.
const _: () = assert!(G_STRIDE <= 3 * 64 && REC_C2 < 3 * 64);

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
/// `2^n_blocks_log` slots. Mirror of `blake2s`'s generator; see it for the
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

// ---------------------------------------------------------------------------
// Convenience API: Blake2sSetup
// ---------------------------------------------------------------------------

/// Bundles the monolithic BLAKE2s compression R1CS for the smallest supported
/// power-of-two shape that can hold `n_blocks` compressions.
#[derive(Clone, Debug)]
pub struct Blake2sSetup {
    pub r1cs: BlockR1cs,
}

impl Blake2sSetup {
    /// Build a setup for `n_blocks` BLAKE2s compressions.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        let r1cs = build_block_r1cs(n_log);
        // Warm the CSC fold circuit here so its one-time build (a pass over
        // ~89M nonzeros) stays out of the first prove/verify. The prove-cycle
        // buffers need no pre-faulting: they come from the arena, which keeps its
        // pages resident across proofs (see `zk_alloc`).
        r1cs.csc_lincheck_circuit();
        Self { r1cs }
    }

    pub fn m(&self) -> usize {
        self.r1cs.m
    }
    pub fn n_blocks_log(&self) -> usize {
        self.r1cs.m - self.r1cs.k_log
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

/// One claim on the committed packed BLAKE2s witness `q_flock`, as left by the
/// The two claims on the committed witness `q_flock` left by the Flock BLAKE2s
/// zerocheck + lincheck reduction, for the PCS to discharge:
/// - `ab`: the `A∘B` side, from lincheck.
/// - `c` : the `C` side, from zerocheck (`C = I`, so a direct z-claim).
///
/// This is the clean seam between Flock's reduction and the PCS: both families
/// are $2^{k_skip}$ bit-slice values at a point, transmitted and checked inside
/// the reduction (see [`Blake2sSetup::prove_reduction`]), so the PCS only has to
/// bind them to the commitment.
#[derive(Clone, Debug)]
pub struct PackedWitnessClaims {
    pub ab: SliceClaim,
    pub c: SliceClaim,
}

/// One side of a reduction: the `2^k_skip` bit-slice values of `z` at
/// `suffix_point`, already transmitted and checked (lincheck's terminal identity
/// pins the `ab` family, the φ8-Lagrange combination against `c_eval` pins the
/// `c` one).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Vec<F192>,
}

/// The variable count (`log2` length) of the committed `q_flock` column for
/// `n_blocks` executed compressions: `K_LOG + min_n_blocks_log − LOG_PACKING`.
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

/// Package the prover's reduction claims as a [`RingSwitchOpen`], so the PCS
/// discharges flock's `(ab, c)` validity in the same opening as the embedder's
/// own point claims. `offset` is `q_flock`'s slot in the committed stack; the
/// opener slices `q_flock` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &PackedWitnessClaims) -> RingSwitchOpen {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchOpen {
        offset,
        qflock_vars,
        claims: vec![
            ring_claim(&reduced.ab, qflock_vars),
            ring_claim(&reduced.c, qflock_vars),
        ],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered
/// `(ab, c)` claims as a [`RingSwitchVerify`], the same statement data. The
/// transmitted opening travels separately.
pub fn ring_switch_verify(n_blocks: usize, offset: usize, ab: &SliceClaim, c: &SliceClaim) -> RingSwitchVerify {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchVerify {
        offset,
        qflock_vars,
        claims: vec![ring_claim(ab, qflock_vars), ring_claim(c, qflock_vars)],
    }
}

/// Everything [`Blake2sSetup::verify_reduction`] recovers: the two `(ab, c)`
/// z-claims for the PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub ab: SliceClaim,
    pub c: SliceClaim,
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

/// The two claims the reduction leaves for the PCS: `ab` is lincheck's output
/// point, whose 64 slice values are `lc.s_hat_v`; `c` is a z-claim at the
/// zerocheck's own point (`C = I`). Prover and verifier must derive them
/// identically, so they share this one derivation.
fn reduction_claims(
    zc: &crate::zerocheck::ZerocheckClaim,
    lc: &crate::lincheck::LincheckClaim,
    x_outer: &[F192],
    c_slices: Vec<F192>,
) -> (SliceClaim, SliceClaim) {
    let mut ab_point = lc.r_inner_rest.clone();
    ab_point.extend_from_slice(x_outer);
    (
        SliceClaim {
            suffix_point: ab_point,
            s_hat_v: lc.s_hat_v.clone(),
        },
        SliceClaim {
            suffix_point: zc.r_rest.clone(),
            s_hat_v: c_slices,
        },
    )
}

/// The `c` family's `PACKING_WIDTH` slices, from the two banks the zerocheck's
/// fused kernel captured. That kernel works in its OWN 128-bit packing, whose
/// prefix absorbs `z` AND the first suffix coordinate `c`, while the 64-bit
/// packing keeps `c` in the suffix: 64-word `y = 2y' + b` is the b-half of the
/// 128-word `y'`, and bit `i` of that half is bit `i + 64b` of it, so
/// `s64[i] = (1+c)·s128[i] + c·s128[i+64]`.
fn fold_c_slices(captured: &[F192], r_rest: &[F192]) -> Vec<F192> {
    match captured.len() {
        PACKING_WIDTH => captured.to_vec(),
        n if n == 2 * PACKING_WIDTH && !r_rest.is_empty() => {
            let c = r_rest[0];
            (0..PACKING_WIDTH)
                .map(|i| (F192::ONE + c) * captured[i] + c * captured[i + PACKING_WIDTH])
                .collect()
        }
        n => panic!("captured c slices have width {n}"),
    }
}

/// What ties the `c` slices to the zerocheck: `c_eval` is the quirky evaluation
/// of `z` at `(z_skip, r_rest)`, which the quirky extension expands as this φ8
/// Lagrange combination of the slices.
fn c_slices_value(slices: &[F192], z_skip: F192) -> F192 {
    lagrange_weights_naive(LOG_PACKING, z_skip)
        .iter()
        .zip(slices)
        .map(|(&w, &s)| w * s)
        .fold(F192::ZERO, |a, x| a + x)
}

impl Blake2sSetup {
    /// **Flock reduction (prover).** Run the BLAKE2s zerocheck and lincheck on
    /// the shared transcript, reducing R1CS validity of `blocks` to two
    /// evaluation claims on the committed packed witness `q_flock`. (The
    /// statement is already transcript-bound: the embedding protocol seeds
    /// with the R1CS digest and announces the count.) Returns:
    /// - `z_packed`: the regenerated packed witness the PCS later opens against;
    /// - the [`PackedWitnessClaims`] `(ab, c)` on `q_flock`, with ring-switch weights.
    ///
    /// Does NOT open the PCS; the caller discharges the returned claims in the
    /// one stacked opening (`lean_vm`'s `pcs::open`).
    pub fn prove_reduction(
        &self,
        blocks: &[Compression],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> (ArenaVec<u64>, PackedWitnessClaims) {
        assert!(
            blocks.len() <= self.n_block_slots(),
            "{} compressions exceed this setup's {} slots",
            blocks.len(),
            self.n_block_slots()
        );
        let n_log = self.n_blocks_log();
        let t_witness = std::time::Instant::now();
        let (z_packed, a_packed_words, b_packed_words, z_packed_lincheck) =
            generate_witness_with_ab_packed_and_lincheck(blocks, n_log);
        if std::env::var_os("FLOCK_PROVE_TRACE").is_some() {
            eprintln!(
                "[flock prove] witness:   {:.2} ms",
                t_witness.elapsed().as_secs_f64() * 1e3,
            );
        }
        let reduced =
            self.prove_reduction_precomputed(&z_packed, &a_packed_words, &b_packed_words, &z_packed_lincheck, ps);
        (z_packed, reduced)
    }

    /// **Flock reduction from a prepared witness (prover).** This is the
    /// witness-generation-free counterpart of [`Self::prove_reduction`] for
    /// embedders that already generated the packed `z`, `A·z`, `B·z`, and
    /// lincheck-stripe buffers before committing the flattened witness.
    pub fn prove_reduction_precomputed(
        &self,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> PackedWitnessClaims {
        let trace = std::env::var_os("FLOCK_PROVE_TRACE").is_some();
        let t_reduction = std::time::Instant::now();

        // The fused generator packs 64 Boolean coordinates per word.
        let packed_len = 1usize << (self.r1cs.m - 6);
        assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
        assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
        assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");
        assert_eq!(z_packed_lincheck.len(), packed_len * 8, "wrong lincheck stripe length");

        // No bind_statement here: the embedding protocol (leanVM-b) seeds its
        // transcript with the R1CS digest and binds the instance
        // count and commitment root before any challenge, so the statement is
        // already fully transcript-bound.

        let padding = crate::zerocheck::PaddingSpec {
            k_log: self.r1cs.k_log,
            useful_bits_per_block: self.r1cs.useful_bits,
        };
        let t_zerocheck = std::time::Instant::now();
        let (zc_claim, s_hat_v_c) = crate::zerocheck::prove_packed_padded_capture_s_hat_v_c(
            packed_bytes(a_packed_words),
            packed_bytes(b_packed_words),
            packed_bytes(z_packed), // C = I, so c == z
            self.r1cs.m,
            &padding,
            ps,
        );
        let zerocheck_time = t_zerocheck.elapsed();

        // The `c` family, sent and tied here rather than by the PCS: both
        // families then leave the reduction in the same shape.
        let c_slices = fold_c_slices(&s_hat_v_c, &zc_claim.r_rest);
        for &x in c_slices.iter() {
            ps.add_scalar(x);
        }

        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = x_ab_of(&zc_claim, inner_rest_len);
        let t_lincheck = std::time::Instant::now();
        let lc_claim = crate::lincheck::prove_padded_capture_s_hat_v(
            z_packed_lincheck,
            self.r1cs.m,
            self.r1cs.k_log,
            self.r1cs.k_skip,
            self.r1cs.useful_bits,
            self.r1cs.csc_lincheck_circuit(),
            &x_ab,
            ps,
        );
        let lincheck_time = t_lincheck.elapsed();

        let (ab, c) = reduction_claims(&zc_claim, &lc_claim, &x_ab.x_outer, c_slices);
        let reduced = PackedWitnessClaims { ab, c };
        if trace {
            let reduction_time = t_reduction.elapsed();
            let glue_time = reduction_time.saturating_sub(zerocheck_time + lincheck_time);
            eprintln!(
                "[flock prove] reduction: {:.2} ms (zerocheck: {:.2} ms, lincheck: {:.2} ms, glue: {:.2} ms)",
                reduction_time.as_secs_f64() * 1e3,
                zerocheck_time.as_secs_f64() * 1e3,
                lincheck_time.as_secs_f64() * 1e3,
                glue_time.as_secs_f64() * 1e3,
            );
        }
        reduced
    }

    /// **Flock reduction (verifier).** Replay the BLAKE2s zerocheck and
    /// lincheck straight off the shared transcript stream, recovering the two
    /// `(ab, c)` evaluation claims on the committed witness `q_flock`. Mirror of
    /// [`Self::prove_reduction`]; the PCS then discharges the returned claims.
    pub fn verify_reduction(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (R1CS digest) + announced count + commitment root.

        let zc_claim = crate::zerocheck::verify(self.r1cs.m, vs).map_err(verifier::VerifyError::Zerocheck)?;

        // The `c` family: read its slices and tie them to `c_eval`.
        let c_slices = vs
            .next_scalars(PACKING_WIDTH)
            .map_err(|_| verifier::VerifyError::CSlicesTruncated)?;
        if c_slices_value(&c_slices, zc_claim.z) != zc_claim.c_eval {
            return Err(verifier::VerifyError::CSlicesMismatch);
        }

        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = x_ab_of(&zc_claim, inner_rest_len);
        // Walk-capable circuit: the verifier's lincheck consistency check is
        // one circuit walk (O(circuit) field ops) instead of the ∝ NNZ CSC
        // marginal fold. Same transcript, same accept/reject.
        let lc_claim = crate::lincheck::verify(
            self.r1cs.m,
            self.r1cs.k_log,
            self.r1cs.k_skip,
            &WalkLincheckCircuit::new(&self.r1cs),
            &x_ab,
            zc_claim.a_eval,
            zc_claim.b_eval,
            vs,
        )
        .map_err(verifier::VerifyError::Lincheck)?;

        let (ab, c) = reduction_claims(&zc_claim, &lc_claim, &x_ab.x_outer, c_slices);
        Ok(ReductionReplay {
            ab,
            c,
            zc_claim,
            lc_claim,
        })
    }
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
    fn r1cs_digest_matches_baked() {
        assert_eq!(
            build_block_r1cs(3).r1cs_digest(),
            R1CS_DIGEST,
            "R1CS changed - update R1CS_DIGEST"
        );
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
