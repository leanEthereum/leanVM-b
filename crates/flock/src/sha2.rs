//! Monolithic SHA-256 compression-function R1CS: one R1CS instance per
//! `C(h, m) → h'` call, encoding the 48-step message schedule, all **64**
//! rounds and the feed-forward in one sparse system.
//!
//! ## Where the rows go, and why there are pins
//!
//! SHA-256's XORs, rotations and shifts are free over GF(2); the nonlinear work
//! is `Ch`, `Maj` and the modular adds. Counting the optimum for each
//! (one AND per bit for `Ch` and `Maj`, 31 products for a two-operand 32-bit
//! add, 61 for a fused three-operand one):
//!
//! ```text
//!   64 rounds × (32 Ch + 32 Maj + 61 + 61 + 31 + 61)          = 17,408
//!   48 schedule steps × (61 + 31)                             =  4,416
//!   8 feed-forward adds × 31                                  =    248
//!                                                    products = 22,072
//! ```
//!
//! That is already over `2^14`, so a compression needs `K_LOG = 15` whatever
//! else is done: it is twice the block BLAKE2s occupied, and that factor is the
//! price of SHA-256 in this proof system. What the remaining slots buy is the
//! choice of which intermediate words to **materialize** ("pin"), and unlike
//! BLAKE2s, where nothing is pinned and every lane cascades through all ten
//! rounds, here pinning is not optional:
//!
//! - `a' = T1 + Sigma_0(a) + Maj` reads `a` through three rotations plus `Maj`,
//!   so an unpinned bit's affine support **quadruples every round**. Over 64
//!   rounds that is `4^64`, not a large constant, and the substituted matrices
//!   could not be built at all. `A_NEW` and `E_NEW` are pinned for that reason,
//!   and `W[t]` for the same reason across the schedule's own recurrence.
//! - `T1` is *not* pinned. Every one of its operands is already a pinned slot,
//!   so its support stays around 70 terms and inlining it into its two
//!   consumers saves 2,048 rows with no cascade.
//!
//! With those three pin families the matrices carry 1,093,586 nonzeros, eighty
//! times fewer than the BLAKE2s encoding this replaces (~89M, the price it paid
//! for pinning nothing), so building them, the CSC transpose and lincheck's
//! `fold_alpha_batched` all get *cheaper* even as the block doubles.
//!
//! ## Witness layout per compression block (`k_log = 15`, `k = 32,768`)
//!
//! ```text
//!   z[0      ..    256)   h        (input chaining value, free)   slots 0..4
//!   z[256    ..    512)   out      (h' = state + h, materialized) slots 4..8
//!   z[512    ..  1,024)   m[0..16] (message block, free)          slots 8..16
//!   z[1,024  ..  6,976)   48 schedule steps × 124
//!   z[6,976  .. 28,864)   64 rounds × 342
//!   z[28,864 .. 29,112)   8 feed-forward carry runs × 31
//!   z[29,112]             1                    (constant wire)
//!   z[29,113 .. 32,768)   padding (forced to 0 by empty rows)
//! ```
//!
//! Per schedule step (124 bits):
//! ```text
//!   [0   ..  61)   sigma_1(W[t-2]) + W[t-7] + sigma_0(W[t-15])  (fused)
//!   [61  ..  92)   + W[t-16]
//!   [92  .. 124)   W[t]                                         (pin)
//! ```
//!
//! Per round (342 bits):
//! ```text
//!   [0   ..  32)   ch_and  = e · (f ⊕ g)
//!   [32  ..  64)   maj_and = (a ⊕ b) · (a ⊕ c)
//!   [64  .. 125)   h + Sigma_1(e) + Ch                          (fused)
//!   [125 .. 186)   + W[r] + K[r]                                (fused, → T1)
//!   [186 .. 217)   d + T1                                       (→ e')
//!   [217 .. 278)   T1 + Sigma_0(a) + Maj                        (fused, → a')
//!   [278 .. 310)   e'                                           (pin)
//!   [310 .. 342)   a'                                           (pin)
//! ```
//!
//! `h` and `out` each fill one clean 256-bit slot and `m` two, the I/O
//! alignment an embedding protocol needs to fold a chaining step with a single
//! tensor opening, and the first 1,024 bits are therefore four clean slots
//! `(h, out, m_lo, m_hi)`. The constant wire moved to the end so as not to
//! break that.
//!
//! ## Big-endian, for free
//!
//! SHA-256 reads its block and writes its digest big-endian, so word `i`'s bit
//! `j` is byte `4i + 3 − j/8`'s bit `j%8`. That is a permutation *within* the
//! same 32 slots a little-endian word would use (`Word::byteswap`), so it
//! costs nothing here and leaves every 64-bit packed word equal to the VM's
//! `u64`. It applies to `h`, `out` and `m`; the circuit's own pins are
//! little-endian, having no bytes to be read in any order.
//!
//! ## Constraint shape (`C = I`)
//!
//! Every z slot is the output of exactly one row, the row kinds being the
//! constant wire, free inputs, AND rows, adder product rows and lin-id pins.
//! See the `gf2` module for the adder row algebra.
//!
//! ## What this does NOT enforce
//!
//! **Input binding**: `h` and `m` are free witness bits. Pinning them to a
//! caller's values is the embedding protocol's job, via PCS openings at fixed
//! indices.

use crate::gf2::{
    ADD3_BITS, CARRY_BITS_PER_ADD, WalkAcc, WireWord, Word, walk_add, walk_add3_fused, walk_and, wire_byteswap,
    wire_from_const, wire_from_slot_base, wire_rotr, wire_shr, wire_xor, write_add_carry_rows, write_add3_fused_rows,
    write_and_rows, write_lin_word_rows,
};
use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};
use crate::verifier;
use crate::witness::packed_bytes;
use crate::witness::{
    BitRecord, add_carry_parts, add3_fused_parts, drive_witness_packed_and_lincheck, or_bit_at, or_u32_at_bit,
    write_lin_word_ab_packed,
};
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify};
use primitives::field::F192;
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one SHA-256 compression occupies `2^K_LOG = 32,768` z slots.
pub const K_LOG: usize = 15;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim, must match [`crate::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

/// Rounds per compression.
pub const N_ROUNDS: usize = primitives::sha2::ROUNDS;
/// Message-schedule steps: `W[16..64]`.
pub const N_SCHED: usize = N_ROUNDS - 16;
/// Bits per SHA-256 word.
pub const WORD_BITS: usize = crate::gf2::WORD_BITS;

/// SHA-256's round constants, from the native hash so the circuit provably
/// encodes the same ones the prover computes.
pub use primitives::sha2::K as ROUND_CONSTANTS;

// ---------------------------------------------------------------------------
// Layout positions (bit indices into the per-block z slice of length K)
// ---------------------------------------------------------------------------

/// One 256-bit chaining value, `2^8`, so `h` and `out` are aligned slots.
pub const SLOT_BITS: usize = 256;
pub const H_BASE: usize = 0; // input region, slot 0: [0, 256)
pub const OUT_BASE: usize = SLOT_BITS; // output region, slot 1: [256, 512)
pub const M_BASE: usize = 2 * SLOT_BITS; // message, slots 2 and 3: [512, 1024)

/// Product and pin slots one schedule step owns: the fused three-operand add,
/// the two-operand add onto `W[t-16]`, then `W[t]` itself.
pub const SCHED_STRIDE: usize = ADD3_BITS + CARRY_BITS_PER_ADD + WORD_BITS; // 124
/// Product and pin slots one round owns; see the module docs for the tiling.
pub const ROUND_STRIDE: usize = 2 * WORD_BITS + 2 * ADD3_BITS + CARRY_BITS_PER_ADD + ADD3_BITS + 2 * WORD_BITS; // 342

pub const SCHED_BASE: usize = M_BASE + 16 * WORD_BITS; // 1,024
pub const ROUND_BASE: usize = SCHED_BASE + N_SCHED * SCHED_STRIDE; // 6,976
pub const OUT_CARRY_BASE: usize = ROUND_BASE + N_ROUNDS * ROUND_STRIDE; // 28,864
pub const Z_CONST_POS: usize = OUT_CARRY_BASE + 8 * CARRY_BITS_PER_ADD; // 29,112
pub const USEFUL_BITS: usize = Z_CONST_POS + 1; // 29,113

const _: () = assert!(USEFUL_BITS <= K, "SHA-256 does not fit the 2^K_LOG block");

// Sub-block offsets within one schedule step's `SCHED_STRIDE` slots.
const S_ADD3: usize = 0;
const S_ADD: usize = S_ADD3 + ADD3_BITS; // 61
const S_PIN: usize = S_ADD + CARRY_BITS_PER_ADD; // 92

// Sub-block offsets within one round's `ROUND_STRIDE` slots.
const R_CH: usize = 0;
const R_MAJ: usize = R_CH + WORD_BITS; // 32
const R_T1A: usize = R_MAJ + WORD_BITS; // 64
const R_T1B: usize = R_T1A + ADD3_BITS; // 125
const R_ENEW: usize = R_T1B + ADD3_BITS; // 186
const R_ANEW: usize = R_ENEW + CARRY_BITS_PER_ADD; // 217
const R_EPIN: usize = R_ANEW + ADD3_BITS; // 278
const R_APIN: usize = R_EPIN + WORD_BITS; // 310

const _: () = assert!(R_APIN + WORD_BITS == ROUND_STRIDE);
const _: () = assert!(S_PIN + WORD_BITS == SCHED_STRIDE);

/// Base slot of `h`'s word `w`. Bit `j` of the word is at
/// `h_word(w) + 8·(3 − j/8) + j%8`; see [`Word::byteswap`].
#[inline]
fn h_word(w: usize) -> usize {
    debug_assert!(w < 8);
    H_BASE + WORD_BITS * w
}
/// Base slot of `out`'s word `w`, big-endian as [`h_word`].
#[inline]
fn out_word(w: usize) -> usize {
    debug_assert!(w < 8);
    OUT_BASE + WORD_BITS * w
}
/// Base slot of message word `i`, big-endian as [`h_word`].
#[inline]
fn m_word(i: usize) -> usize {
    debug_assert!(i < 16);
    M_BASE + WORD_BITS * i
}
/// Base slot of the sub-block at offset `off` within schedule step `s`'s block,
/// where `s = t − 16`.
#[inline]
fn s_slot(s: usize, off: usize) -> usize {
    debug_assert!(s < N_SCHED && off < SCHED_STRIDE);
    SCHED_BASE + SCHED_STRIDE * s + off
}
/// Base slot of the sub-block at offset `off` within round `r`'s block.
#[inline]
fn r_slot(r: usize, off: usize) -> usize {
    debug_assert!(r < N_ROUNDS && off < ROUND_STRIDE);
    ROUND_BASE + ROUND_STRIDE * r + off
}
/// Carry run of the feed-forward add producing `out[w]`.
#[inline]
fn out_carry(w: usize) -> usize {
    debug_assert!(w < 8);
    OUT_CARRY_BASE + CARRY_BITS_PER_ADD * w
}

// ---------------------------------------------------------------------------
// One SHA-256 compression input: `(h, m)`.
// ---------------------------------------------------------------------------

/// One SHA-256 compression input: the chaining value and the message block's
/// 16 big-endian words.
pub type Compression = ([u32; 8], [u32; 16]);

/// `C`, the compression this circuit encodes.
pub use primitives::sha2::compress;

/// The chaining value a 64-byte `sha2_eth` starts from, which is what the VM's
/// `Sha2` opcode and `fiat_shamir::sponge::compress` use.
pub const fn iv_64() -> [u32; 8] {
    primitives::sha2::IV_64
}

/// A convenient one-block standard hash [`Compression`] of `m`: exactly
/// `sha2_eth(m)` for a 64-byte message. The circuit itself accepts arbitrary
/// chaining values, so any block of any longer hash is equally an instance.
pub fn pinned_compression(m: [u32; 16]) -> Compression {
    (iv_64(), m)
}

/// The padding instance: `sha2_eth(0^64)`. Fills unused trailing slots so every
/// batched block is a valid instance with constant wire 1, as the lincheck
/// const-wire pin requires.
pub fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
}

// ---------------------------------------------------------------------------
// Matrix builder
// ---------------------------------------------------------------------------

fn small_sigma_0(x: &Word) -> Word {
    x.rotr(7).xor(&x.rotr(18)).xor(&x.shr(3)).dedup()
}
fn small_sigma_1(x: &Word) -> Word {
    x.rotr(17).xor(&x.rotr(19)).xor(&x.shr(10)).dedup()
}
fn big_sigma_0(x: &Word) -> Word {
    x.rotr(2).xor(&x.rotr(13)).xor(&x.rotr(22)).dedup()
}
fn big_sigma_1(x: &Word) -> Word {
    x.rotr(6).xor(&x.rotr(11)).xor(&x.rotr(25)).dedup()
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
    for base in [H_BASE, M_BASE] {
        let len = if base == H_BASE { 8 } else { 16 } * WORD_BITS;
        for s in base..base + len {
            a_rows[s] = vec![s];
            b_rows[s] = vec![Z_CONST_POS];
        }
    }

    let h_in: [Word; 8] = std::array::from_fn(|w| Word::from_slot_base(h_word(w)).byteswap());

    // Message schedule. `w[t]` for `t < 16` is a message word, read big-endian;
    // the rest are this circuit's own pins.
    let mut w: Vec<Word> = (0..16).map(|i| Word::from_slot_base(m_word(i)).byteswap()).collect();
    for s in 0..N_SCHED {
        let t = 16 + s;
        // `W[t-7]` is a single slot, so it takes the fused adder's sparse
        // operand position; the two sigmas are three terms a bit.
        let partial = write_add3_fused_rows(
            &mut a_rows,
            &mut b_rows,
            &small_sigma_1(&w[t - 2]),
            &small_sigma_0(&w[t - 15]),
            &w[t - 7],
            s_slot(s, S_ADD3),
        );
        let sum = write_add_carry_rows(&mut a_rows, &mut b_rows, &partial, &w[t - 16], s_slot(s, S_ADD));
        write_lin_word_rows(&mut a_rows, &mut b_rows, &sum, s_slot(s, S_PIN), Z_CONST_POS);
        w.push(Word::from_slot_base(s_slot(s, S_PIN)));
    }

    let mut state = h_in.clone();
    for r in 0..N_ROUNDS {
        let [a, b, c, d, e, f, g, h] = state;
        let ch_and = write_and_rows(&mut a_rows, &mut b_rows, &e, &f.xor(&g).dedup(), r_slot(r, R_CH));
        let ch = ch_and.xor(&g).dedup();
        let maj_and = write_and_rows(
            &mut a_rows,
            &mut b_rows,
            &a.xor(&b).dedup(),
            &a.xor(&c).dedup(),
            r_slot(r, R_MAJ),
        );
        let maj = maj_and.xor(&a).dedup();

        // T1 = h + Sigma_1(e) + Ch + W[r] + K[r], as two fused adds. The sparse
        // operand goes third: `h` is one slot, `K[r]` is the constant wire.
        let t1a = write_add3_fused_rows(&mut a_rows, &mut b_rows, &big_sigma_1(&e), &ch, &h, r_slot(r, R_T1A));
        let k_word = Word::from_const(ROUND_CONSTANTS[r], Z_CONST_POS);
        let t1 = write_add3_fused_rows(&mut a_rows, &mut b_rows, &t1a, &w[r], &k_word, r_slot(r, R_T1B));

        let e_new = write_add_carry_rows(&mut a_rows, &mut b_rows, &d, &t1, r_slot(r, R_ENEW));
        write_lin_word_rows(&mut a_rows, &mut b_rows, &e_new, r_slot(r, R_EPIN), Z_CONST_POS);
        // a' = T1 + T2 with T2 = Sigma_0(a) + Maj, fused into one three-operand
        // add rather than a separate T2.
        let a_new = write_add3_fused_rows(&mut a_rows, &mut b_rows, &t1, &big_sigma_0(&a), &maj, r_slot(r, R_ANEW));
        write_lin_word_rows(&mut a_rows, &mut b_rows, &a_new, r_slot(r, R_APIN), Z_CONST_POS);

        // Register shift. Both new words are read from their pins, which is
        // what stops the support cascade (see the module docs).
        state = [
            Word::from_slot_base(r_slot(r, R_APIN)),
            a,
            b,
            c,
            Word::from_slot_base(r_slot(r, R_EPIN)),
            e,
            f,
            g,
        ];
    }

    // Feed-forward: out[w] = state[w] + h[w], the compression's only output.
    for (wd, (final_word, h_word_in)) in state.iter().zip(&h_in).enumerate() {
        let sum = write_add_carry_rows(&mut a_rows, &mut b_rows, final_word, h_word_in, out_carry(wd));
        write_lin_word_rows(&mut a_rows, &mut b_rows, &sum.byteswap(), out_word(wd), Z_CONST_POS);
    }

    // Padding rows ([USEFUL_BITS, K)) stay empty: the constraint 0·0 = z[i]
    // forces z[i] = 0.

    let to_mat = |rows| SparseBinaryMatrix {
        num_rows: K,
        num_cols: K,
        rows,
    };
    (to_mat(a_rows), to_mat(b_rows))
}

/// [`BlockR1cs::r1cs_digest`] of this module's circuit, baked as a constant:
/// recomputing it means building the matrices and hashing their 256 MiB bit
/// image, which embedding protocols would otherwise pay inside their first
/// prove. The `r1cs_digest_matches_baked` test recomputes and compares: a
/// circuit change fails it until this constant is updated alongside. The same
/// digest is mirrored in `python-verifier/verifier.py`, which cannot rebuild
/// the matrices at all.
pub const R1CS_DIGEST: [u8; 32] = [
    0xea, 0x60, 0xba, 0x3d, 0x4b, 0x1b, 0x62, 0x71, 0x81, 0xba, 0x90, 0xa2, 0xa4, 0x3b, 0xdd, 0x8b, 0xd0, 0x58, 0x9a,
    0x9c, 0xb9, 0x87, 0xcd, 0x37, 0xd8, 0x13, 0x77, 0x0a, 0x3f, 0x5c, 0xc8, 0x9a,
];

/// Build a [`BlockR1cs`] batching `2^n_blocks_log` independent SHA-256
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

pub fn bilinear_walk_pair(u: &[F192], col: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(col.len(), K);
    let mut acc = WalkAcc::zero();
    // Σ u[row] over rows with A = B = [Z_CONST]: just the constant row.
    let u_abconst = u[Z_CONST_POS];
    acc.free_input_rows(u, col, H_BASE, 8 * WORD_BITS);
    acc.free_input_rows(u, col, M_BASE, 16 * WORD_BITS);

    let h_in: [WireWord; 8] = std::array::from_fn(|wd| wire_byteswap(&wire_from_slot_base(col, h_word(wd))));

    let mut w: Vec<WireWord> = (0..16)
        .map(|i| wire_byteswap(&wire_from_slot_base(col, m_word(i))))
        .collect();
    for s in 0..N_SCHED {
        let t = 16 + s;
        let s1 = wire_sigma(&w[t - 2], 17, 19, 10);
        let s0 = wire_sigma(&w[t - 15], 7, 18, 3);
        let partial = walk_add3_fused(&mut acc, u, col, &s1, &s0, &w[t - 7], s_slot(s, S_ADD3));
        let sum = walk_add(&mut acc, u, col, &partial, &w[t - 16], s_slot(s, S_ADD));
        acc.lin_word_rows(u, &sum, s_slot(s, S_PIN));
        w.push(wire_from_slot_base(col, s_slot(s, S_PIN)));
    }

    let mut state = h_in;
    for r in 0..N_ROUNDS {
        let [a, b, c, d, e, f, g, h] = state;
        let ch_and = walk_and(&mut acc, u, col, &e, &wire_xor(&f, &g), r_slot(r, R_CH));
        let ch = wire_xor(&ch_and, &g);
        let maj_and = walk_and(&mut acc, u, col, &wire_xor(&a, &b), &wire_xor(&a, &c), r_slot(r, R_MAJ));
        let maj = wire_xor(&maj_and, &a);

        let t1a = walk_add3_fused(&mut acc, u, col, &wire_rot3(&e, 6, 11, 25), &ch, &h, r_slot(r, R_T1A));
        let k_word = wire_from_const(col, ROUND_CONSTANTS[r], Z_CONST_POS);
        let t1 = walk_add3_fused(&mut acc, u, col, &t1a, &w[r], &k_word, r_slot(r, R_T1B));

        let e_new = walk_add(&mut acc, u, col, &d, &t1, r_slot(r, R_ENEW));
        acc.lin_word_rows(u, &e_new, r_slot(r, R_EPIN));
        let a_new = walk_add3_fused(
            &mut acc,
            u,
            col,
            &t1,
            &wire_rot3(&a, 2, 13, 22),
            &maj,
            r_slot(r, R_ANEW),
        );
        acc.lin_word_rows(u, &a_new, r_slot(r, R_APIN));

        state = [
            wire_from_slot_base(col, r_slot(r, R_APIN)),
            a,
            b,
            c,
            wire_from_slot_base(col, r_slot(r, R_EPIN)),
            e,
            f,
            g,
        ];
    }

    for (wd, (final_word, h_word_in)) in state.iter().zip(&h_in).enumerate() {
        let sum = walk_add(&mut acc, u, col, final_word, h_word_in, out_carry(wd));
        acc.lin_word_rows(u, &wire_byteswap(&sum), out_word(wd));
    }

    acc.finish(col, Z_CONST_POS, u_abconst)
}

/// `Sigma_i`: the XOR of three rotations.
#[inline]
fn wire_rot3(x: &WireWord, r1: usize, r2: usize, r3: usize) -> WireWord {
    wire_xor(&wire_xor(&wire_rotr(x, r1), &wire_rotr(x, r2)), &wire_rotr(x, r3))
}

/// `sigma_i`: two rotations and a shift.
#[inline]
fn wire_sigma(x: &WireWord, r1: usize, r2: usize, sh: usize) -> WireWord {
    wire_xor(&wire_xor(&wire_rotr(x, r1), &wire_rotr(x, r2)), &wire_shr(x, sh))
}

/// `(uᵀ A_0 w) + α·(uᵀ B_0 w)`, the α-batched form lincheck's verifier
/// consumes, by one circuit walk.
pub fn bilinear_walk(alpha: F192, u: &[F192], w: &[F192]) -> F192 {
    let (va, vb) = bilinear_walk_pair(u, w);
    va + alpha * vb
}

/// Walk-capable [`crate::lincheck::LincheckCircuit`] over the SHA-256 R1CS:
/// `bilinear_form` answers lincheck's verifier in O(circuit) field ops, so the
/// verifier never materializes the substituted matrices' column marginal. The
/// prover-side `fold_alpha_batched` delegates to the (lazily built) CSC fold;
/// the verifier's fast path never calls it.
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
// Witness generation: emits the R1CS row-witnesses directly from the SHA-256
// computation, as bit-packed u64 words. Row-witness semantics match
// `build_matrices`.
// ---------------------------------------------------------------------------

/// One round's rows are composed in a `BitRecord<6>` and one schedule step's in
/// a `BitRecord<2>`, so each stride, and the last sub-block offset within it,
/// must fit.
const _: () = assert!(ROUND_STRIDE <= 6 * 64 && R_APIN + WORD_BITS <= 6 * 64);
const _: () = assert!(SCHED_STRIDE <= 2 * 64 && S_PIN + WORD_BITS <= 2 * 64);

/// A lin-id pin inside a record: `(z, a) = val`, `b` all ones.
macro_rules! pin_into {
    ($pos:ident, $rz:ident, $ra:ident, $rb:ident, $val:expr) => {{
        let v = $val;
        $rz.push::<$pos>(v);
        $ra.push::<$pos>(v);
        $rb.push::<$pos>(u32::MAX);
    }};
}

/// Build the (z, a, b) blocks for ONE compression instance, into this
/// instance's `K / 64` words of each packed table. Buffers must be zero on
/// entry.
///
/// **No c buffer.** Since `C = I`, `c == z` byte-for-byte; callers use
/// `z_packed` directly as the c-side input to zerocheck.
fn build_block_witness_ab_packed_into(h: &[u32; 8], m: &[u32; 16], z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    or_bit_at(z, Z_CONST_POS);
    or_bit_at(a, Z_CONST_POS);
    or_bit_at(b, Z_CONST_POS);

    // The big-endian I/O words: the byte reversal that `Word::byteswap` is on
    // the matrix side.
    for (wd, &hw) in h.iter().enumerate() {
        write_lin_word_ab_packed(h_word(wd), hw.swap_bytes(), z, a, b);
    }
    for (i, &mi) in m.iter().enumerate() {
        write_lin_word_ab_packed(m_word(i), mi.swap_bytes(), z, a, b);
    }

    let mut w = [0u32; N_ROUNDS];
    w[..16].copy_from_slice(m);
    for s in 0..N_SCHED {
        let t = 16 + s;
        let x = w[t - 15];
        let s0 = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
        let y = w[t - 2];
        let s1 = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);

        let mut rz = BitRecord::<2>::new();
        let mut ra = BitRecord::<2>::new();
        let mut rb = BitRecord::<2>::new();
        let (partial, maj, rip) = add3_fused_parts(s1, s0, w[t - 7]);
        rz.push::<S_ADD3>(maj.2);
        ra.push::<S_ADD3>(maj.0);
        rb.push::<S_ADD3>(maj.1);
        const S_ADD3_RIP: usize = S_ADD3 + CARRY_BITS_PER_ADD;
        rz.push::<S_ADD3_RIP>(rip.2);
        ra.push::<S_ADD3_RIP>(rip.0);
        rb.push::<S_ADD3_RIP>(rip.1);
        let (sum, left, right, carry) = add_carry_parts(partial, w[t - 16]);
        rz.push::<S_ADD>(carry);
        ra.push::<S_ADD>(left);
        rb.push::<S_ADD>(right);
        pin_into!(S_PIN, rz, ra, rb, sum);

        let base = SCHED_BASE + SCHED_STRIDE * s;
        rz.flush(z, base);
        ra.flush(a, base);
        rb.flush(b, base);
        w[t] = sum;
    }

    let mut state = *h;
    for r in 0..N_ROUNDS {
        let [a_v, b_v, c_v, d_v, e_v, f_v, g_v, h_v] = state;

        let mut rz = BitRecord::<6>::new();
        let mut ra = BitRecord::<6>::new();
        let mut rb = BitRecord::<6>::new();

        let ch_and = e_v & (f_v ^ g_v);
        rz.push::<R_CH>(ch_and);
        ra.push::<R_CH>(e_v);
        rb.push::<R_CH>(f_v ^ g_v);
        let maj_and = (a_v ^ b_v) & (a_v ^ c_v);
        rz.push::<R_MAJ>(maj_and);
        ra.push::<R_MAJ>(a_v ^ b_v);
        rb.push::<R_MAJ>(a_v ^ c_v);

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
            ($pos:ident, $x:expr, $y:expr, $z:expr) => {{
                const RIP: usize = $pos + CARRY_BITS_PER_ADD;
                let (sum, maj, rip) = add3_fused_parts($x, $y, $z);
                rz.push::<$pos>(maj.2);
                ra.push::<$pos>(maj.0);
                rb.push::<$pos>(maj.1);
                rz.push::<RIP>(rip.2);
                ra.push::<RIP>(rip.0);
                rb.push::<RIP>(rip.1);
                sum
            }};
        }

        let ch = ch_and ^ g_v;
        let maj = maj_and ^ a_v;
        let s1e = e_v.rotate_right(6) ^ e_v.rotate_right(11) ^ e_v.rotate_right(25);
        let s0a = a_v.rotate_right(2) ^ a_v.rotate_right(13) ^ a_v.rotate_right(22);

        let t1a = add3_into!(R_T1A, s1e, ch, h_v);
        let t1 = add3_into!(R_T1B, t1a, w[r], ROUND_CONSTANTS[r]);
        let e_new = add_into!(R_ENEW, d_v, t1);
        let a_new = add3_into!(R_ANEW, t1, s0a, maj);
        pin_into!(R_EPIN, rz, ra, rb, e_new);
        pin_into!(R_APIN, rz, ra, rb, a_new);

        let base = ROUND_BASE + ROUND_STRIDE * r;
        rz.flush(z, base);
        ra.flush(a, base);
        rb.flush(b, base);

        state = [a_new, a_v, b_v, c_v, e_new, e_v, f_v, g_v];
    }

    for (wd, (&final_word, &h_word_in)) in state.iter().zip(h.iter()).enumerate() {
        let (sum, left, right, carry) = add_carry_parts(final_word, h_word_in);
        or_u32_at_bit(z, out_carry(wd), carry);
        or_u32_at_bit(a, out_carry(wd), left);
        or_u32_at_bit(b, out_carry(wd), right);
        write_lin_word_ab_packed(out_word(wd), sum.swap_bytes(), z, a, b);
    }
}

/// Produce `(z, a, b, z_lincheck)` for `blocks.len()` compressions padded to
/// `2^n_blocks_log` slots.
pub fn generate_witness_with_ab_packed_and_lincheck(
    blocks: &[Compression],
    n_blocks_log: usize,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
    let padding = padding_block();
    drive_witness_packed_and_lincheck(blocks, Some(&padding), n_blocks_log, K_LOG, |(h, m), z, a, b| {
        build_block_witness_ab_packed_into(h, m, z, a, b)
    })
}

// ---------------------------------------------------------------------------
// Convenience API: Sha2Setup
// ---------------------------------------------------------------------------

/// Bundles the monolithic SHA-256 compression R1CS for the smallest supported
/// power-of-two shape that can hold `n_blocks` compressions.
#[derive(Clone, Debug)]
pub struct Sha2Setup {
    pub r1cs: BlockR1cs,
}

impl Sha2Setup {
    /// Build a setup for `n_blocks` SHA-256 compressions.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        let r1cs = build_block_r1cs(n_log);
        // Warm the CSC fold circuit here so its one-time build stays out of the
        // first prove/verify. The prove-cycle buffers need no pre-faulting: they
        // come from the arena, which keeps its pages resident across proofs.
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

/// The one claim on the committed witness `q_flock` left by the Flock SHA-256
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

/// Everything [`Sha2Setup::verify_reduction`] recovers: the z-claim for the
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
/// [`Sha2Setup::prove_reduction_precomputed`] are split only so a caller can
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

impl Sha2Setup {
    /// **Flock reduction (prover).** Run the SHA-256 zerocheck and lincheck on
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
            "{} compressions exceed this setup's {} slots",
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
        let packed_len = 1usize << (self.r1cs.m - 6);
        assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
        assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
        assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");

        // No bind_statement here: the embedding protocol (leanVM-b) seeds its
        // transcript with the R1CS digest and binds the instance
        // count and commitment root before any challenge, so the statement is
        // already fully transcript-bound.

        let padding = crate::zerocheck::PaddingSpec {
            k_log: self.r1cs.k_log,
            useful_bits_per_block: self.r1cs.useful_bits,
        };
        let zc_claim = crate::zerocheck::prove_packed_padded(
            packed_bytes(a_packed_words),
            packed_bytes(b_packed_words),
            packed_bytes(z_packed), // C = I, so c == z
            self.r1cs.m,
            &padding,
            ps,
        );

        let x_ab = x_ab_of(&zc_claim, self.r1cs.k_log - self.r1cs.k_skip);
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
        let packed_len = 1usize << (self.r1cs.m - 6);
        assert_eq!(z_packed_lincheck.len(), packed_len * 8, "wrong lincheck stripe length");

        let ZerocheckStage { x_ab } = stage;
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

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        trace_stage("lincheck:", t_lincheck);
        claim
    }

    /// **Flock reduction (verifier).** Replay the SHA-256 zerocheck and
    /// lincheck straight off the shared transcript stream, recovering the one
    /// evaluation claim on the committed witness `q_flock`. Mirror of
    /// [`Self::prove_reduction`]; the PCS then discharges the returned claim.
    pub fn verify_reduction(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (R1CS digest) + announced count + commitment root.

        let zc_claim = crate::zerocheck::verify(self.r1cs.m, vs).map_err(verifier::VerifyError::Zerocheck)?;

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

    /// Read a big-endian I/O word back out of the unpacked witness, exercising
    /// the byte permutation from the reading side.
    fn read_be_word(z: &[bool], base: usize) -> u32 {
        (0..WORD_BITS).fold(0u32, |acc, j| acc | ((z[base + 8 * (3 - j / 8) + j % 8] as u32) << j))
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
        claim(M_BASE, 16 * WORD_BITS);
        claim(SCHED_BASE, N_SCHED * SCHED_STRIDE);
        claim(ROUND_BASE, N_ROUNDS * ROUND_STRIDE);
        claim(OUT_CARRY_BASE, 8 * CARRY_BITS_PER_ADD);
        claim(Z_CONST_POS, 1);
        for s in 0..K {
            let constrained = !a_0.rows[s].is_empty() || !b_0.rows[s].is_empty();
            assert_eq!(
                constrained, expected[s],
                "slot {s} constrained={constrained}, want {}",
                expected[s]
            );
        }
    }

    /// The witness's `out` slot holds `C(h, m)`, read back through the
    /// big-endian accessor. Pins the whole schedule, the rounds and the
    /// feed-forward against `primitives::sha2`.
    #[test]
    fn witness_encodes_correct_output() {
        let mut rng = Rng::new(0x5A2C_0DE5);
        for trial in 0..3 {
            let h: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            let z = generate_witness(&[(h, m)], 3);
            let expected = compress(h, m);
            for wd in 0..8 {
                assert_eq!(read_be_word(&z, out_word(wd)), expected[wd], "trial {trial}, out[{wd}]");
                assert_eq!(read_be_word(&z, h_word(wd)), h[wd], "trial {trial}, h[{wd}]");
            }
            for i in 0..16 {
                assert_eq!(read_be_word(&z, m_word(i)), m[i], "trial {trial}, m[{i}]");
            }
        }
    }

    /// The 64-byte hash the sponge and the Merkle parent run is one instance of
    /// this circuit, so the padding block is a real `sha2_eth`.
    #[test]
    fn pinned_block_is_a_64_byte_hash() {
        let msg: Vec<u8> = (0..64u8).collect();
        let m: [u32; 16] = std::array::from_fn(|i| u32::from_be_bytes(msg[4 * i..4 * i + 4].try_into().unwrap()));
        let (h_in, block) = pinned_compression(m);
        let out = compress(h_in, block);
        let mut digest = [0u8; 32];
        for (chunk, word) in digest.chunks_exact_mut(4).zip(&out) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        assert_eq!(digest, primitives::sha2::hash(&msg));
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        let mut rng = Rng::new(0x5A7157);
        let r1cs = build_block_r1cs(3);
        for n_blocks in [1usize, 5, 8] {
            let blocks: Vec<Compression> = (0..n_blocks)
                .map(|_| {
                    (
                        std::array::from_fn(|_| rng.next_u32()),
                        std::array::from_fn(|_| rng.next_u32()),
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
        let mut rng = Rng::new(0xDEAD);
        let r1cs = build_block_r1cs(3);
        let blocks = vec![(iv_64(), std::array::from_fn(|_| rng.next_u32()))];
        let mut z = generate_witness(&blocks, 3);
        assert!(r1cs.satisfies(&z));
        // One bit in each row kind, in the last round where the cascade into
        // the feed-forward is shortest and a wrong bit is least likely to be
        // caught by something else.
        for off in [
            R_CH + 5,
            R_MAJ + 9,
            R_T1A + 3,
            R_T1B + CARRY_BITS_PER_ADD + 4,
            R_ENEW + 7,
        ] {
            z[r_slot(N_ROUNDS - 1, off)] ^= true;
            assert!(
                !r1cs.satisfies(&z),
                "tampered bit at round offset {off} should violate R1CS"
            );
            z[r_slot(N_ROUNDS - 1, off)] ^= true;
        }
        assert!(r1cs.satisfies(&z), "restoring every bit should re-satisfy");
    }

    /// The circuit walk agrees with the built matrices on random weights. This
    /// is what pins the two representations of every gadget together.
    #[test]
    fn bilinear_walk_matches_matrices() {
        let (a_0, b_0) = matrices();
        let mut rng = Rng::new(0x11A1C);
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
            assert_eq!(bilinear_walk(alpha, &u, &w), va + alpha * vb, "batched, trial {trial}");
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
