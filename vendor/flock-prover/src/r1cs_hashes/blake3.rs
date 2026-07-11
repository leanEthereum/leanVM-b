//! Monolithic BLAKE3 compression-function R1CS — one R1CS instance per
//! `compress(cv, m, counter, block_len, flags) → state[16]` call. Encodes
//! the 16-word state init, all 7 rounds (8 G's per round + the message
//! permutation), and the final output XORs in one big sparse system.
//!
//! ## Encoding choice — "Option D" (minimum-slot)
//!
//! BLAKE3 has no AND-based Ch/Maj; the only nonlinear constraints are the
//! carry_aux bits of 32-bit ADDs. Per compression: 7 rounds × 8 G × 6 ADDs
//! × 31 carry_aux = **10,416 ANDs**. We materialize **only the irreducible
//! slots**:
//!
//! - **No sum-bit slots**. Each ADD's 32 sum bits expand into lin_funcs at
//!   the use site (`s[i] = X[i] ⊕ Y[i] ⊕ ⊕_{j<i} carry_aux[j]`).
//! - **No `a_new` / `c_new` lin-id slots**. Lanes 0–3 ("a" positions) and
//!   8–11 ("c" positions) cascade — every read of these lanes inlines the
//!   full chain of carry_aux references from prior G's that touched the
//!   lane. After 7 rounds this chain is deep, but the slot count stays
//!   tight enough to fit `k_log = 14`.
//! - **`b_new` / `d_new` lin-id slots only**. Lanes 4–7 ("b" positions) and
//!   12–15 ("d" positions) are materialized as 32-bit lin-id slots per G,
//!   so the next G's read of these lanes is a single-slot lookup. This
//!   breaks the cascade for half the lanes — without it, `prove`-time
//!   matrix density would blow up further.
//!
//! Trade-off: matrix is **substantially denser** than a "materialize all
//! sums" encoding, so the slow-path
//! `apply_{a,b,c}_packed` and `sparse_row_fold` are slower per K-block.
//! But K halves (2^15 → 2^14), which speeds up PCS commit/open and lets
//! more instances fit at the same `m`.
//!
//! ## Witness layout per compression block (`k_log = 14`, `k = 16,384`)
//!
//! I/O-aligned (see the layout-positions section below): cv and out_lo each
//! fill one clean 256-bit slot.
//!
//! ```text
//!   z[0      ..    256)        = cv[0..8]   (8 × 32-bit words, PINNED = IV)
//!   z[256    ..    512)        = out_lo[0..8] = state[0..8] ^ state[8..16]
//!   z[512]                     = 1                    (constant wire)
//!   z[513    ..    640)        = padding (forced to 0 by empty rows)
//!   z[640    ..  1,152)        = m[0..16]   (16 × 32-bit words, free)
//!   z[1,152  ..  1,184)        = counter_lo (PINNED = 0)
//!   z[1,184  ..  1,216)        = counter_hi (PINNED = 0)
//!   z[1,216  ..  1,248)        = block_len  (PINNED = 64)
//!   z[1,248  ..  1,280)        = flags      (PINNED = CHUNK_START|CHUNK_END|ROOT)
//!   z[1,280  .. 15,280)        = 56 G blocks × 250 bits each
//!   z[15,280 .. 15,536)        = out_hi[0..8] = state[8..16] ^ cv[0..8]
//!   z[15,536 .. 16,384)        = padding (forced to 0 by empty rows)
//! ```
//!
//! Per G block layout (250 bits):
//! ```text
//!   [0   .. 31)    carry_aux for ADD_TMP0  = a + b
//!   [31  .. 62)    carry_aux for ADD_A1    = ADD_TMP0 + mx        (→ a_1)
//!   [62  .. 93)    carry_aux for ADD_C1    = c + d_1              (→ c_1)
//!   [93  .. 124)   carry_aux for ADD_TMP1  = a_1 + b_1
//!   [124 .. 155)   carry_aux for ADD_A2    = ADD_TMP1 + my        (→ a_new)
//!   [155 .. 186)   carry_aux for ADD_C2    = c_1 + d_2            (→ c_new)
//!   [186 .. 218)   b_new = rotr7(b_1 ^ c_2)                (lin-id)
//!   [218 .. 250)   d_new = rotr8(d_1 ^ a_2)                (lin-id)
//! ```
//!
//! `tmp_0`, `a_1`, `c_1`, `tmp_1`, `a_2 (a_new)`, `c_2 (c_new)`, `d_1`,
//! `b_1`, `d_2` are NEVER materialized as slots — they're lin_funcs
//! evaluated at row-build time and threaded forward in the state cascade.
//!
//! ## Constraint shape (`C = I`)
//!
//! Every z-slot is the output of one R1CS row:
//!
//! | Row kind            | A_row            | B_row           | Output       |
//! |---------------------|------------------|-----------------|--------------|
//! | Constant `z[0]`     | `[0]`            | `[0]`           | `z[0]·z[0]`  |
//! | Input slot (m)      | `[slot]`         | `[Z_CONST]`     | `z[slot]·1`  |
//! | Pinned const, bit 1 | `[Z_CONST]`      | `[Z_CONST]`     | `1·1`        |
//! | Pinned const, bit 0 | `[]`             | `[]`            | `0·0`        |
//! | lin-id slot         | lin_func         | `[Z_CONST]`     | lin_func·1   |
//! | carry_aux           | lin_func_L       | lin_func_R      | (L)·(R)      |
//! | Padding             | `[]`             | `[]`            | `0·0`        |
//!
//! ## What this enforces
//!
//! - The 56 G-functions execute correctly: each ADD's carry_aux witness is
//!   constrained to `(X[i] ⊕ cin[i]) · (Y[i] ⊕ cin[i])`, so the sum bits
//!   `X[i] ⊕ Y[i] ⊕ cin[i]` are the correct 32-bit sum modulo 2³².
//! - `b_new`, `d_new` lin-id slots equal the right XOR-rotate of prior values.
//! - `out_lo[w] = state[w] ^ state[w+8]` and `out_hi[w] = state[w+8] ^ cv[w]`
//!   (BLAKE3 finalization).
//! - **Constant pinning**: `cv = IV`, `counter = 0`, `block_len = 64`,
//!   `flags = CHUNK_START|CHUNK_END|ROOT` via the pinned-const rows (given the
//!   lincheck const-wire pin forcing `z[Z_CONST] = 1`, see
//!   `docs/const-wire-pin.md`), so an instance can only be `blake3::hash` of
//!   one 64-byte block ([`pinned_compression`]).
//!
//! ## What this does NOT enforce
//!
//! - **Message binding**: the 512 `m` bits are free witness bits. PCS-level
//!   openings at fixed indices pin them to claimed public inputs.

use super::common::{BitRecord, add_carry_parts, or_bit_at, or_u32_at_bit, xor_dedup};
use flock_core::transcript::{ProverState, VerifierState};
use flock_core::field::F128;
use flock_core::pcs::Commitment;
use flock_core::r1cs::{BlockR1cs, SparseBinaryMatrix};
use flock_core::verifier;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one BLAKE3 compression occupies `2^K_LOG = 16,384` z slots.
pub const K_LOG: usize = 14;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim — must match [`flock_core::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

/// Number of BLAKE3 rounds.
pub const N_ROUNDS: usize = 7;
/// Number of G calls per round (4 column + 4 diagonal).
pub const N_G_PER_ROUND: usize = 8;
/// Total G calls per compression.
pub const N_G: usize = N_ROUNDS * N_G_PER_ROUND;
/// Bits per BLAKE3 word.
pub const WORD_BITS: usize = 32;

/// Carry_aux bits per 32-bit ADD (bit 0..30; bit 31 is the discarded
/// mod-2³² carry-out and isn't allocated).
pub const CARRY_BITS_PER_ADD: usize = WORD_BITS - 1; // 31
/// ADDs per G.
pub const ADDS_PER_G: usize = 6;
/// Lin-id 32-bit words per G (b_new, d_new).
pub const LIN_WORDS_PER_G: usize = 2;
/// Bits per G block (no sum-bit slots — see module docs).
pub const G_STRIDE: usize = ADDS_PER_G * CARRY_BITS_PER_ADD + LIN_WORDS_PER_G * WORD_BITS; // 250

/// BLAKE3 initial hash values (identical to SHA-256 IV).
pub const BLAKE3_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// BLAKE3 message permutation applied between rounds.
pub const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// Lanes touched by G index `g` within a round: `[a, b, c, d]`.
/// First 4 are column G's, last 4 are diagonal G's.
pub const G_LANES: [[usize; 4]; N_G_PER_ROUND] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

/// Message-index pairs `(mx, my)` consumed by G index `g` within a round,
/// indexing into the (already-permuted) per-round message buffer.
pub const G_MSG_IDX: [[usize; 2]; N_G_PER_ROUND] = [
    [0, 1],
    [2, 3],
    [4, 5],
    [6, 7],
    [8, 9],
    [10, 11],
    [12, 13],
    [14, 15],
];

// ---------------------------------------------------------------------------
// Layout positions (bit indices into the per-block z slice of length K)
// ---------------------------------------------------------------------------

// **I/O-aligned layout** for the hash chain (forked from `blake3`): the input
// chaining value `cv` lives in aligned slot 0 and the output chaining value
// `out_lo` (= state[0..8] ^ state[8..16]) in aligned slot 1 — each a clean
// 256-bit (`2^8`) window, so the chain shift argument folds them via a single
// tensor opening. cv/out_lo are *exactly* 256 bits, so the slots have NO
// interior padding. Everything else (const, m, counters, flags, G-blocks,
// out_hi) packs after the two slots. The re-layout is purely a change of these
// base offsets — all bit placement goes through the `*_bit` accessors below.
pub const SLOT_BITS: usize = 256; // 2^8, one 256-bit chaining value
pub const CV_BASE: usize = 0; // input region, slot 0: [0, 256)
pub const OUT_LO_BASE: usize = SLOT_BITS; // output region, slot 1: [256, 512)
pub const Z_CONST_POS: usize = 2 * SLOT_BITS; // 512
pub const M_BASE: usize = (Z_CONST_POS + 1).div_ceil(128) * 128; // 640 (128-aligned: leanVM single-PCS)
pub const T_LO_BASE: usize = M_BASE + 16 * WORD_BITS; // 1152
pub const T_HI_BASE: usize = T_LO_BASE + WORD_BITS; // 1184
pub const BLEN_BASE: usize = T_HI_BASE + WORD_BITS; // 1216
pub const FLAGS_BASE: usize = BLEN_BASE + WORD_BITS; // 1248
pub const GS_BASE: usize = FLAGS_BASE + WORD_BITS; // 1280
pub const OUT_HI_BASE: usize = GS_BASE + N_G * G_STRIDE; // 15,280
pub const USEFUL_BITS: usize = OUT_HI_BASE + 8 * WORD_BITS; // 15,536

// G sub-block: ADD `add_idx` ∈ 0..6 (carry_aux only), then lin-id
// `which` ∈ 0..2.
const ADD_TMP0: usize = 0;
const ADD_A1: usize = 1;
const ADD_C1: usize = 2;
const ADD_TMP1: usize = 3;
const ADD_A2: usize = 4;
const ADD_C2: usize = 5;
const LIN_B_NEW: usize = 0;
const LIN_D_NEW: usize = 1;

#[inline]
fn cv_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    CV_BASE + WORD_BITS * w + b
}
#[inline]
fn m_bit(i: usize, b: usize) -> usize {
    debug_assert!(i < 16 && b < WORD_BITS);
    M_BASE + WORD_BITS * i + b
}
#[inline]
fn g_add_carry_bit(g: usize, add_idx: usize, b: usize) -> usize {
    debug_assert!(g < N_G && add_idx < ADDS_PER_G && b < CARRY_BITS_PER_ADD);
    GS_BASE + G_STRIDE * g + CARRY_BITS_PER_ADD * add_idx + b
}
#[inline]
fn g_lin_bit(g: usize, which: usize, b: usize) -> usize {
    debug_assert!(g < N_G && which < LIN_WORDS_PER_G && b < WORD_BITS);
    GS_BASE + G_STRIDE * g + ADDS_PER_G * CARRY_BITS_PER_ADD + WORD_BITS * which + b
}
#[inline]
fn out_lo_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    OUT_LO_BASE + WORD_BITS * w + b
}
#[inline]
fn out_hi_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    OUT_HI_BASE + WORD_BITS * w + b
}

// ---------------------------------------------------------------------------
// Reference BLAKE3 compression — the witness oracle. Cross-checked against
// the `blake3` crate in tests.
// ---------------------------------------------------------------------------

#[inline]
fn g_fn(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(mx);
    state[d] = (state[d] ^ state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(12);
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(my);
    state[d] = (state[d] ^ state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(7);
}

fn round_fn(state: &mut [u32; 16], block: &[u32; 16]) {
    g_fn(state, 0, 4, 8, 12, block[0], block[1]);
    g_fn(state, 1, 5, 9, 13, block[2], block[3]);
    g_fn(state, 2, 6, 10, 14, block[4], block[5]);
    g_fn(state, 3, 7, 11, 15, block[6], block[7]);
    g_fn(state, 0, 5, 10, 15, block[8], block[9]);
    g_fn(state, 1, 6, 11, 12, block[10], block[11]);
    g_fn(state, 2, 7, 8, 13, block[12], block[13]);
    g_fn(state, 3, 4, 9, 14, block[14], block[15]);
}

fn permute(m: &mut [u32; 16]) {
    let mut permuted = [0u32; 16];
    for i in 0..16 {
        permuted[i] = m[MSG_PERMUTATION[i]];
    }
    *m = permuted;
}

/// BLAKE3 compression function. Returns the full 16-word output state
/// (post-finalization XOR). For chaining, the new CV is `out[0..8]`.
pub fn blake3_compress(
    cv: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [u32; 16] {
    let counter_low = counter as u32;
    let counter_high = (counter >> 32) as u32;
    let mut state = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        BLAKE3_IV[0],
        BLAKE3_IV[1],
        BLAKE3_IV[2],
        BLAKE3_IV[3],
        counter_low,
        counter_high,
        block_len,
        flags,
    ];
    let mut block = *block_words;
    for r in 0..N_ROUNDS {
        round_fn(&mut state, &block);
        if r + 1 < N_ROUNDS {
            permute(&mut block);
        }
    }
    for i in 0..8 {
        state[i] ^= state[i + 8];
        state[i + 8] ^= cv[i];
    }
    state
}

/// `per_round_msg_idx()[r][g] = (mx_idx, my_idx)` for round `r`, G index `g`
/// — i.e., `PERM^r [G_MSG_IDX[g]]`.
fn per_round_msg_idx() -> [[[usize; 2]; N_G_PER_ROUND]; N_ROUNDS] {
    let mut perm = [0usize; 16];
    for i in 0..16 {
        perm[i] = i;
    }
    let mut out = [[[0usize; 2]; N_G_PER_ROUND]; N_ROUNDS];
    for r in 0..N_ROUNDS {
        for g in 0..N_G_PER_ROUND {
            out[r][g][0] = perm[G_MSG_IDX[g][0]];
            out[r][g][1] = perm[G_MSG_IDX[g][1]];
        }
        let mut next = [0usize; 16];
        for i in 0..16 {
            next[i] = perm[MSG_PERMUTATION[i]];
        }
        perm = next;
    }
    out
}

// ---------------------------------------------------------------------------
// Lin_func cascade — per-bit lists of slot indices XOR'd to evaluate one bit.
//
// In Option D, sum bits aren't materialized as slots; instead, the "value" of
// any intermediate bit is a `LinBits[i] = Vec<usize>` whose XOR equals that
// bit. The G-builder threads these lin_funcs forward through the state, so
// each lane's value at any point in the protocol is represented as a `Word`.
// ---------------------------------------------------------------------------

/// A 32-bit symbolic word. `bits[i]` is a list of slot indices whose XOR
/// equals bit `i` of the word.
#[derive(Clone)]
struct Word {
    bits: [Vec<usize>; WORD_BITS],
}

impl Word {
    fn zero() -> Self {
        Self {
            bits: std::array::from_fn(|_| Vec::new()),
        }
    }
    /// Construct from a 32-bit witness or lin-id slot whose 32 bits live at
    /// `[base + 0, base + 1, …, base + 31]`.
    fn from_slot_base(base: usize) -> Self {
        Self {
            bits: std::array::from_fn(|i| vec![base + i]),
        }
    }
    /// Construct from a 32-bit constant — bit `i` is `[Z_CONST]` if set,
    /// `[]` otherwise.
    fn from_const(val: u32) -> Self {
        Self {
            bits: std::array::from_fn(|i| {
                if (val >> i) & 1 == 1 {
                    vec![Z_CONST_POS]
                } else {
                    Vec::new()
                }
            }),
        }
    }
    /// Bitwise XOR, no dedup. Caller calls `dedup()` after a chain if it
    /// wants canonical rows.
    fn xor(&self, other: &Word) -> Word {
        let mut out = self.clone();
        for i in 0..WORD_BITS {
            out.bits[i].extend(&other.bits[i]);
        }
        out
    }
    /// `rotr(n)` — pure index permutation; doesn't touch slot lists.
    fn rotr(&self, n: usize) -> Word {
        Word {
            bits: std::array::from_fn(|i| self.bits[(i + n) % WORD_BITS].clone()),
        }
    }
    /// Sort + cancel duplicates per bit.
    fn dedup(mut self) -> Word {
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

fn write_add_carry_rows(
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
// Initial lane sources at the start of compression.
// ---------------------------------------------------------------------------

fn initial_lane_words() -> [Word; 16] {
    let mut s: [Word; 16] = std::array::from_fn(|_| Word::zero());
    for w in 0..8 {
        s[w] = Word::from_slot_base(cv_bit(w, 0));
    }
    for i in 0..4 {
        s[8 + i] = Word::from_const(BLAKE3_IV[i]);
    }
    s[12] = Word::from_slot_base(T_LO_BASE);
    s[13] = Word::from_slot_base(T_HI_BASE);
    s[14] = Word::from_slot_base(BLEN_BASE);
    s[15] = Word::from_slot_base(FLAGS_BASE);
    s
}

// ---------------------------------------------------------------------------
// Matrix builder
// ---------------------------------------------------------------------------

/// Build the per-block base matrices `(A_0, B_0)`. `C_0 = I_k` (circuit-shape
/// R1CS — every z slot is the output of its row).
/// The fixed per-block R1CS matrices `(A0, B0)`, built once per process and
/// cached: verifiers (native reduced-claim checks, aggregation provers) treat
/// them as setup constants, not per-proof work.
pub fn matrices() -> &'static (SparseBinaryMatrix, SparseBinaryMatrix) {
    static MATRICES: std::sync::OnceLock<(SparseBinaryMatrix, SparseBinaryMatrix)> = std::sync::OnceLock::new();
    MATRICES.get_or_init(build_matrices)
}

pub fn build_matrices() -> (SparseBinaryMatrix, SparseBinaryMatrix) {
    let mut a_rows: Vec<Vec<usize>> = vec![Vec::new(); K];
    let mut b_rows: Vec<Vec<usize>> = vec![Vec::new(); K];

    // Constant z[0]: z[0]·z[0] = z[0]. Trivially satisfied for any boolean.
    a_rows[Z_CONST_POS] = vec![Z_CONST_POS];
    b_rows[Z_CONST_POS] = vec![Z_CONST_POS];

    // Free-input rows for the 512 message bits m (unconstrained when the
    // constant wire is 1).
    let mut input_emit = |base: usize, len: usize| {
        for j in 0..len {
            let s = base + j;
            a_rows[s] = vec![s];
            b_rows[s] = vec![Z_CONST_POS];
        }
    };
    input_emit(M_BASE, 16 * WORD_BITS);

    // Constant rows pin cv/counter/block_len/flags to the root-block
    // configuration: a set bit gets `z_const · z_const = z_s` (= 1 once the
    // lincheck const-wire pin forces z_const = 1), a clear bit keeps the empty
    // rows (`0·0 = z_s`).
    let mut const_emit = |base: usize, words: &[u32]| {
        for (w, &val) in words.iter().enumerate() {
            for j in 0..WORD_BITS {
                if (val >> j) & 1 == 1 {
                    let s = base + w * WORD_BITS + j;
                    a_rows[s] = vec![Z_CONST_POS];
                    b_rows[s] = vec![Z_CONST_POS];
                }
            }
        }
    };
    const_emit(CV_BASE, &BLAKE3_IV);
    const_emit(T_LO_BASE, &[0]);
    const_emit(T_HI_BASE, &[0]);
    const_emit(BLEN_BASE, &[PINNED_BLOCK_LEN]);
    const_emit(FLAGS_BASE, &[PINNED_FLAGS]);

    let msg_idx = per_round_msg_idx();
    let mut state: [Word; 16] = initial_lane_words();

    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let [mx_idx, my_idx] = msg_idx[r][g_in_round];

            // Snapshot inputs before any state mutation. Cloning is cheap
            // (lane Words point at the same slot lists — we never alias).
            let a = state[la].clone();
            let b = state[lb].clone();
            let c = state[lc].clone();
            let d = state[ld].clone();
            let mx = Word::from_slot_base(m_bit(mx_idx, 0));
            let my = Word::from_slot_base(m_bit(my_idx, 0));

            // tmp_0 = a + b
            let tmp_0 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &a,
                &b,
                g_add_carry_bit(g, ADD_TMP0, 0),
            );
            // a_1 = tmp_0 + mx
            let a_1 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &tmp_0,
                &mx,
                g_add_carry_bit(g, ADD_A1, 0),
            );
            // d_1 = rotr16(d ^ a_1)
            let d_1 = d.xor(&a_1).dedup().rotr(16);
            // c_1 = c + d_1
            let c_1 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &c,
                &d_1,
                g_add_carry_bit(g, ADD_C1, 0),
            );
            // b_1 = rotr12(b ^ c_1)
            let b_1 = b.xor(&c_1).dedup().rotr(12);
            // tmp_1 = a_1 + b_1
            let tmp_1 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &a_1,
                &b_1,
                g_add_carry_bit(g, ADD_TMP1, 0),
            );
            // a_2 = tmp_1 + my   (= a_new — cascades)
            let a_2 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &tmp_1,
                &my,
                g_add_carry_bit(g, ADD_A2, 0),
            );
            // d_2 = rotr8(d_1 ^ a_2)
            let d_2 = d_1.xor(&a_2).dedup().rotr(8);
            // c_2 = c_1 + d_2    (= c_new — cascades)
            let c_2 = write_add_carry_rows(
                &mut a_rows,
                &mut b_rows,
                &c_1,
                &d_2,
                g_add_carry_bit(g, ADD_C2, 0),
            );
            // b_new = rotr7(b_1 ^ c_2)    (materialized lin-id)
            let b_new_word = b_1.xor(&c_2).dedup().rotr(7);
            for i in 0..WORD_BITS {
                let s = g_lin_bit(g, LIN_B_NEW, i);
                a_rows[s] = b_new_word.bits[i].clone();
                b_rows[s] = vec![Z_CONST_POS];
            }
            // d_new = d_2                  (materialized lin-id)
            for i in 0..WORD_BITS {
                let s = g_lin_bit(g, LIN_D_NEW, i);
                a_rows[s] = d_2.bits[i].clone();
                b_rows[s] = vec![Z_CONST_POS];
            }

            // Advance the symbolic state. `a_2` and `c_2` keep cascading;
            // `b_new` and `d_new` reset to single-slot lookups.
            state[la] = a_2;
            state[lb] = Word::from_slot_base(g_lin_bit(g, LIN_B_NEW, 0));
            state[lc] = c_2;
            state[ld] = Word::from_slot_base(g_lin_bit(g, LIN_D_NEW, 0));
        }
    }

    // Finalization XORs.
    //   out_lo[w] = state[w] ^ state[w+8]
    //   out_hi[w] = state[w+8] ^ cv[w]
    for w in 0..8 {
        let lo = state[w].xor(&state[w + 8]).dedup();
        for i in 0..WORD_BITS {
            let s = out_lo_bit(w, i);
            a_rows[s] = lo.bits[i].clone();
            b_rows[s] = vec![Z_CONST_POS];
        }
        let cv_w = Word::from_slot_base(cv_bit(w, 0));
        let hi = state[w + 8].xor(&cv_w).dedup();
        for i in 0..WORD_BITS {
            let s = out_hi_bit(w, i);
            a_rows[s] = hi.bits[i].clone();
            b_rows[s] = vec![Z_CONST_POS];
        }
    }

    // Padding rows [USEFUL_BITS..K): A = B = []. Constraint 0·0 = z[i]
    // forces z[i] = 0 for all padding bits.

    let to_mat = |rows| SparseBinaryMatrix {
        num_rows: K,
        num_cols: K,
        rows,
    };
    (to_mat(a_rows), to_mat(b_rows))
}

/// Build a [`BlockR1cs`] batching `2^n_blocks_log` independent BLAKE3
/// compressions. `n_blocks_log ≥ 3` is required (lincheck needs `n_outer ≥ 8`).
pub fn build_block_r1cs(n_blocks_log: usize) -> BlockR1cs {
    let (a_0, b_0) = build_matrices();
    super::common::build_block_r1cs_with_matrices(
        n_blocks_log,
        K_LOG,
        K_SKIP,
        USEFUL_BITS,
        a_0,
        b_0,
        // Constant-wire pin (docs/const-wire-pin.md): forces z[Z_CONST_POS] = 1
        // in every block. Requires padding blocks filled with valid compressions.
        Some(Z_CONST_POS),
    )
}

// ---------------------------------------------------------------------------
// Witness generation (boolean)
// ---------------------------------------------------------------------------

/// Compute one 32-bit ADD, writing 31 carry_aux bits into `z` at `carry_base`.
/// Returns `x.wrapping_add(y)` (sum bits are NOT materialized in this
/// encoding — see module docs).
fn add_with_witness_carry_only(x: u32, y: u32, z: &mut [bool], carry_base: usize) -> u32 {
    let mut cin: u32 = 0;
    for i in 0..WORD_BITS {
        if i < CARRY_BITS_PER_ADD {
            let xi = (x >> i) & 1;
            let yi = (y >> i) & 1;
            let ci = (cin >> i) & 1;
            let carry_aux = (xi ^ ci) & (yi ^ ci);
            z[carry_base + i] = carry_aux == 1;
            let real_carry = carry_aux ^ ci;
            cin |= real_carry << (i + 1);
        }
    }
    x.wrapping_add(y)
}

#[inline]
fn write_word(z: &mut [bool], base: usize, val: u32) {
    for i in 0..WORD_BITS {
        z[base + i] = ((val >> i) & 1) == 1;
    }
}

/// Build the witness block for ONE compression. Length = `K`.
pub fn build_block_witness(
    cv: &[u32; 8],
    m: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> Vec<bool> {
    assert_pinned(&(*cv, *m, counter, block_len, flags));
    let mut z = vec![false; K];
    z[Z_CONST_POS] = true;
    // Inputs.
    for w in 0..8 {
        write_word(&mut z, cv_bit(w, 0), cv[w]);
    }
    for i in 0..16 {
        write_word(&mut z, m_bit(i, 0), m[i]);
    }
    let counter_lo = counter as u32;
    let counter_hi = (counter >> 32) as u32;
    write_word(&mut z, T_LO_BASE, counter_lo);
    write_word(&mut z, T_HI_BASE, counter_hi);
    write_word(&mut z, BLEN_BASE, block_len);
    write_word(&mut z, FLAGS_BASE, flags);

    // Internal state evolution (matches the matrix builder's symbolic
    // cascade by construction).
    let mut state: [u32; 16] = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        BLAKE3_IV[0],
        BLAKE3_IV[1],
        BLAKE3_IV[2],
        BLAKE3_IV[3],
        counter_lo,
        counter_hi,
        block_len,
        flags,
    ];
    let msg_idx = per_round_msg_idx();

    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let [mx_i, my_i] = msg_idx[r][g_in_round];
            let mx = m[mx_i];
            let my = m[my_i];

            let a = state[la];
            let b = state[lb];
            let c = state[lc];
            let d = state[ld];

            let tmp_0 = add_with_witness_carry_only(a, b, &mut z, g_add_carry_bit(g, ADD_TMP0, 0));
            let a_1 = add_with_witness_carry_only(tmp_0, mx, &mut z, g_add_carry_bit(g, ADD_A1, 0));
            let d_1 = (d ^ a_1).rotate_right(16);
            let c_1 = add_with_witness_carry_only(c, d_1, &mut z, g_add_carry_bit(g, ADD_C1, 0));
            let b_1 = (b ^ c_1).rotate_right(12);
            let tmp_1 =
                add_with_witness_carry_only(a_1, b_1, &mut z, g_add_carry_bit(g, ADD_TMP1, 0));
            let a_2 = add_with_witness_carry_only(tmp_1, my, &mut z, g_add_carry_bit(g, ADD_A2, 0));
            let d_2 = (d_1 ^ a_2).rotate_right(8);
            let c_2 = add_with_witness_carry_only(c_1, d_2, &mut z, g_add_carry_bit(g, ADD_C2, 0));
            let b_new = (b_1 ^ c_2).rotate_right(7);
            let d_new = d_2;
            write_word(&mut z, g_lin_bit(g, LIN_B_NEW, 0), b_new);
            write_word(&mut z, g_lin_bit(g, LIN_D_NEW, 0), d_new);

            state[la] = a_2;
            state[lb] = b_new;
            state[lc] = c_2;
            state[ld] = d_new;
        }
    }

    for w in 0..8 {
        let lo = state[w] ^ state[w + 8];
        let hi = state[w + 8] ^ cv[w];
        write_word(&mut z, out_lo_bit(w, 0), lo);
        write_word(&mut z, out_hi_bit(w, 0), hi);
    }
    z
}

/// Minimum `n_blocks_log` needed to prove `n_blocks` BLAKE3 compressions,
/// subject to the lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    let n = n_blocks.max(8);
    n.next_power_of_two().trailing_zeros() as usize
}

/// One BLAKE3 compression input: `(cv, m, counter, block_len, flags)`.
pub type Compression = ([u32; 8], [u32; 16], u64, u32, u32);

/// The pinned block length: one full 64-byte block.
pub const PINNED_BLOCK_LEN: u32 = 64;
/// The pinned flags: `CHUNK_START(1) | CHUNK_END(2) | ROOT(8)` — the single
/// 64-byte root block, under which the compression output equals
/// `blake3::hash` of the input.
pub const PINNED_FLAGS: u32 = (1 << 0) | (1 << 1) | (1 << 3);

/// The [`Compression`] of message `m` under the pinned configuration
/// (`cv = IV`, `counter = 0`, [`PINNED_BLOCK_LEN`], [`PINNED_FLAGS`]) — the
/// only shape satisfying the matrices' constant rows.
pub fn pinned_compression(m: [u32; 16]) -> Compression {
    (BLAKE3_IV, m, 0, PINNED_BLOCK_LEN, PINNED_FLAGS)
}

/// The padding instance: the pinned compression of the all-zero message,
/// i.e. `blake3(0^64)`. Fills unused trailing slots so every batched block —
/// padding included — is a valid instance with constant wire 1, as the
/// lincheck const-wire pin requires.
pub fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
}

/// Panic unless `block` matches the pinned configuration (only `m` is free) —
/// witness generation calls this so a non-conforming block fails fast instead
/// of surfacing as a zerocheck mismatch.
pub fn assert_pinned(block: &Compression) {
    let &(cv, _, counter, block_len, flags) = block;
    assert!(
        cv == BLAKE3_IV && counter == 0 && block_len == PINNED_BLOCK_LEN && flags == PINNED_FLAGS,
        "compression violates the pinned root-block configuration"
    );
}

/// Generate the boolean witness vector for `blocks.len()` independent BLAKE3
/// compressions, padded to `2^n_blocks_log` slots. Padding blocks run
/// [`padding_block`] (constant wire = 1). Parallel across instances via rayon.
pub fn generate_witness(blocks: &[Compression], n_blocks_log: usize) -> Vec<bool> {
    use rayon::prelude::*;
    let n_total = 1usize << n_blocks_log;
    let n_blocks = blocks.len();
    assert!(
        n_blocks <= n_total,
        "{n_blocks} compressions > 2^{n_blocks_log} = {n_total} slots"
    );
    let padding = padding_block();
    let mut z = vec![false; n_total * K];
    z.par_chunks_mut(K).enumerate().for_each(|(idx, chunk)| {
        let (cv, m, t, b, d) = if idx < n_blocks { blocks[idx] } else { padding };
        let block = build_block_witness(&cv, &m, t, b, d);
        chunk.copy_from_slice(&block);
    });
    z
}

// ---------------------------------------------------------------------------
// Fast witness generation with (a, b, c) — emits the R1CS row-witnesses
// directly from the BLAKE3 computation, in F_{2^128}-packed form. Skips the
// `apply_block_diag_packed` pass downstream.
//
// Row-witness semantics (matching `build_matrices`):
// - Constant z[0]:       (z, a, b, c) = (1, 1, 1, 1).
// - Free-input slot (m): (z, a, b, c) = (val, val, 1, val).
// - Pinned-const slot:   (z, a, b, c) = (val, val, val, val), val ∈ {0, 1}.
// - Lin-id slot:         (z, a, b, c) = (lin_val, lin_val, 1, lin_val).
// - Carry_aux row i:     (z, a, b, c) = (carry_aux, X⊕cin, Y⊕cin, carry_aux).
// - Padding row:         all zero (already zero on entry).
// ---------------------------------------------------------------------------

/// One 32-bit ADD: returns `(sum, left, right, carry_aux)` for the caller to
/// place into the per-G records. Sum bits are NOT materialized in this
/// encoding (Option D).
///
/// **c is not written.** Since `C = I` in this R1CS, `c == z` byte-for-byte,
/// so callers can use `z_packed` directly as the c-side input to zerocheck —
/// no separate c buffer is needed.
///
/// Word-level derivation:
/// ```text
///   sum       = x + y (mod 2^32)
///   cin       = sum ⊕ x ⊕ y          (since sum[i] = x[i] ⊕ y[i] ⊕ cin[i])
///   left      = x ⊕ cin              (per-bit X ⊕ cin → operand_x of carry row)
///   right     = y ⊕ cin              (per-bit Y ⊕ cin → operand_y of carry row)
///   carry_aux = left ∧ right
/// ```
/// Bit 31 is the discarded mod-2³² carry-out and is masked off so the
/// record push doesn't spill into the next slot.
// Record-relative positions: carries at 31·i, lin words after all carries.
const REC_C0: usize = 0;
const REC_C1: usize = CARRY_BITS_PER_ADD;
const REC_C2: usize = 2 * CARRY_BITS_PER_ADD;
const REC_C3: usize = 3 * CARRY_BITS_PER_ADD;
const REC_C4: usize = 4 * CARRY_BITS_PER_ADD;
const REC_C5: usize = 5 * CARRY_BITS_PER_ADD;
const REC_LIN0: usize = ADDS_PER_G * CARRY_BITS_PER_ADD;
const REC_LIN1: usize = REC_LIN0 + WORD_BITS;

/// Write a 32-bit lin-id (or input) slot: (z, a) = val, b = all-ones.
/// **c is not written** — same `c == z` aliasing trick as above.
#[inline]
fn write_lin_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, 0xFFFF_FFFF);
}

/// Constant-row word (cv/counter/blen/flags): set bits have `A = B =
/// [Z_CONST]`, so `(z, a, b) = (1, 1, 1)`; clear bits have empty rows, so
/// `(z, a, b) = (0, 0, 0)`. I.e. `a = b = z = val`.
fn write_const_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, val);
}

/// Build the (z, a, b) blocks for ONE compression instance, into u64 views
/// of the F128-packed per-block storage. Buffers must be zero on entry.
///
/// **No c buffer.** Since `C = I` (this is the circuit-shape R1CS), `c == z`
/// byte-for-byte; callers use `z_packed` directly as the c-side input to
/// zerocheck.
fn build_block_witness_ab_packed_into(
    cv: &[u32; 8],
    m: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
    z: &mut [u64],
    a: &mut [u64],
    b: &mut [u64],
) {
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    // Constant z[0] = 1; a/b also 1 (z[0]·z[0] = z[0]).
    or_bit_at(z, Z_CONST_POS);
    or_bit_at(a, Z_CONST_POS);
    or_bit_at(b, Z_CONST_POS);

    // Free-input rows (m) and constant rows (cv/counter/blen/flags).
    let counter_lo = counter as u32;
    let counter_hi = (counter >> 32) as u32;
    for w in 0..8 {
        write_const_word_ab_packed(cv_bit(w, 0), cv[w], z, a, b);
    }
    for i in 0..16 {
        write_lin_word_ab_packed(m_bit(i, 0), m[i], z, a, b);
    }
    write_const_word_ab_packed(T_LO_BASE, counter_lo, z, a, b);
    write_const_word_ab_packed(T_HI_BASE, counter_hi, z, a, b);
    write_const_word_ab_packed(BLEN_BASE, block_len, z, a, b);
    write_const_word_ab_packed(FLAGS_BASE, flags, z, a, b);

    // BLAKE3 state evolution.
    let mut state: [u32; 16] = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        BLAKE3_IV[0],
        BLAKE3_IV[1],
        BLAKE3_IV[2],
        BLAKE3_IV[3],
        counter_lo,
        counter_hi,
        block_len,
        flags,
    ];
    let msg_idx = per_round_msg_idx();
    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let [mx_i, my_i] = msg_idx[r][g_in_round];
            let mx = m[mx_i];
            let my = m[my_i];

            let a_val = state[la];
            let b_val = state[lb];
            let c_val = state[lc];
            let d_val = state[ld];

            let mut rz = BitRecord::<4>::new();
            let mut ra = BitRecord::<4>::new();
            let mut rb = BitRecord::<4>::new();

            macro_rules! add_into {
                ($pos:ident, $x:expr, $y:expr) => {{
                    let (sum, left, right, carry) = add_carry_parts($x, $y);
                    rz.push::<$pos>(carry);
                    ra.push::<$pos>(left);
                    rb.push::<$pos>(right);
                    sum
                }};
            }

            let tmp_0 = add_into!(REC_C0, a_val, b_val);
            let a_1 = add_into!(REC_C1, tmp_0, mx);
            let d_1 = (d_val ^ a_1).rotate_right(16);
            let c_1 = add_into!(REC_C2, c_val, d_1);
            let b_1 = (b_val ^ c_1).rotate_right(12);
            let tmp_1 = add_into!(REC_C3, a_1, b_1);
            let a_2 = add_into!(REC_C4, tmp_1, my);
            let d_2 = (d_1 ^ a_2).rotate_right(8);
            let c_2 = add_into!(REC_C5, c_1, d_2);
            let b_new = (b_1 ^ c_2).rotate_right(7);
            let d_new = d_2;
            rz.push::<REC_LIN0>(b_new);
            ra.push::<REC_LIN0>(b_new);
            rb.push::<REC_LIN0>(0xFFFF_FFFF);
            rz.push::<REC_LIN1>(d_new);
            ra.push::<REC_LIN1>(d_new);
            rb.push::<REC_LIN1>(0xFFFF_FFFF);

            let g_base = GS_BASE + G_STRIDE * g;
            rz.flush(z, g_base);
            ra.flush(a, g_base);
            rb.flush(b, g_base);

            state[la] = a_2;
            state[lb] = b_new;
            state[lc] = c_2;
            state[ld] = d_new;
        }
    }

    // Finalization XOR rows.
    for w in 0..8 {
        let lo = state[w] ^ state[w + 8];
        let hi = state[w + 8] ^ cv[w];
        write_lin_word_ab_packed(out_lo_bit(w, 0), lo, z, a, b);
        write_lin_word_ab_packed(out_hi_bit(w, 0), hi, z, a, b);
    }
}

/// **The fast path.** Produces `(z, a, b)` directly as F_{2^128}-packed
/// vectors — no bool intermediates, no `pack_witness` step, no
/// `apply_block_diag_packed`. Parallel across compression instances via rayon.
///
/// **No c buffer** — since `C = I` (circuit-shape R1CS), `c == z`
/// byte-for-byte; callers wrap `z_packed` as the c-side input to zerocheck.
pub fn generate_witness_with_ab_packed(
    blocks: &[Compression],
    n_blocks_log: usize,
) -> (
    Vec<flock_core::field::F128>,
    Vec<flock_core::field::F128>,
    Vec<flock_core::field::F128>,
) {
    use flock_core::field::F128;
    use rayon::prelude::*;
    let n_total = 1usize << n_blocks_log;
    let n_blocks = blocks.len();
    assert!(
        n_blocks <= n_total,
        "{n_blocks} compressions > 2^{n_blocks_log} = {n_total} slots"
    );
    blocks.iter().for_each(assert_pinned);

    const F128_PER_BLOCK: usize = K / 128;
    let total_f128 = n_total * F128_PER_BLOCK;
    let mut z = vec![F128::ZERO; total_f128];
    let mut a = vec![F128::ZERO; total_f128];
    let mut b = vec![F128::ZERO; total_f128];

    // Constant-wire pin (docs/const-wire-pin.md): padding slots get the pinned
    // compression of the all-zero message (constant wire = 1), matching
    // [`generate_witness_with_ab_packed_and_lincheck`].
    let padding = padding_block();

    z.par_chunks_mut(F128_PER_BLOCK)
        .zip(a.par_chunks_mut(F128_PER_BLOCK))
        .zip(b.par_chunks_mut(F128_PER_BLOCK))
        .enumerate()
        .for_each(|(idx, ((z_c, a_c), b_c))| {
            let (cv, m, t, bl, fl) = if idx < n_blocks {
                &blocks[idx]
            } else {
                &padding
            };
            // SAFETY: F128 is repr(C, align(16)) with LE u64 halves — same
            // byte layout as a u64 pair.
            let z_u64: &mut [u64] = unsafe {
                std::slice::from_raw_parts_mut(z_c.as_mut_ptr() as *mut u64, z_c.len() * 2)
            };
            let a_u64: &mut [u64] = unsafe {
                std::slice::from_raw_parts_mut(a_c.as_mut_ptr() as *mut u64, a_c.len() * 2)
            };
            let b_u64: &mut [u64] = unsafe {
                std::slice::from_raw_parts_mut(b_c.as_mut_ptr() as *mut u64, b_c.len() * 2)
            };
            build_block_witness_ab_packed_into(cv, m, *t, *bl, *fl, z_u64, a_u64, b_u64);
        });

    (z, a, b)
}

/// Like [`generate_witness_with_ab_packed`] but also emits the lincheck
/// byte-stripe layout in the same parallel pass. Replaces the separate
/// `pack_z_lincheck_from_packed` call entirely.
///
/// Returns `(z, a, b, z_lincheck)`; **no c buffer** (c == z byte-for-byte).
///
/// `z_lincheck` has length `n_total · K / 8`, indexed as
/// `z_lincheck[byte_idx · K + i_inner]`, with bit `r` of that byte equal to
/// `z[i_inner, 8·byte_idx + r]`.
///
/// Parallelism granularity: 8 compressions per task; each task writes its 8
/// commit chunks then bit-transposes the just-written z u64s into its
/// lincheck stripe while they are still hot in L1.
pub fn generate_witness_with_ab_packed_and_lincheck(
    blocks: &[Compression],
    n_blocks_log: usize,
) -> (
    Vec<flock_core::field::F128>,
    Vec<flock_core::field::F128>,
    Vec<flock_core::field::F128>,
    Vec<u8>,
) {
    // Constant-wire pin (docs/const-wire-pin.md): fill padding blocks with the
    // pinned compression of the all-zero message so the constant cell is 1 in
    // every block. (The chain forbids padding, so this only affects the
    // standalone batch setup.)
    let padding = padding_block();
    blocks.iter().for_each(assert_pinned);
    super::common::drive_witness_packed_and_lincheck(
        blocks,
        Some(&padding),
        n_blocks_log,
        K_LOG,
        |block: &Compression, z_u64, a_u64, b_u64| {
            let (cv, m, t, bl, fl) = block;
            build_block_witness_ab_packed_into(cv, m, *t, *bl, *fl, z_u64, a_u64, b_u64);
        },
    )
}

// ---------------------------------------------------------------------------
// Convenience API: Blake3Setup
// ---------------------------------------------------------------------------

/// Bundles the monolithic BLAKE3 compression R1CS sized for `n_blocks`
/// compressions.
#[derive(Clone, Debug)]
pub struct Blake3Setup {
    pub n_blocks: usize,
    pub r1cs: BlockR1cs,
}

impl Blake3Setup {
    /// Build a setup for `n_blocks` BLAKE3 compressions.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        let r1cs = build_block_r1cs(n_log);
        // Warm the CSC fold circuit here so its one-time build (a pass over
        // ~21M nonzeros) stays out of the first prove/verify, and pre-fault
        // the prove-cycle scratch buffers (see scratch::prewarm_prover).
        r1cs.csc_lincheck_circuit();
        flock_core::scratch::prewarm_prover(r1cs.m);
        Self { n_blocks, r1cs }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// SplitMix64.
    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u32(&mut self) -> u32 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            (z ^ (z >> 31)) as u32
        }
    }

    /// BLAKE3 chunk flags (subset).
    const CHUNK_START: u32 = 1 << 0;
    const CHUNK_END: u32 = 1 << 1;
    const ROOT: u32 = 1 << 3;

    #[test]
    fn layout_constants() {
        // I/O-aligned layout: cv in slot 0, out_lo in slot 1 (both 256-bit).
        assert_eq!(CV_BASE, 0);
        assert_eq!(OUT_LO_BASE, 256);
        assert_eq!(Z_CONST_POS, 512);
        assert_eq!(M_BASE, 640);
        assert_eq!(GS_BASE, 1280);
        assert_eq!(G_STRIDE, 250);
        assert_eq!(N_G, 56);
        assert_eq!(OUT_HI_BASE, 15_280);
        assert_eq!(USEFUL_BITS, 15_536);
        assert!(USEFUL_BITS <= K);
        assert_eq!(CV_BASE % SLOT_BITS, 0);
        assert_eq!(OUT_LO_BASE % SLOT_BITS, 0);
    }

    /// Reference compression matches the `blake3` crate for empty input
    /// (a single root-block, single-chunk, ROOT-flagged compression).
    #[test]
    fn compress_matches_blake3_crate_empty() {
        let state = blake3_compress(
            &BLAKE3_IV,
            &[0u32; 16],
            0,
            0,
            CHUNK_START | CHUNK_END | ROOT,
        );
        let mut got = [0u8; 32];
        for w in 0..8 {
            got[w * 4..w * 4 + 4].copy_from_slice(&state[w].to_le_bytes());
        }
        let expected = *::blake3::hash(b"").as_bytes();
        assert_eq!(got, expected);
    }

    /// Reference compression matches the `blake3` crate for a full 64-byte
    /// input (single block + single chunk + root).
    #[test]
    fn compress_matches_blake3_crate_64_bytes() {
        let mut rng = Rng::new(0xDEAD_BEEF);
        let mut bytes = [0u8; 64];
        for byte in bytes.iter_mut() {
            *byte = (rng.next_u32() & 0xFF) as u8;
        }
        let mut m = [0u32; 16];
        for i in 0..16 {
            m[i] = u32::from_le_bytes(bytes[i * 4..i * 4 + 4].try_into().unwrap());
        }
        let state = blake3_compress(&BLAKE3_IV, &m, 0, 64, CHUNK_START | CHUNK_END | ROOT);
        let mut got = [0u8; 32];
        for w in 0..8 {
            got[w * 4..w * 4 + 4].copy_from_slice(&state[w].to_le_bytes());
        }
        let expected = *::blake3::hash(&bytes).as_bytes();
        assert_eq!(got, expected);
    }

    /// Witness's out_lo / out_hi slots equal the BLAKE3 finalization XORs.
    #[test]
    fn witness_encodes_correct_output() {
        let mut rng = Rng::new(0x1234_5678);
        let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
        let (cv, m, counter, block_len, flags) = pinned_compression(m);
        let z = build_block_witness(&cv, &m, counter, block_len, flags);
        let expected = blake3_compress(&cv, &m, counter, block_len, flags);
        for w in 0..8 {
            let mut got = 0u32;
            for b in 0..WORD_BITS {
                if z[out_lo_bit(w, b)] {
                    got |= 1 << b;
                }
            }
            assert_eq!(got, expected[w], "out_lo[{w}] mismatch");
            let mut got_hi = 0u32;
            for b in 0..WORD_BITS {
                if z[out_hi_bit(w, b)] {
                    got_hi |= 1 << b;
                }
            }
            assert_eq!(got_hi, expected[w + 8], "out_hi[{w}] mismatch");
        }
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        let mut rng = Rng::new(0xCAFE_F00D);
        for &n_blocks in &[1usize, 3, 8] {
            let n_log = min_n_blocks_log(n_blocks).max(3);
            let r1cs = build_block_r1cs(n_log);
            let blocks: Vec<Compression> = (0..n_blocks)
                .map(|_| {
                    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                    pinned_compression(m)
                })
                .collect();
            let z = generate_witness(&blocks, n_log);
            assert_eq!(z.len(), r1cs.n());
            assert!(
                r1cs.satisfies(&z),
                "witness for {n_blocks} compressions fails R1CS"
            );
        }
    }

    #[test]
    fn mutated_witness_fails() {
        let mut rng = Rng::new(0xBEEF_F00D);
        let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
        let r1cs = build_block_r1cs(3);
        let blocks = vec![pinned_compression(m)];
        let mut z = generate_witness(&blocks, 3);
        assert!(r1cs.satisfies(&z));
        // Flip a carry_aux bit inside G #10 (middle of round 1).
        z[g_add_carry_bit(10, ADD_A2, 5)] ^= true;
        assert!(
            !r1cs.satisfies(&z),
            "tampered carry bit should violate R1CS"
        );
    }

    /// The fused generator produces (z, a, b) byte-identical to
    /// `generate_witness_with_ab_packed` AND a lincheck stripe byte-identical
    /// to `pack_z_lincheck_from_packed(z)`.
    #[test]
    fn fused_lincheck_matches_separate() {
        use flock_core::lincheck::pack_z_lincheck_from_packed;
        for &n_blocks in &[1usize, 4, 8, 13] {
            let n_log = min_n_blocks_log(n_blocks).max(3);
            let r1cs = build_block_r1cs(n_log);
            let mut rng = Rng::new(0xABCD_EF00 + n_blocks as u64);
            let blocks: Vec<Compression> = (0..n_blocks)
                .map(|_| {
                    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                    pinned_compression(m)
                })
                .collect();

            let (z1, a1, b1) = generate_witness_with_ab_packed(&blocks, n_log);
            let lincheck_ref = pack_z_lincheck_from_packed(&z1, r1cs.m, r1cs.k_log);
            let (z2, a2, b2, lincheck_new) =
                generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
            assert_eq!(z1, z2, "z mismatch at n_blocks={n_blocks}");
            assert_eq!(a1, a2, "a mismatch at n_blocks={n_blocks}");
            assert_eq!(b1, b2, "b mismatch at n_blocks={n_blocks}");
            assert_eq!(
                lincheck_ref, lincheck_new,
                "lincheck stripe mismatch at n_blocks={n_blocks}"
            );
        }
    }

    #[test]
    fn setup_sizes_correctly() {
        for &(n_blocks, expected_n_log) in
            &[(1usize, 3), (8, 3), (9, 4), (16, 4), (17, 5), (1000, 10)]
        {
            let setup = Blake3Setup::new(n_blocks);
            assert_eq!(setup.n_blocks_log(), expected_n_log, "n_blocks={n_blocks}");
            assert_eq!(setup.m(), K_LOG + expected_n_log);
            assert!(setup.n_block_slots() >= n_blocks);
        }
    }

    /// Constant-wire pin (docs/const-wire-pin.md): the all-zero witness
    /// satisfies every R1CS row (0·0 = 0), so the pin carried by the lincheck
    /// circuit is the ONLY thing rejecting it. Run the kept zerocheck +
    /// lincheck reduction on zeroed buffers and assert the lincheck verifier
    /// rejects (the all-ones const column is absent).
    #[test]
    fn const_pin_all_zero_rejected() {
        let setup = Blake3Setup::new(5);
        let r1cs = &setup.r1cs;
        let inner_rest_len = r1cs.k_log - r1cs.k_skip;

        // Correctly-shaped buffers (padding-only generation), then zeroed.
        let (mut z, mut a, mut b, mut zlc) =
            generate_witness_with_ab_packed_and_lincheck(&[], setup.n_blocks_log());
        z.fill(F128::ZERO);
        a.fill(F128::ZERO);
        b.fill(F128::ZERO);
        zlc.fill(0);

        // Prover side: the reduction happily runs on the zero witness.
        let padding = flock_core::zerocheck::PaddingSpec {
            k_log: r1cs.k_log,
            useful_bits_per_block: r1cs.useful_bits,
        };
        let as_bytes = |v: &[F128]| unsafe {
            std::slice::from_raw_parts(
                v.as_ptr() as *const u8,
                v.len() * core::mem::size_of::<F128>(),
            )
        };
        let mut ps = flock_core::transcript::ProverState::new(b"const-pin-poc", &[]);
        let (zc_claim, _s_hat_v_c) = flock_core::zerocheck::prove_packed_padded_capture_s_hat_v_c(
            as_bytes(&a),
            as_bytes(&b),
            as_bytes(&z), // C = I, so c == z
            r1cs.m,
            &padding,
            &mut ps,
        );
        let x_ab = flock_core::lincheck::QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
        };
        let _ = flock_core::lincheck::prove_padded_capture_z_vec(
            &zlc,
            r1cs.m,
            r1cs.k_log,
            r1cs.k_skip,
            r1cs.useful_bits,
            r1cs.csc_lincheck_circuit(),
            &x_ab,
            &mut ps,
        );
        let proof_t = ps.into_proof();

        // Verifier side: zerocheck accepts, the lincheck const-wire pin rejects.
        let mut vs = flock_core::transcript::VerifierState::new(b"const-pin-poc", &proof_t, &[]);
        let zc = flock_core::zerocheck::verify(r1cs.m, &mut vs)
            .expect("zerocheck accepts the all-zero witness");
        let x_ab_v = flock_core::lincheck::QuirkyPoint {
            z_skip: zc.z,
            x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
        };
        let res = flock_core::lincheck::verify(
            r1cs.m,
            r1cs.k_log,
            r1cs.k_skip,
            r1cs.csc_lincheck_circuit(),
            &x_ab_v,
            zc.a_eval,
            zc.b_eval,
            &mut vs,
        );
        assert!(
            matches!(
                res,
                Err(flock_core::lincheck::VerifyError::ConsistencyFailed { .. })
            ),
            "all-zero witness must be rejected by the constant-wire pin; got {res:?}"
        );
    }
}

// ===== leanVM-b stacked BLAKE3 reduction (grafted) =====
// (No Blake3StackProof struct: the zerocheck / lincheck / ring-switch scalars
// ride the shared transcript stream, and the one hash-bearing Ligerito rides
// the caller's opening channel.)

/// One claim on the committed packed BLAKE3 witness `q_pkd`, as left by the
/// Flock reduction and handed to the PCS. `claim` is the `ẑ(point) = value`
/// evaluation the PCS must discharge; `s_hat_v` is the prover-only ring-switch
/// tensor weight the packed open consumes (`None` when `k_log < LOG_PACKING`,
/// and unused on the verifier side, which recovers it from `proof.open`).
#[derive(Clone, Debug)]
pub struct WitnessClaim {
    pub claim: flock_core::proof::ZClaim,
    pub s_hat_v: Option<Vec<F128>>,
}

/// The two claims on the committed witness `q_pkd` left by the Flock BLAKE3
/// zerocheck + lincheck reduction, for the PCS to discharge:
/// - `ab`: the `A∘B` side, from lincheck.
/// - `c` : the `C` side, from zerocheck (`C = I`, so a direct z-claim).
///
/// This is the clean seam between Flock's reduction and the PCS: the reduction
/// produces these; the PCS opens them (see [`Blake3Setup::prove_reduction`]).
#[derive(Clone, Debug)]
pub struct ReducedClaims {
    pub ab: WitnessClaim,
    pub c: WitnessClaim,
}

/// Everything [`Blake3Setup::verify_reduction`] recovers: the two `(ab, c)`
/// z-claims for the PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub ab: flock_core::proof::ZClaim,
    pub c: flock_core::proof::ZClaim,
    pub zc_claim: flock_core::zerocheck::ZerocheckClaim,
    pub lc_claim: flock_core::lincheck::LincheckClaim,
}

/// Construct a multilinear `x_outer_full` of length `m − k_skip` from a
/// QuirkyPoint: concatenate `x_inner_rest` and `x_outer`. This is the format
/// the PCS expects (k_skip = 6 absorbed via `z_skip`; everything else is
/// multilinear).
fn quirky_x_outer_full(point: &flock_core::lincheck::QuirkyPoint) -> Vec<F128> {
    let mut v = Vec::with_capacity(point.x_inner_rest.len() + point.x_outer.len());
    v.extend_from_slice(&point.x_inner_rest);
    v.extend_from_slice(&point.x_outer);
    v
}

impl Blake3Setup {
    /// **Flock reduction (prover).** Bind the statement, then run the BLAKE3
    /// zerocheck and lincheck on the shared `sponge`, reducing R1CS validity
    /// of `blocks` to two evaluation claims on the committed packed witness
    /// `q_pkd` (see `flock.tex` §zerocheck/§lincheck). Returns:
    /// - `z_packed`: the regenerated packed witness the PCS later opens against;
    /// - the transmitted zerocheck / lincheck sub-proofs;
    /// - the [`ReducedClaims`] `(ab, c)` on `q_pkd`, with ring-switch weights.
    ///
    /// This touches the commitment only to *bind* it — it does NOT open the PCS.
    /// The caller discharges the returned claims (see [`Self::prove_validity_stacked`]).
    pub fn prove_reduction(
        &self,
        blocks: &[Compression],
        stack_commitment: &Commitment,
        ps: &mut ProverState,
    ) -> (Vec<F128>, ReducedClaims) {
        assert_eq!(blocks.len(), self.n_blocks);
        let n_log = self.n_blocks_log();
        let (z_packed, a_packed_f128, b_packed_f128, z_packed_lincheck) =
            generate_witness_with_ab_packed_and_lincheck(blocks, n_log);

        // No bind_statement here: the embedding protocol (leanVM-b) seeds its
        // transcript with the circuit-FAMILY digest and binds the instance
        // count and commitment root before any challenge, so the statement is
        // already fully transcript-bound. `_ = stack_commitment` keeps the
        // symmetric signature.
        let _ = stack_commitment;

        let padding = flock_core::zerocheck::PaddingSpec {
            k_log: self.r1cs.k_log,
            useful_bits_per_block: self.r1cs.useful_bits,
        };
        let (zc_claim, s_hat_v_c) = {
            let a_packed: &[u8] = unsafe {
                std::slice::from_raw_parts(
                    a_packed_f128.as_ptr() as *const u8,
                    a_packed_f128.len() * core::mem::size_of::<F128>(),
                )
            };
            let b_packed: &[u8] = unsafe {
                std::slice::from_raw_parts(
                    b_packed_f128.as_ptr() as *const u8,
                    b_packed_f128.len() * core::mem::size_of::<F128>(),
                )
            };
            let c_packed: &[u8] = unsafe {
                std::slice::from_raw_parts(
                    z_packed.as_ptr() as *const u8,
                    z_packed.len() * core::mem::size_of::<F128>(),
                )
            };
            flock_core::zerocheck::prove_packed_padded_capture_s_hat_v_c(
                a_packed, b_packed, c_packed, self.r1cs.m, &padding, ps,
            )
        };

        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = flock_core::lincheck::QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
        };
        let (lc_claim, z_vec_pre) = flock_core::lincheck::prove_padded_capture_z_vec(
            &z_packed_lincheck,
            self.r1cs.m,
            self.r1cs.k_log,
            self.r1cs.k_skip,
            self.r1cs.useful_bits,
            self.r1cs.csc_lincheck_circuit(),
            &x_ab,
            ps,
        );

        let ab = flock_core::proof::ZClaim {
            point: flock_core::lincheck::QuirkyPoint {
                z_skip: lc_claim.r_inner_skip,
                x_inner_rest: lc_claim.r_inner_rest.clone(),
                x_outer: x_ab.x_outer.clone(),
            },
            value: lc_claim.w,
        };
        let c = flock_core::proof::ZClaim {
            point: flock_core::lincheck::QuirkyPoint {
                z_skip: zc_claim.z,
                x_inner_rest: zc_claim.r_rest[..inner_rest_len].to_vec(),
                x_outer: zc_claim.r_rest[inner_rest_len..].to_vec(),
            },
            value: zc_claim.c_eval,
        };
        let s_hat_v_ab = if self.r1cs.k_log >= flock_core::pcs::LOG_PACKING {
            Some(flock_core::pcs::ring_switch::s_hat_v_from_z_vec(
                &z_vec_pre,
                &lc_claim.r_inner_rest[1..],
            ))
        } else {
            None
        };

        let reduced = ReducedClaims {
            ab: WitnessClaim { claim: ab, s_hat_v: s_hat_v_ab },
            c: WitnessClaim { claim: c, s_hat_v: Some(s_hat_v_c) },
        };
        (z_packed, reduced)
    }

    /// Prove `blocks` are valid compressions in two clean phases:
    /// 1. [`Self::prove_reduction`] — Flock zerocheck + lincheck → the `(ab, c)`
    ///    claims on the committed witness `q_pkd`;
    /// 2. the PCS: discharge those claims *together with* the caller's own
    ///    `stack_pd` point claims in ONE stacked Ligerito open over `stack` (the
    ///    caller's committed witness, with `q_pkd` the aligned sub-block at
    ///    `stack_offset`).
    ///
    /// `stack_data`/`stack_commitment` are the caller's commit; the transcript
    /// `sponge` is shared.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_validity_stacked(
        &self,
        blocks: &[Compression],
        stack: &[F128],
        stack_offset: usize,
        stack_data: &flock_core::pcs::ProverData,
        stack_commitment: &Commitment,
        stack_pd: &[(Vec<F128>, F128)],
        ps: &mut ProverState,
    ) -> flock_core::pcs::ligerito::LigeritoProof {
        // Phase 1 — Flock reduction: zerocheck + lincheck → claims on q_pkd.
        let (z_packed, reduced) = self.prove_reduction(blocks, stack_commitment, ps);
        debug_assert_eq!(
            &stack[stack_offset..stack_offset + z_packed.len()],
            z_packed.as_slice(),
            "committed q_pkd slice must equal the regenerated packed witness"
        );

        // Phase 2 — PCS: discharge the reduction's claims (plus the caller's
        // full-stack point claims) in one stacked open.
        self.discharge_reduction_stacked(
            &z_packed,
            &reduced,
            stack,
            stack_offset,
            stack_data,
            stack_commitment,
            stack_pd,
            ps,
        )
    }

    /// Phase 2 of [`Self::prove_validity_stacked`]: the PCS open of the
    /// reduction's `(ab, c)` claims on `q_pkd` (`z_packed`), lifted into the
    /// caller's `stack` and batched with the caller's `stack_pd` point claims.
    #[allow(clippy::too_many_arguments)]
    fn discharge_reduction_stacked(
        &self,
        z_packed: &[F128],
        reduced: &ReducedClaims,
        stack: &[F128],
        stack_offset: usize,
        stack_data: &flock_core::pcs::ProverData,
        stack_commitment: &Commitment,
        stack_pd: &[(Vec<F128>, F128)],
        ps: &mut ProverState,
    ) -> flock_core::pcs::ligerito::LigeritoProof {
        let padding = flock_core::zerocheck::PaddingSpec {
            k_log: self.r1cs.k_log,
            useful_bits_per_block: self.r1cs.useful_bits,
        };
        let ab_x = quirky_x_outer_full(&reduced.ab.claim.point);
        let c_x = quirky_x_outer_full(&reduced.c.claim.point);
        // This standalone-flock path takes general full-stack point claims.
        let pd: Vec<flock_core::pcs::StackClaim> = stack_pd
            .iter()
            .map(|(point, value)| flock_core::pcs::StackClaim::Point { point, value: *value })
            .collect();
        let (lig_config, _) = stacked_lig_configs(stack_commitment);
        flock_core::pcs::open_batch_mixed_ligerito_stacked(
            z_packed,
            &[ab_x.as_slice(), c_x.as_slice()],
            &[reduced.ab.s_hat_v.as_deref(), reduced.c.s_hat_v.as_deref()],
            &padding,
            stack,
            stack_offset,
            stack_data,
            stack_commitment,
            &pd,
            &lig_config,
            ps,
        )
    }

    /// **Flock reduction (verifier).** Bind the statement, then replay the BLAKE3
    /// zerocheck and lincheck from `zerocheck`/`lincheck` on the shared
    /// `sponge`, recovering the two `(ab, c)` evaluation claims on the
    /// committed witness `q_pkd`. Mirror of [`Self::prove_reduction`]; the PCS
    /// then discharges the returned claims (see [`Self::verify_validity_stacked`]).
    pub fn verify_reduction(
        &self,
        stack_commitment: &Commitment,
        vs: &mut VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (family digest) + announced count + commitment root.
        let _ = stack_commitment;

        let zc_claim = flock_core::zerocheck::verify(self.r1cs.m, vs)
            .map_err(verifier::VerifyError::Zerocheck)?;
        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = flock_core::lincheck::QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
        };
        let lc_claim = flock_core::lincheck::verify(
            self.r1cs.m,
            self.r1cs.k_log,
            self.r1cs.k_skip,
            self.r1cs.csc_lincheck_circuit(),
            &x_ab,
            zc_claim.a_eval,
            zc_claim.b_eval,
            vs,
        )
        .map_err(verifier::VerifyError::Lincheck)?;

        let ab = flock_core::proof::ZClaim {
            point: flock_core::lincheck::QuirkyPoint {
                z_skip: lc_claim.r_inner_skip,
                x_inner_rest: lc_claim.r_inner_rest.clone(),
                x_outer: x_ab.x_outer.clone(),
            },
            value: lc_claim.w,
        };
        let c = flock_core::proof::ZClaim {
            point: flock_core::lincheck::QuirkyPoint {
                z_skip: zc_claim.z,
                x_inner_rest: zc_claim.r_rest[..inner_rest_len].to_vec(),
                x_outer: zc_claim.r_rest[inner_rest_len..].to_vec(),
            },
            value: zc_claim.c_eval,
        };
        Ok(ReductionReplay { ab, c, zc_claim, lc_claim })
    }

    /// Verifier mirror of [`Self::prove_validity_stacked`], in the same two
    /// phases: (1) [`Self::verify_reduction`] replays zerocheck + lincheck to
    /// recover the `(ab, c)` claims on `q_pkd`, then (2) the stacked Ligerito
    /// opening of those claims (and the caller's `stack_pd`) is verified against
    /// `stack_commitment`. `stack_offset` and the derived `qpkd_vars` locate
    /// `q_pkd` inside the stack.
    pub fn verify_validity_stacked(
        &self,
        stack_commitment: &Commitment,
        stack_offset: usize,
        stack_pd: &[(Vec<F128>, F128)],
        open: &flock_core::pcs::ligerito::LigeritoProof,
        vs: &mut VerifierState<'_>,
    ) -> Result<(), verifier::VerifyError> {
        // Phase 1 — Flock reduction: replay zerocheck + lincheck → (ab, c).
        let ReductionReplay { ab, c, .. } = self.verify_reduction(stack_commitment, vs)?;

        // Phase 2 — PCS: verify the stacked opening of (ab, c) + stack_pd.
        let ab_x = quirky_x_outer_full(&ab.point);
        let c_x = quirky_x_outer_full(&c.point);
        let qpkd_vars = self.r1cs.m - flock_core::pcs::LOG_PACKING;
        let pd: Vec<flock_core::pcs::StackClaim> = stack_pd
            .iter()
            .map(|(point, value)| flock_core::pcs::StackClaim::Point { point, value: *value })
            .collect();
        let (_, lig_config) = stacked_lig_configs(stack_commitment);
        flock_core::pcs::verify_opening_batch_mixed_ligerito_stacked(
            stack_commitment,
            stack_offset,
            qpkd_vars,
            &[ab.value, c.value],
            &[ab.point.z_skip, c.point.z_skip],
            &[ab_x.as_slice(), c_x.as_slice()],
            &pd,
            open,
            &lig_config,
            vs,
        )
        .map(|_| ())
        .map_err(verifier::VerifyError::PcsAb)
    }
}

/// The Ligerito (prover, verifier) config pair for a stacked open against
/// `stack_commitment` — derived from the commitment's own `(m, profile)` params,
/// so both sides agree by construction.
fn stacked_lig_configs(
    stack_commitment: &Commitment,
) -> (
    flock_core::pcs::ligerito::ProverConfig,
    flock_core::pcs::ligerito::VerifierConfig,
) {
    flock_core::pcs::ligerito::LigeritoSecurityConfig::derive_profile(
        stack_commitment.params.m,
        stack_commitment.params.profile,
    )
    .and_then(|sec| sec.to_prover_verifier_configs())
    .expect("ligerito config for stacked open")
}
