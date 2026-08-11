// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! Monolithic BLAKE3 compression-function R1CS: one R1CS instance per
//! `compress(cv, m, counter, block_len, flags) → state[16]` call. Encodes
//! the 16-word state init, all 7 rounds (8 G's per round + the message
//! permutation), and the final output XORs in one big sparse system.
//!
//! ## Encoding choice: "Option D" (minimum-slot)
//!
//! BLAKE3 has no AND-based Ch/Maj; the only nonlinear constraints are the
//! product bits of 32-bit ADDs. Per compression: 7 rounds × 8 G × (2 fused
//! three-operand ADDs × 61 + 2 two-operand ADDs × 31) = **10,304 ANDs**,
//! the multiplicative-complexity floor for this decomposition. We
//! materialize **only the irreducible slots**:
//!
//! - **No sum-bit slots**. Each ADD's 32 sum bits expand into lin_funcs at
//!   the use site (`s[i] = X[i] ⊕ Y[i] ⊕ ⊕_{j<i} carry_aux[j]`).
//! - **Fused three-operand ADDs.** `a + b + mx` is one 61-slot gadget, not
//!   two chained 31-slot ripples: a carry-save layer witnesses the 31
//!   majorities, then one ripple adds the affine partial sum against the
//!   shifted majorities, whose bit 0 is zero and so needs no product. Worth
//!   one slot per three-operand ADD, and (the reason to do it) it halves the
//!   carry-prefix depth the `a` lane cascade carries forward, cutting matrix
//!   nonzeros 21.0M → 16.7M.
//! - **No `a_new` / `c_new` lin-id slots**. Lanes 0 to 3 ("a" positions) and
//!   8 to 11 ("c" positions) cascade: every read of these lanes inlines the
//!   full chain of carry_aux references from prior G's that touched the
//!   lane. After 7 rounds this chain is deep, but the slot count stays
//!   tight enough to fit `k_log = 14`.
//! - **`b_new` / `d_new` lin-id slots only**. Lanes 4 to 7 ("b" positions) and
//!   12 to 15 ("d" positions) are materialized as 32-bit lin-id slots per G,
//!   so the next G's read of these lanes is a single-slot lookup. This
//!   breaks the cascade for half the lanes; without it, `prove`-time
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
//!   z[0      ..    256)        = cv[0..8]   (8 × 32-bit words, free input)
//!   z[256    ..    512)        = out_lo[0..8] = state[0..8] ^ state[8..16]
//!   z[512]                     = 1                    (constant wire)
//!   z[513    ..    640)        = padding (forced to 0 by empty rows)
//!   z[640    ..  1,152)        = m[0..16]   (16 × 32-bit words, free)
//!   z[1,152  ..  1,184)        = counter_lo (free input)
//!   z[1,184  ..  1,216)        = counter_hi (free input)
//!   z[1,216  ..  1,248)        = block_len  (free input)
//!   z[1,248  ..  1,280)        = flags      (free input)
//!   z[1,280  .. 15,168)        = 56 G blocks × 248 bits each
//!   z[15,168 .. 15,424)        = out_hi[0..8] = state[8..16] ^ cv[0..8]
//!   z[15,424 .. 16,384)        = padding (forced to 0 by empty rows)
//! ```
//!
//! Per G block layout (248 bits):
//! ```text
//!   [0   .. 31)    majority products, ADD3_A1 = a + b + mx        (→ a_1)
//!   [31  .. 61)    ripple products,   ADD3_A1
//!   [61  .. 92)    carry_aux for ADD_C1      = c + d_1            (→ c_1)
//!   [92  .. 123)   majority products, ADD3_A2 = a_1 + b_1 + my    (→ a_new)
//!   [123 .. 153)   ripple products,   ADD3_A2
//!   [153 .. 184)   carry_aux for ADD_C2      = c_1 + d_2          (→ c_new)
//!   [184 .. 216)   b_new = rotr7(b_1 ^ c_2)                (lin-id)
//!   [216 .. 248)   d_new = rotr8(d_1 ^ a_2)                (lin-id)
//! ```
//!
//! `a_1`, `c_1`, `a_2 (a_new)`, `c_2 (c_new)`, `d_1`, `b_1`, `d_2` and both
//! fused ADDs' partial sums are NEVER materialized as slots: they're
//! lin_funcs evaluated at row-build time and threaded forward in the state
//! cascade.
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
//! - `cv`, `m`, `counter`, `block_len`, and `flags` are free input slots. The
//!   embedding protocol binds them to VM memory / bytecode with PCS openings.
//!
//! ## What this does NOT enforce
//!
//! - **Input binding**: all compression inputs are free witness bits. PCS-level
//!   openings at fixed indices pin them to claimed memory and bytecode values.

use crate::blake3_witness::{BitRecord, add_carry_parts, add3_fused_parts, or_bit_at, or_u32_at_bit, xor_dedup};
use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};
use crate::verifier;
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify};
use primitives::field::F192;
use primitives::multilinear::lagrange_weights_naive;
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one BLAKE3 compression occupies `2^K_LOG = 16,384` z slots.
pub const K_LOG: usize = 14;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim, must match [`crate::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

/// Number of BLAKE3 rounds.
pub const N_ROUNDS: usize = 7;
/// Number of G calls per round (4 column + 4 diagonal).
pub const N_G_PER_ROUND: usize = 8;
/// Total G calls per compression.
pub const N_G: usize = N_ROUNDS * N_G_PER_ROUND;
/// Bits per BLAKE3 word.
pub const WORD_BITS: usize = 32;

/// Carry_aux bits per 32-bit two-operand ADD (bit 0..30; bit 31 is the
/// discarded mod-2³² carry-out and isn't allocated).
pub const CARRY_BITS_PER_ADD: usize = WORD_BITS - 1; // 31
/// Ripple-layer product bits per fused three-operand ADD (bit 1..30): bit 0's
/// product is `p₀ · 0`, since the shifted majority word's bit 0 is zero.
pub const RIPPLE_BITS_PER_ADD3: usize = WORD_BITS - 2; // 30
/// Product slots per fused three-operand ADD: 31 majorities + 30 ripple.
pub const ADD3_BITS: usize = CARRY_BITS_PER_ADD + RIPPLE_BITS_PER_ADD3; // 61
/// Lin-id 32-bit words per G (b_new, d_new).
pub const LIN_WORDS_PER_G: usize = 2;
/// Bits per G block (no sum-bit slots, see module docs).
pub const G_STRIDE: usize = 2 * ADD3_BITS + 2 * CARRY_BITS_PER_ADD + LIN_WORDS_PER_G * WORD_BITS; // 248

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
pub const G_MSG_IDX: [[usize; 2]; N_G_PER_ROUND] =
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11], [12, 13], [14, 15]];

// ---------------------------------------------------------------------------
// Layout positions (bit indices into the per-block z slice of length K)
// ---------------------------------------------------------------------------

// **I/O-aligned layout** for the hash chain (forked from `blake3`): the input
// chaining value `cv` lives in aligned slot 0 and the output chaining value
// `out_lo` (= state[0..8] ^ state[8..16]) in aligned slot 1, each a clean
// 256-bit (`2^8`) window, so the chain shift argument folds them via a single
// tensor opening. cv/out_lo are *exactly* 256 bits, so the slots have NO
// interior padding. Everything else (const, m, counters, flags, G-blocks,
// out_hi) packs after the two slots. The re-layout is purely a change of these
// base offsets; all bit placement goes through the `*_bit` accessors below.
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
pub const OUT_HI_BASE: usize = GS_BASE + N_G * G_STRIDE; // 15,168
pub const USEFUL_BITS: usize = OUT_HI_BASE + 8 * WORD_BITS; // 15,424

// Sub-block offsets within one G's `G_STRIDE` slots. A fused ADD owns two
// consecutive runs (majorities then ripple); a two-operand ADD owns one.
const G_ADD3_A1: usize = 0; // a + b + mx  → a_1
const G_ADD_C1: usize = G_ADD3_A1 + ADD3_BITS; // c + d_1 → c_1
const G_ADD3_A2: usize = G_ADD_C1 + CARRY_BITS_PER_ADD; // a_1 + b_1 + my → a_new
const G_ADD_C2: usize = G_ADD3_A2 + ADD3_BITS; // c_1 + d_2 → c_new
const G_LIN_B_NEW: usize = G_ADD_C2 + CARRY_BITS_PER_ADD;
const G_LIN_D_NEW: usize = G_LIN_B_NEW + WORD_BITS;

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
/// Base slot of the sub-block at offset `off` (one of the `G_*` constants)
/// within G `g`'s block.
#[inline]
fn g_slot(g: usize, off: usize) -> usize {
    debug_assert!(g < N_G && off < G_STRIDE);
    GS_BASE + G_STRIDE * g + off
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
// Reference BLAKE3 compression, the witness oracle. Cross-checked against
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
    for g in 0..N_G_PER_ROUND {
        let [a, b, c, d] = G_LANES[g];
        let [mx, my] = G_MSG_IDX[g];
        g_fn(state, a, b, c, d, block[mx], block[my]);
    }
}

fn permute(m: &mut [u32; 16]) {
    let p = MSG_PERMUTATION.map(|i| m[i]);
    *m = p;
}

/// The 16-word state a compression starts from: the chaining value, the first
/// four IV words, and the four metadata words.
fn initial_state(cv: &[u32; 8], counter_lo: u32, counter_hi: u32, block_len: u32, flags: u32) -> [u32; 16] {
    let mut state = [0u32; 16];
    state[..8].copy_from_slice(cv);
    state[8..12].copy_from_slice(&BLAKE3_IV[..4]);
    state[12] = counter_lo;
    state[13] = counter_hi;
    state[14] = block_len;
    state[15] = flags;
    state
}

/// BLAKE3 compression function. Returns the full 16-word output state
/// (post-finalization XOR). For chaining, the new CV is `out[0..8]`.
pub fn blake3_compress(cv: &[u32; 8], block_words: &[u32; 16], counter: u64, block_len: u32, flags: u32) -> [u32; 16] {
    let counter_low = counter as u32;
    let counter_high = (counter >> 32) as u32;
    let mut state = initial_state(cv, counter_low, counter_high, block_len, flags);
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

/// `per_round_msg_idx()[r][g] = (mx_idx, my_idx)` for round `r`, G index `g`,
/// i.e. `PERM^r [G_MSG_IDX[g]]`.
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
// Lin_func cascade: per-bit lists of slot indices XOR'd to evaluate one bit.
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
    /// Construct from a 32-bit constant: bit `i` is `[Z_CONST]` if set,
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
    /// `rotr(n)`: pure index permutation, doesn't touch slot lists.
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
// ---------------------------------------------------------------------------

fn write_add3_fused_rows(
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

    // Constant z[0]: z[0]·z[0] = z[0]. Trivially satisfied for any boolean.
    a_rows[Z_CONST_POS] = vec![Z_CONST_POS];
    b_rows[Z_CONST_POS] = vec![Z_CONST_POS];

    // Free-input rows for cv, message, counter, block length, and flags
    // (unconstrained when the constant wire is 1). The embedding protocol
    // binds these aligned slots to memory / bytecode claims.
    let mut input_emit = |base: usize, len: usize| {
        for j in 0..len {
            let s = base + j;
            a_rows[s] = vec![s];
            b_rows[s] = vec![Z_CONST_POS];
        }
    };
    input_emit(CV_BASE, 8 * WORD_BITS);
    input_emit(M_BASE, 16 * WORD_BITS);
    input_emit(T_LO_BASE, 2 * WORD_BITS);
    input_emit(BLEN_BASE, WORD_BITS);
    input_emit(FLAGS_BASE, WORD_BITS);

    let msg_idx = per_round_msg_idx();
    let mut state: [Word; 16] = initial_lane_words();

    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let [mx_idx, my_idx] = msg_idx[r][g_in_round];

            // Snapshot the four input lanes: the G writes back into `state[la]`
            // .. `state[ld]` below, and every step reads the pre-G values.
            let a = state[la].clone();
            let b = state[lb].clone();
            let c = state[lc].clone();
            let d = state[ld].clone();
            let mx = Word::from_slot_base(m_bit(mx_idx, 0));
            let my = Word::from_slot_base(m_bit(my_idx, 0));

            // a_1 = a + b + mx   (fused; mx is the sparse operand, so it takes
            // the majority layer's doubled `z` position)
            let a_1 = write_add3_fused_rows(&mut a_rows, &mut b_rows, &a, &b, &mx, g_slot(g, G_ADD3_A1));
            // d_1 = rotr16(d ^ a_1)
            let d_1 = d.xor(&a_1).dedup().rotr(16);
            // c_1 = c + d_1
            let c_1 = write_add_carry_rows(&mut a_rows, &mut b_rows, &c, &d_1, g_slot(g, G_ADD_C1));
            // b_1 = rotr12(b ^ c_1)
            let b_1 = b.xor(&c_1).dedup().rotr(12);
            // a_2 = a_1 + b_1 + my   (fused; = a_new, cascades)
            let a_2 = write_add3_fused_rows(&mut a_rows, &mut b_rows, &a_1, &b_1, &my, g_slot(g, G_ADD3_A2));
            // d_2 = rotr8(d_1 ^ a_2)
            let d_2 = d_1.xor(&a_2).dedup().rotr(8);
            // c_2 = c_1 + d_2    (= c_new, cascades)
            let c_2 = write_add_carry_rows(&mut a_rows, &mut b_rows, &c_1, &d_2, g_slot(g, G_ADD_C2));
            // b_new = rotr7(b_1 ^ c_2)    (materialized lin-id)
            let b_new_word = b_1.xor(&c_2).dedup().rotr(7);
            for i in 0..WORD_BITS {
                let s = g_slot(g, G_LIN_B_NEW + i);
                a_rows[s] = b_new_word.bits[i].clone();
                b_rows[s] = vec![Z_CONST_POS];
            }
            // d_new = d_2                  (materialized lin-id)
            for i in 0..WORD_BITS {
                let s = g_slot(g, G_LIN_D_NEW + i);
                a_rows[s] = d_2.bits[i].clone();
                b_rows[s] = vec![Z_CONST_POS];
            }

            // Advance the symbolic state. `a_2` and `c_2` keep cascading;
            // `b_new` and `d_new` reset to single-slot lookups.
            state[la] = a_2;
            state[lb] = Word::from_slot_base(g_slot(g, G_LIN_B_NEW));
            state[lc] = c_2;
            state[ld] = Word::from_slot_base(g_slot(g, G_LIN_D_NEW));
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

// ---------------------------------------------------------------------------
// Circuit-walk evaluation (flock §Circuit walking)
//
// Evaluates the two bilinear forms
//
//     uᵀ A_0 w   and   uᵀ B_0 w
//
// for arbitrary row weights `u` and column weights `w` (length K each) by
// walking the UNSUBSTITUTED compression circuit forward: the same cascade
// `build_matrices` threads symbolically, evaluated over F192 values. A lane
// is a 32-vector of wire values; a committed slot contributes `w[slot]`, an
// intermediate wire the running linear combination. Row i's contribution
// `u[i]·⟨A_i, w⟩` / `u[i]·⟨B_i, w⟩` is accumulated exactly where
// `build_matrices` would emit that row, with `⟨row, w⟩` read off the threaded
// wire values. Cost: O(circuit) field ops (~50K muls), never the ~16.7M
// substituted nonzeros, and the matrices need not be materialized at all.
// This is what lets a verifier evaluate the matrix MLEs directly instead of
// paying the sparse-matrix cost (or deferring the claim).
// ---------------------------------------------------------------------------

/// One lane's wire values: bit `i` of the word, as the F192 combination
/// `⟨lin_func_i, w⟩`.
type WireWord = [F192; WORD_BITS];

#[inline]
fn wire_from_slot_base(w: &[F192], base: usize) -> WireWord {
    std::array::from_fn(|i| w[base + i])
}

/// Constant word: a set bit is the `[Z_CONST]` lin_func, a clear bit empty.
#[inline]
fn wire_from_const(w: &[F192], val: u32) -> WireWord {
    std::array::from_fn(|i| {
        if (val >> i) & 1 == 1 {
            w[Z_CONST_POS]
        } else {
            F192::ZERO
        }
    })
}

#[inline]
fn wire_xor(x: &WireWord, y: &WireWord) -> WireWord {
    std::array::from_fn(|i| x[i] + y[i])
}

#[inline]
fn wire_rotr(x: &WireWord, n: usize) -> WireWord {
    std::array::from_fn(|i| x[(i + n) % WORD_BITS])
}

/// Pair of accumulators for the A-side and B-side bilinear forms, plus the
/// running sum of `u` over rows whose B-side is the single `[Z_CONST]` entry
/// (lin-id / free-input rows), factored so those rows cost one B-side
/// F-addition instead of a multiplication each.
struct WalkAcc {
    a: F192,
    b: F192,
    /// Σ u[row] over rows with `B_row = [Z_CONST]`; folded in once at the end
    /// as `b += w[Z_CONST_POS] · u_bconst`.
    u_bconst: F192,
}

/// Walk one 32-bit ADD (mirror of `write_add_carry_rows` + `Word::add_sum`):
/// accumulate the 31 carry rows into `acc` and return the sum-bit wires.
///
///   carry row cb+i:  A = X[i] ⊕ cin[i],  B = Y[i] ⊕ cin[i]
///   sum[i]         = X[i] ⊕ Y[i] ⊕ cin[i]
///
/// with `cin[i] = ⊕_{j<i} carry_aux[cb+j]`, a running prefix of `w` reads.
fn walk_add(acc: &mut WalkAcc, u: &[F192], w: &[F192], x: &WireWord, y: &WireWord, carry_base: usize) -> WireWord {
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
fn walk_add3_fused(
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

/// Walk 32 consecutive `lin_func · 1` rows (lin-id / out_lo / out_hi):
/// row base+i has `A = <wire bit i>`, `B = [Z_CONST]`.
fn walk_lin_rows(acc: &mut WalkAcc, u: &[F192], vals: &WireWord, base: usize) {
    for i in 0..WORD_BITS {
        acc.a += u[base + i] * vals[i];
        acc.u_bconst += u[base + i];
    }
}

/// `(uᵀ A_0 w, uᵀ B_0 w)` by the forward circuit walk, over the exact matrices
/// `build_matrices` emits, never materialized.
pub fn bilinear_walk_pair(u: &[F192], w: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(w.len(), K);
    let wc = w[Z_CONST_POS];
    let mut acc = WalkAcc {
        a: F192::ZERO,
        b: F192::ZERO,
        u_bconst: F192::ZERO,
    };
    // Σ u[row] over rows with A = B = [Z_CONST] (just the constant row now
    // that every compression input is a free row): folded in at the end on
    // both sides.
    let u_abconst = u[Z_CONST_POS];

    // Free-input rows for the 512 message bits: A = [slot], B = [Z_CONST].
    for j in 0..16 * WORD_BITS {
        let s = M_BASE + j;
        acc.a += u[s] * w[s];
        acc.u_bconst += u[s];
    }

    // Free-input rows for the 256 chaining-value bits and the 128 metadata
    // bits (counter lo/hi, block_len, flags): A = [slot], B = [Z_CONST], the
    // same shape as the message bits (the generalized circuit no longer pins
    // them to constants; the embedding protocol binds them instead).
    for j in 0..8 * WORD_BITS {
        let s = CV_BASE + j;
        acc.a += u[s] * w[s];
        acc.u_bconst += u[s];
    }
    for base in [T_LO_BASE, T_HI_BASE, BLEN_BASE, FLAGS_BASE] {
        for j in 0..WORD_BITS {
            let s = base + j;
            acc.a += u[s] * w[s];
            acc.u_bconst += u[s];
        }
    }

    // The G cascade, over wire values (mirrors `initial_lane_words`).
    let msg_idx = per_round_msg_idx();
    let mut state: [WireWord; 16] = std::array::from_fn(|_| [F192::ZERO; WORD_BITS]);
    for wd in 0..8 {
        state[wd] = wire_from_slot_base(w, cv_bit(wd, 0));
    }
    for i in 0..4 {
        state[8 + i] = wire_from_const(w, BLAKE3_IV[i]);
    }
    state[12] = wire_from_slot_base(w, T_LO_BASE);
    state[13] = wire_from_slot_base(w, T_HI_BASE);
    state[14] = wire_from_slot_base(w, BLEN_BASE);
    state[15] = wire_from_slot_base(w, FLAGS_BASE);

    for r in 0..N_ROUNDS {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let [mx_idx, my_idx] = msg_idx[r][g_in_round];
            let (a, b, c, d) = (state[la], state[lb], state[lc], state[ld]);
            let mx = wire_from_slot_base(w, m_bit(mx_idx, 0));
            let my = wire_from_slot_base(w, m_bit(my_idx, 0));

            let a_1 = walk_add3_fused(&mut acc, u, w, &a, &b, &mx, g_slot(g, G_ADD3_A1));
            let d_1 = wire_rotr(&wire_xor(&d, &a_1), 16);
            let c_1 = walk_add(&mut acc, u, w, &c, &d_1, g_slot(g, G_ADD_C1));
            let b_1 = wire_rotr(&wire_xor(&b, &c_1), 12);
            let a_2 = walk_add3_fused(&mut acc, u, w, &a_1, &b_1, &my, g_slot(g, G_ADD3_A2));
            let d_2 = wire_rotr(&wire_xor(&d_1, &a_2), 8);
            let c_2 = walk_add(&mut acc, u, w, &c_1, &d_2, g_slot(g, G_ADD_C2));
            let b_new = wire_rotr(&wire_xor(&b_1, &c_2), 7);
            walk_lin_rows(&mut acc, u, &b_new, g_slot(g, G_LIN_B_NEW));
            walk_lin_rows(&mut acc, u, &d_2, g_slot(g, G_LIN_D_NEW));

            state[la] = a_2;
            state[lb] = wire_from_slot_base(w, g_slot(g, G_LIN_B_NEW));
            state[lc] = c_2;
            state[ld] = wire_from_slot_base(w, g_slot(g, G_LIN_D_NEW));
        }
    }

    // Finalization rows: out_lo[w] = state[w] ⊕ state[w+8],
    // out_hi[w] = state[w+8] ⊕ cv[w]. Padding rows are empty: no contribution.
    for wd in 0..8 {
        let lo = wire_xor(&state[wd], &state[wd + 8]);
        walk_lin_rows(&mut acc, u, &lo, out_lo_bit(wd, 0));
        let cv_w = wire_from_slot_base(w, cv_bit(wd, 0));
        let hi = wire_xor(&state[wd + 8], &cv_w);
        walk_lin_rows(&mut acc, u, &hi, out_hi_bit(wd, 0));
    }

    // Fold in the factored constant-B and constant-A/B row sums.
    (acc.a + wc * u_abconst, acc.b + wc * (acc.u_bconst + u_abconst))
}

/// `α·(uᵀ A_0 w) + (uᵀ B_0 w)`, the α-batched form lincheck's verifier
/// consumes, by one circuit walk.
pub fn bilinear_walk(alpha: F192, u: &[F192], w: &[F192]) -> F192 {
    let (va, vb) = bilinear_walk_pair(u, w);
    alpha * va + vb
}

/// Walk-capable [`crate::lincheck::LincheckCircuit`] over the BLAKE3 R1CS:
/// `bilinear_form` answers lincheck's verifier in O(circuit) field ops via
/// [`bilinear_walk`], so `lincheck::verify` never materializes the
/// ~16.7M-nonzero substituted matrices' column marginal. The prover-side
/// `fold_alpha_batched` delegates to the (lazily built) CSC fold; the
/// verifier's fast path never calls it.
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

/// [`BlockR1cs::family_digest`] of this module's circuit, baked as a constant:
/// recomputing it means building and hashing ~16.7M matrix entries (~300 ms),
/// which embedding protocols would otherwise pay inside their first prove.
/// The `family_digest_matches_baked` test recomputes and compares: a circuit
/// change fails it until this constant is updated alongside.
pub const FAMILY_DIGEST: [u8; 32] = [
    0xbc, 0x44, 0xee, 0x31, 0xd8, 0x63, 0x94, 0xb8, 0xe1, 0x25, 0x6f, 0x37, 0xcf, 0x3b, 0xf8, 0x72, 0x02, 0x12, 0xdd,
    0x97, 0xa6, 0x8d, 0x1e, 0x5f, 0x35, 0x7a, 0x99, 0x2c, 0x46, 0xac, 0xf1, 0xa7,
];

/// Build a [`BlockR1cs`] batching `2^n_blocks_log` independent BLAKE3
/// compressions. `n_blocks_log ≥ 3` is required (lincheck needs `n_outer ≥ 8`).
pub fn build_block_r1cs(n_blocks_log: usize) -> BlockR1cs {
    assert!(n_blocks_log >= 3, "lincheck needs n_outer ≥ 8, pick n_blocks_log ≥ 3");
    // Clone the cached matrices (~ms) instead of re-running the symbolic
    // builder (~200 ms): setups, family digests and const-pin lookups all
    // share one build per process.
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
        // Constant-wire pin (see lincheck's `LincheckCircuit::const_pin_col`): forces z[Z_CONST_POS] = 1
        // in every block. Requires padding blocks filled with valid compressions.
        const_pin: Some(Z_CONST_POS),
        csc_cache: std::sync::OnceLock::new(),
    }
}

// ---------------------------------------------------------------------------
// Witness generation (boolean)
// ---------------------------------------------------------------------------

/// Minimum `n_blocks_log` needed to prove `n_blocks` BLAKE3 compressions,
/// subject to the lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    let n = n_blocks.max(8);
    n.next_power_of_two().trailing_zeros() as usize
}

/// One BLAKE3 compression input: `(cv, m, counter, block_len, flags)`.
pub type Compression = ([u32; 8], [u32; 16], u64, u32, u32);

/// The default one-block hash length: one full 64-byte block.
pub const PINNED_BLOCK_LEN: u32 = 64;
/// The default flags: `CHUNK_START(1) | CHUNK_END(2) | ROOT(8)`, the single
/// 64-byte root block, under which the compression output equals
/// `blake3::hash` of the input.
pub const PINNED_FLAGS: u32 = (1 << 0) | (1 << 1) | (1 << 3);

/// A convenient one-block standard hash [`Compression`] of `m`
/// (`cv = IV`, `counter = 0`, [`PINNED_BLOCK_LEN`], [`PINNED_FLAGS`]). The
/// circuit itself accepts arbitrary chaining values and metadata.
pub fn pinned_compression(m: [u32; 16]) -> Compression {
    (BLAKE3_IV, m, 0, PINNED_BLOCK_LEN, PINNED_FLAGS)
}

/// The padding instance: a default compression of the all-zero message,
/// i.e. `blake3(0^64)`. Fills unused trailing slots so every batched block
/// (padding included) is a valid instance with constant wire 1, as the
/// lincheck const-wire pin requires.
pub fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
}

/// Unpack the first `n_bits` logical bits of a packed witness: bit `i` is bit
/// `i % 64` of word `i / 64`.
#[cfg(test)]
fn unpack_bits(z: &[u64], n_bits: usize) -> Vec<bool> {
    (0..n_bits).map(|i| (z[i / 64] >> (i % 64)) & 1 == 1).collect()
}

/// The boolean witness vector for `blocks.len()` independent BLAKE3
/// compressions, padded to `2^n_blocks_log` slots, unpacked from the
/// production generator so the R1CS tests check the witness that is actually
/// proved.
#[cfg(test)]
fn generate_witness(blocks: &[Compression], n_blocks_log: usize) -> Vec<bool> {
    let z = generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log).0;
    unpack_bits(&z, (1usize << n_blocks_log) * K)
}

// ---------------------------------------------------------------------------
// Fast witness generation with (a, b, c): emits the R1CS row-witnesses
// directly from the BLAKE3 computation, as bit-packed u64 words. Skips the
// `apply_block_diag_packed` pass downstream.
//
// Row-witness semantics (matching `build_matrices`):
// - Constant z[0]:       (z, a, b, c) = (1, 1, 1, 1).
// - Free-input slot (m): (z, a, b, c) = (val, val, 1, val).
// - Pinned-const slot:   (z, a, b, c) = (val, val, val, val), val ∈ {0, 1}.
// - Lin-id slot:         (z, a, b, c) = (lin_val, lin_val, 1, lin_val).
// - Carry_aux row i:     (z, a, b, c) = (carry_aux, X⊕cin, Y⊕cin, carry_aux).
// - Fused majority row:  (z, a, b, c) = (maj_aux, X⊕Z, Y⊕Z, maj_aux).
// - Fused ripple row:    (z, a, b, c) = (rip_aux, p⊕cin, q⊕cin, rip_aux),
//                        all three pre-shifted down one bit (bit 0 has no row).
// - Padding row:         all zero (already zero on entry).
// ---------------------------------------------------------------------------

// Record-relative positions, mirroring the `G_*` sub-block offsets. A fused
// ADD needs two: its majority run and its ripple run.
const REC_MAJ_A1: usize = G_ADD3_A1;
const REC_RIP_A1: usize = G_ADD3_A1 + CARRY_BITS_PER_ADD;
const REC_C1: usize = G_ADD_C1;
const REC_MAJ_A2: usize = G_ADD3_A2;
const REC_RIP_A2: usize = G_ADD3_A2 + CARRY_BITS_PER_ADD;
const REC_C2: usize = G_ADD_C2;
const REC_LIN0: usize = G_LIN_B_NEW;
const REC_LIN1: usize = G_LIN_D_NEW;

/// Write a 32-bit lin-id (or input) slot: (z, a) = val, b = all-ones.
/// **c is not written**: since `C = I`, `c == z` byte-for-byte.
#[inline]
fn write_lin_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, 0xFFFF_FFFF);
}

/// Build the (z, a, b) blocks for ONE compression instance, into this
/// instance's `K / 64` words of each packed table. Buffers must be zero on
/// entry.
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

    // Free-input rows.
    let counter_lo = counter as u32;
    let counter_hi = (counter >> 32) as u32;
    for w in 0..8 {
        write_lin_word_ab_packed(cv_bit(w, 0), cv[w], z, a, b);
    }
    for i in 0..16 {
        write_lin_word_ab_packed(m_bit(i, 0), m[i], z, a, b);
    }
    write_lin_word_ab_packed(T_LO_BASE, counter_lo, z, a, b);
    write_lin_word_ab_packed(T_HI_BASE, counter_hi, z, a, b);
    write_lin_word_ab_packed(BLEN_BASE, block_len, z, a, b);
    write_lin_word_ab_packed(FLAGS_BASE, flags, z, a, b);

    // BLAKE3 state evolution.
    let mut state = initial_state(cv, counter_lo, counter_hi, block_len, flags);
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

/// **The fast path.** Produces `(z, a, b)` directly as bit-packed `u64` words
/// (no bool intermediates, no `pack_witness` step, no
/// `apply_block_diag_packed`) and, in the same parallel pass, the lincheck
/// byte-stripe layout.
///
/// Returns `(z, a, b, z_lincheck)`; **no c buffer**: since `C = I`
/// (circuit-shape R1CS), `c == z` word-for-word, so callers pass `z` as the
/// c-side input to zerocheck.
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
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
    // Constant-wire pin (see lincheck's `LincheckCircuit::const_pin_col`): fill padding blocks with the
    // pinned compression of the all-zero message so the constant cell is 1 in
    // every block. (The chain forbids padding, so this only affects the
    // standalone batch setup.)
    let padding = padding_block();
    crate::blake3_witness::drive_witness_packed_and_lincheck(
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

/// The packed witness as the byte string the zerocheck kernels read. Bit `i`
/// of the witness is bit `i % 8` of byte `i / 8`, which is the in-memory image
/// of the `u64` words on a little-endian target.
fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s
    // alignment divides `u64`'s, so the words are a valid `8 · len` byte slice.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

// ---------------------------------------------------------------------------
// Convenience API: Blake3Setup
// ---------------------------------------------------------------------------

/// Bundles the monolithic BLAKE3 compression R1CS for the smallest supported
/// power-of-two shape that can hold `n_blocks` compressions.
#[derive(Clone, Debug)]
pub struct Blake3Setup {
    pub r1cs: BlockR1cs,
}

impl Blake3Setup {
    /// Build a setup for `n_blocks` BLAKE3 compressions.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        let r1cs = build_block_r1cs(n_log);
        // Warm the CSC fold circuit here so its one-time build (a pass over
        // ~16.7M nonzeros) stays out of the first prove/verify. The prove-cycle
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

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn family_digest_matches_baked() {
        assert_eq!(
            build_block_r1cs(3).family_digest(),
            FAMILY_DIGEST,
            "circuit family changed - update FAMILY_DIGEST"
        );
    }

    /// The circuit walk computes the same bilinear forms as the materialized
    /// matrices, for fully random (unstructured) row/column weights: any
    /// missing, extra, or misplaced row contribution would break equality.
    #[test]
    fn bilinear_walk_matches_matrices() {
        let (ma, mb) = matrices();
        let mut rng = Rng::new(0xC12C);
        for trial in 0..3 {
            let alpha = rng.ext();
            let u: Vec<F192> = rng.ext_vec(K);
            let w: Vec<F192> = rng.ext_vec(K);
            let contract = |m: &SparseBinaryMatrix| -> F192 {
                m.rows
                    .iter()
                    .enumerate()
                    .map(|(i, row)| u[i] * row.iter().map(|&j| w[j]).fold(F192::ZERO, |acc, x| acc + x))
                    .fold(F192::ZERO, |acc, x| acc + x)
            };
            let (direct_a, direct_b) = (contract(ma), contract(mb));
            let (walk_a, walk_b) = bilinear_walk_pair(&u, &w);
            assert_eq!(walk_a, direct_a, "A-side, trial {trial}");
            assert_eq!(walk_b, direct_b, "B-side, trial {trial}");
            assert_eq!(
                bilinear_walk(alpha, &u, &w),
                alpha * direct_a + direct_b,
                "alpha-batched, trial {trial}"
            );
        }
    }

    /// BLAKE3 chunk flags (subset).
    const CHUNK_START: u32 = 1 << 0;
    const CHUNK_END: u32 = 1 << 1;
    const ROOT: u32 = 1 << 3;

    #[test]
    fn layout_constants() {
        assert_eq!(G_STRIDE, 248);
        assert_eq!(N_G, 56);
        assert_eq!(OUT_HI_BASE, 15_168);
        assert_eq!(USEFUL_BITS, 15_424);
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(USEFUL_BITS <= K);
            // The per-G record is composed in a `BitRecord<4>` (256 bits),
            // whose last sub-block must start within the record's four words.
            assert!(G_LIN_D_NEW < 4 * 64 && G_STRIDE <= 4 * 64);
        }
    }

    /// The constrained rows tile the layout exactly: every slot a region
    /// claims is the output of one non-degenerate row, and every slot outside
    /// is padding.
    ///
    /// This is the invariant the per-G sub-block offsets have to preserve.
    /// They are computed by summing widths, so a wrong width makes two
    /// sub-blocks overlap; the second `a_rows[s] = ...` would then overwrite
    /// the first and leave one product slot unconstrained, which a prover
    /// could set freely. The overwritten row is still non-empty, so only
    /// checking the whole tiling catches it.
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
        claim(CV_BASE, 8 * WORD_BITS);
        claim(OUT_LO_BASE, 8 * WORD_BITS);
        claim(Z_CONST_POS, 1);
        claim(M_BASE, 16 * WORD_BITS);
        claim(T_LO_BASE, 4 * WORD_BITS);
        claim(GS_BASE, N_G * G_STRIDE);
        claim(OUT_HI_BASE, 8 * WORD_BITS);
        for s in 0..K {
            let constrained = !a_0.rows[s].is_empty() || !b_0.rows[s].is_empty();
            assert_eq!(
                constrained, expected[s],
                "slot {s} constrained={constrained}, want {}",
                expected[s]
            );
            assert!(
                !(constrained && s >= USEFUL_BITS),
                "slot {s} is constrained past USEFUL_BITS"
            );
        }
    }

    /// Reference compression matches the `blake3` crate for empty input
    /// (a single root-block, single-chunk, ROOT-flagged compression).
    #[test]
    fn compress_matches_blake3_crate_empty() {
        let state = blake3_compress(&BLAKE3_IV, &[0u32; 16], 0, 0, CHUNK_START | CHUNK_END | ROOT);
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
        let block = pinned_compression(m);
        let (cv, m, counter, block_len, flags) = block;
        // The fused generator's floor is 8 instances; only the first is read.
        let z = generate_witness(&[block], 3);
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
                    let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                    (
                        cv,
                        m,
                        rng.next_u32() as u64 | ((rng.next_u32() as u64) << 32),
                        rng.next_u32() % 65,
                        rng.next_u32(),
                    )
                })
                .collect();
            let z = generate_witness(&blocks, n_log);
            assert_eq!(z.len(), r1cs.n());
            assert!(r1cs.satisfies(&z), "witness for {n_blocks} compressions fails R1CS");
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
        // Flip a product bit in each layer of G #10's second fused ADD
        // (middle of round 1), one at a time.
        for off in [G_ADD3_A2 + 5, G_ADD3_A2 + CARRY_BITS_PER_ADD + 5] {
            z[g_slot(10, off)] ^= true;
            assert!(!r1cs.satisfies(&z), "tampered product bit at {off} should violate R1CS");
            z[g_slot(10, off)] ^= true;
        }
        assert!(r1cs.satisfies(&z), "restoring both bits should re-satisfy");
    }

    /// The fused generator's lincheck stripe is byte-identical to the direct
    /// repacking of its own `z`, over shapes with partial groups and padding
    /// slots.
    #[test]
    fn fused_lincheck_matches_separate() {
        use crate::lincheck::pack_z_lincheck_from_packed;
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

            let (z, _a, _b, lincheck_new) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
            assert_eq!(
                pack_z_lincheck_from_packed(&z, r1cs.m, r1cs.k_log),
                lincheck_new,
                "lincheck stripe mismatch at n_blocks={n_blocks}"
            );
        }
    }

    #[test]
    fn setup_sizes_correctly() {
        for &(n_blocks, expected_n_log) in &[(1usize, 3), (8, 3), (9, 4), (16, 4), (17, 5), (1000, 10)] {
            let setup = Blake3Setup::new(n_blocks);
            assert_eq!(setup.n_blocks_log(), expected_n_log, "n_blocks={n_blocks}");
            assert_eq!(setup.m(), K_LOG + expected_n_log);
            assert!(setup.n_block_slots() >= n_blocks);
        }
    }

    /// Constant-wire pin (see lincheck's `LincheckCircuit::const_pin_col`): the all-zero witness
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
        let (mut z, mut a, mut b, mut zlc) = generate_witness_with_ab_packed_and_lincheck(&[], setup.n_blocks_log());
        z.fill(0);
        a.fill(0);
        b.fill(0);
        zlc.fill(0);

        // Prover side: the reduction happily runs on the zero witness.
        let padding = crate::zerocheck::PaddingSpec {
            k_log: r1cs.k_log,
            useful_bits_per_block: r1cs.useful_bits,
        };
        let mut ps = pcs::ProverState::new(b"const-pin-poc", &[]);
        let (zc_claim, _s_hat_v_c) = crate::zerocheck::prove_packed_padded_capture_s_hat_v_c(
            packed_bytes(&a),
            packed_bytes(&b),
            packed_bytes(&z), // C = I, so c == z
            r1cs.m,
            &padding,
            &mut ps,
        );
        let x_ab = x_ab_of(&zc_claim, inner_rest_len);
        let _ = crate::lincheck::prove_padded_capture_s_hat_v(
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
        let mut vs = pcs::VerifierState::new(b"const-pin-poc", &proof_t, &[]);
        let zc = crate::zerocheck::verify(r1cs.m, &mut vs).expect("zerocheck accepts the all-zero witness");
        let x_ab_v = x_ab_of(&zc, inner_rest_len);
        let res = crate::lincheck::verify(
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
            matches!(res, Err(crate::lincheck::VerifyError::ConsistencyFailed { .. })),
            "all-zero witness must be rejected by the constant-wire pin; got {res:?}"
        );
    }
}

// The zerocheck, lincheck, and ring-switch scalars use the shared transcript;
// the caller carries the WHIR opening.

/// One claim on the committed packed BLAKE3 witness `q_flock`, as left by the
/// Flock reduction and handed to the PCS. `claim` is the `ẑ(point) = value`
/// evaluation the PCS must discharge; `s_hat_v` is the prover-only ring-switch
/// tensor weight the packed open consumes (`None` when `k_log < LOG_PACKING`,
/// and unused on the verifier side, which recovers it from `proof.open`).
#[derive(Clone, Debug)]
pub struct WitnessClaim {
    pub claim: crate::proof::ZClaim,
    pub s_hat_v: Option<Vec<F192>>,
}

/// The two claims on the committed witness `q_flock` left by the Flock BLAKE3
/// zerocheck + lincheck reduction, for the PCS to discharge:
/// - `ab`: the `A∘B` side, from lincheck.
/// - `c` : the `C` side, from zerocheck (`C = I`, so a direct z-claim).
///
/// This is the clean seam between Flock's reduction and the PCS: the reduction
/// produces these; the PCS opens them (see [`Blake3Setup::prove_reduction`]).
#[derive(Clone, Debug)]
pub struct PackedWitnessClaims {
    pub ab: WitnessClaim,
    pub c: WitnessClaim,
}

/// The variable count (`log2` length) of the committed `q_flock` column for
/// `n_blocks` executed compressions: `K_LOG + min_n_blocks_log − LOG_PACKING`.
/// Always at least one instance: `n_blocks = 0` still commits one padding
/// instance, keeping the proof shape uniform.
pub fn qflock_kappa(n_blocks: usize) -> usize {
    K_LOG + min_n_blocks_log(n_blocks.max(1)) - LOG_PACKING
}

/// One reduction claim as a tower [`RingSwitchClaim`]: the quirky point splits
/// at the packing boundary. Its univariate-skip coordinate
/// `z_skip` covers exactly the `k_skip = LOG_PACKING = 6` packed variables, so
/// the packing prefix is the 64 φ8-Lagrange weights at `z_skip`, and the WHOLE
/// multilinear tail `x_inner_rest ++ x_outer` is the suffix point (`q_flock`
/// has `2^qflock_vars` words, and no coordinate is split off into the prefix).
///
/// `captured` is the prover-side precomputed `s_hat_v`. The reduction captures
/// the bit-slice MLEs w.r.t. its OWN 128-bit packing, whose prefix absorbs
/// `z_skip` AND the first inner-rest coordinate `c`; the 64-bit packing here
/// keeps `c` in the suffix. The 64-wide values recombine linearly: 64-word
/// `y = 2y' + b` is the b-half of 128-word `y'`, and bit `i` of that half is
/// bit `i + 64b` of the 128-word, so `s64[i] = (1+c)·s128[i] + c·s128[i+64]`.
/// Lincheck already captures the 64 slices the ring switch expects; zerocheck's
/// fused kernel captures two 64-slice banks around the first suffix coordinate,
/// and that coordinate is folded here without rescanning `q_flock`.
fn ring_claim(z: &crate::proof::ZClaim, captured: Option<&[F192]>, qflock_vars: usize) -> RingSwitchClaim {
    let mut suffix_point = z.point.x_inner_rest.clone();
    suffix_point.extend_from_slice(&z.point.x_outer);
    assert_eq!(
        suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );

    let s_hat_v = captured.and_then(|s| match s.len() {
        PACKING_WIDTH => Some(s.to_vec()),
        n if n == 2 * PACKING_WIDTH && !z.point.x_inner_rest.is_empty() => {
            let c = z.point.x_inner_rest[0];
            Some(
                (0..PACKING_WIDTH)
                    .map(|i| (F192::ONE + c) * s[i] + c * s[i + PACKING_WIDTH])
                    .collect(),
            )
        }
        _ => None,
    });

    RingSwitchClaim {
        prefix_weights: lagrange_weights_naive(LOG_PACKING, z.point.z_skip),
        suffix_point,
        value: z.value,
        s_hat_v,
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
        prebound: 1,
        claims: vec![
            ring_claim(&reduced.ab.claim, reduced.ab.s_hat_v.as_deref(), qflock_vars),
            ring_claim(&reduced.c.claim, reduced.c.s_hat_v.as_deref(), qflock_vars),
        ],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered
/// `(ab, c)` claims as a [`RingSwitchVerify`], the same statement data. The
/// transmitted opening travels separately.
pub fn ring_switch_verify(
    n_blocks: usize,
    offset: usize,
    ab: &crate::proof::ZClaim,
    c: &crate::proof::ZClaim,
    ab_s_hat_v: &[F192],
) -> RingSwitchVerify {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchVerify {
        offset,
        qflock_vars,
        reconstructed: vec![ab_s_hat_v.to_vec()],
        claims: vec![ring_claim(ab, None, qflock_vars), ring_claim(c, None, qflock_vars)],
    }
}

/// Everything [`Blake3Setup::verify_reduction`] recovers: the two `(ab, c)`
/// z-claims for the PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub ab: crate::proof::ZClaim,
    pub c: crate::proof::ZClaim,
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

/// The `(ab, c)` z-claims the reduction leaves for the PCS: `ab` at lincheck's
/// output point, `c` at the zerocheck's own (`C = I`, so the c-claim is already
/// a z-claim). Prover and verifier must derive them identically, so they share
/// this one derivation.
fn reduction_claims(
    zc: &crate::zerocheck::ZerocheckClaim,
    lc: &crate::lincheck::LincheckClaim,
    x_outer: &[F192],
    inner_rest_len: usize,
) -> (crate::proof::ZClaim, crate::proof::ZClaim) {
    let ab = crate::proof::ZClaim {
        point: crate::lincheck::QuirkyPoint {
            z_skip: lc.r_inner_skip,
            x_inner_rest: lc.r_inner_rest.clone(),
            x_outer: x_outer.to_vec(),
        },
        value: lc.w,
    };
    let c = crate::proof::ZClaim {
        point: crate::lincheck::QuirkyPoint {
            z_skip: zc.z,
            x_inner_rest: zc.r_rest[..inner_rest_len].to_vec(),
            x_outer: zc.r_rest[inner_rest_len..].to_vec(),
        },
        value: zc.c_eval,
    };
    (ab, c)
}

impl Blake3Setup {
    /// **Flock reduction (prover).** Run the BLAKE3 zerocheck and lincheck on
    /// the shared transcript, reducing R1CS validity of `blocks` to two
    /// evaluation claims on the committed packed witness `q_flock`. (The
    /// statement is already transcript-bound: the embedding protocol seeds
    /// with the circuit family digest and announces the count.) Returns:
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
        // transcript with the circuit-FAMILY digest and binds the instance
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

        let (ab, c) = reduction_claims(&zc_claim, &lc_claim, &x_ab.x_outer, inner_rest_len);
        let s_hat_v_ab = (self.r1cs.k_log >= LOG_PACKING).then_some(lc_claim.s_hat_v);

        let reduced = PackedWitnessClaims {
            ab: WitnessClaim {
                claim: ab,
                s_hat_v: s_hat_v_ab,
            },
            c: WitnessClaim {
                claim: c,
                s_hat_v: Some(s_hat_v_c),
            },
        };
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

    /// **Flock reduction (verifier).** Replay the BLAKE3 zerocheck and
    /// lincheck straight off the shared transcript stream, recovering the two
    /// `(ab, c)` evaluation claims on the committed witness `q_flock`. Mirror of
    /// [`Self::prove_reduction`]; the PCS then discharges the returned claims.
    pub fn verify_reduction(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (family digest) + announced count + commitment root.

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
            vs,
        )
        .map_err(verifier::VerifyError::Lincheck)?;

        let (ab, c) = reduction_claims(&zc_claim, &lc_claim, &x_ab.x_outer, inner_rest_len);
        Ok(ReductionReplay {
            ab,
            c,
            zc_claim,
            lc_claim,
        })
    }
}
