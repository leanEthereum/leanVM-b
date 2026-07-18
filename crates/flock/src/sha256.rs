//! **SHA-256** compression-function R1CS-over-GF(2) for the VM's fixed-IV,
//! single-block `64 bytes -> 32 bytes` primitive. This is one compression with
//! feed-forward, without SHA padding or a length block. `H_in` is pinned to the
//! SHA-256 IV; the raw message and digest bytes occupy aligned public slots.
//!
//! ## Bit layout (single instance)
//!
//! ```text
//! z[0..256]         H_in        — 8 words × 32 bits  (slot 0, byte 0)
//! z[256..512]       H_out       — 8 words × 32 bits  (slot 1, byte 32)
//! z[512..1024]      M_in        — 16 words × 32 bits (raw input bytes)
//! z[1024..3072]     ch_and      — 64 rounds × 32 bits (AND outputs)
//! z[3072..5120]     maj_and     — 64 rounds × 32 bits (AND outputs)
//! z[5120..19008]    round carry-aux — 64 rounds × 7 adds × 31 carries
//! z[19008..20544]   W[t]        — 48 schedule final sums (sched_2)
//! z[20544..25008]   sched carries — 48 × 3 × 31
//! z[25008..27056]   T1[r]       — 64 round final T1 sums
//! z[27056..29104]   E_NEW[r]    — 64 round new-e sums
//! z[29104..31152]   A_NEW[r]    — 64 round new-a sums
//! z[31152..31400]   output carries — 8 × 31
//! z[31400]          Z_CONST (= 1)
//! z[31401..32768]   padding (forced to 0)
//! ```
//!
//! All bit placement goes through the `*_bit` accessors below — flipping the
//! base offsets is the only change required for the R1CS construction.
//!
//! ## Inlined adders
//!
//! Per 32-bit add, only the 31 `carry_aux` slots are allocated; the 32 sum
//! bits are symbolic XOR expressions inlined into the next consumer's row.
//! This keeps the witness compact (~31,401 useful rows).
//!
//! ## Sum slots that *are* materialized
//!
//! - `W[t]` for `t ∈ 16..64` — referenced once each by `T1_3`, but the
//!   schedule chain is 3 deep and `W[t]` itself depends on prior `W`'s
//!   (cascades for `t ≥ 32`). Slotting breaks the cascade.
//! - `T1[r]` — referenced twice (E_NEW and A_NEW), so slotting saves
//!   duplicate inlining.
//! - `E_NEW[r]`, `A_NEW[r]` — feed downstream rounds (4 uses each via
//!   register shift); without slots the state would cascade end-to-end and
//!   each Ch / Maj AND row would blow up to thousands of terms.
//! - `H_out[w]` — the public output of the compression.

use crate::binary_witness::{BitRecord, add_carry_parts, or_bit_at, or_u32_at_bit};
use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};
use crate::verifier;
use primitives::field::F192;

// ───────────────────────────────────────────────────────────────────────────
// Compile-time slot layout
// ───────────────────────────────────────────────────────────────────────────

/// Inner-dimension log: `K = 2^15 = 32,768` rows per block.
pub const K_LOG: usize = 15;
pub const K: usize = 1 << K_LOG;
/// Univariate-skip width.
pub const K_SKIP: usize = 6;

pub const N_ROUNDS: usize = 64;
pub const N_SCHED: usize = 48;
pub const WORD_BITS: usize = 32;
pub const H_WORDS: usize = 8;
pub const M_WORDS: usize = 16;
pub const N_OUT_WORDS: usize = 8;
pub const ADDS_PER_ROUND: usize = 7;
pub const ADDS_PER_SCHED: usize = 3;
pub const CARRIES_PER_ADD: usize = WORD_BITS - 1; // 31

/// SHA-256 IV (FIPS 180-4 §5.3.3).
pub const SHA256_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];
/// SHA-256 round constants (FIPS 180-4 §4.2.2).
pub const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];

// I/O-aligned layout: the fixed input chaining value `H_in` lives in slot 0,
// the output in slot 1, and the raw 64-byte message in slots 2 and 3. `H_in`
// is constrained to SHA256_IV; only the message and output slots are exposed
// through `SLOTS` to the VM proof bridge.
pub const SLOT_BITS: usize = 256; // 2^8, one 256-bit chaining value
pub const H_BASE: usize = 0; // input region, slot 0: [0, 256)
pub const H_OUT_BASE: usize = SLOT_BITS; // output region, slot 1: [256, 512)
// Note: M (the 512-bit message block) lives at bits 512..1024 — directly
// after H_OUT, with no Z_CONST gap in the middle. This gives a clean 4-slot
// region of 1024 bits at the start of each block (slot 0 = H, slot 1 = H_OUT,
// slot 2 = M_lo, slot 3 = M_hi), so the Merkle-path protocol's
// `MerkleLayout` can address `(H_in, H_out, M_left, M_right)` by single-bit
// slot selectors. The Z_CONST constant-1 bit moved to the end of useful_bits
// (after the OUT_CARRY block), where it sits in a 1-bit gap that doesn't
// disturb the slot alignment.
pub const M_BASE: usize = 2 * SLOT_BITS; // 512
pub const CH_AND_BASE: usize = M_BASE + M_WORDS * WORD_BITS; // 1,024
pub const MAJ_AND_BASE: usize = CH_AND_BASE + N_ROUNDS * WORD_BITS; // 3,072
pub const ROUND_CARRY_BASE: usize = MAJ_AND_BASE + N_ROUNDS * WORD_BITS; // 5,120
pub const W_BASE: usize = ROUND_CARRY_BASE + N_ROUNDS * ADDS_PER_ROUND * CARRIES_PER_ADD; // 19,008
pub const SCHED_CARRY_BASE: usize = W_BASE + N_SCHED * WORD_BITS; // 20,544
pub const T1_BASE: usize = SCHED_CARRY_BASE + N_SCHED * ADDS_PER_SCHED * CARRIES_PER_ADD; // 25,008
pub const E_NEW_BASE: usize = T1_BASE + N_ROUNDS * WORD_BITS; // 27,056
pub const A_NEW_BASE: usize = E_NEW_BASE + N_ROUNDS * WORD_BITS; // 29,104
pub const OUT_CARRY_BASE: usize = A_NEW_BASE + N_ROUNDS * WORD_BITS; // 31,152
pub const Z_CONST_POS: usize = OUT_CARRY_BASE + N_OUT_WORDS * CARRIES_PER_ADD; // 31,400
pub const USEFUL_BITS: usize = Z_CONST_POS + 1; // 31,401

// Slot accessors.
#[inline]
pub fn h_bit(w: usize, b: usize) -> usize {
    H_BASE + WORD_BITS * w + b
}
#[inline]
pub fn m_bit(i: usize, b: usize) -> usize {
    // SHA-256 interprets message words big-endian, while the VM exposes raw
    // bytes as little-endian F64 limbs. Reverse the four bytes inside each
    // u32 so the physical 512-bit M region is byte-identical to VM memory.
    M_BASE + WORD_BITS * i + (b ^ 24)
}
#[inline]
pub fn ch_and_bit(r: usize, b: usize) -> usize {
    CH_AND_BASE + WORD_BITS * r + b
}
#[inline]
pub fn maj_and_bit(r: usize, b: usize) -> usize {
    MAJ_AND_BASE + WORD_BITS * r + b
}
#[inline]
pub fn round_carry_bit(r: usize, add: usize, b: usize) -> usize {
    ROUND_CARRY_BASE + r * ADDS_PER_ROUND * CARRIES_PER_ADD + add * CARRIES_PER_ADD + b
}
#[inline]
pub fn w_bit(t: usize, b: usize) -> usize {
    debug_assert!(t < N_SCHED + 16);
    if t < 16 {
        m_bit(t, b)
    } else {
        W_BASE + (t - 16) * WORD_BITS + b
    }
}
#[inline]
pub fn sched_carry_bit(t: usize, add: usize, b: usize) -> usize {
    debug_assert!((16..16 + N_SCHED).contains(&t));
    SCHED_CARRY_BASE + (t - 16) * ADDS_PER_SCHED * CARRIES_PER_ADD + add * CARRIES_PER_ADD + b
}
#[inline]
pub fn t1_bit(r: usize, b: usize) -> usize {
    T1_BASE + WORD_BITS * r + b
}
#[inline]
pub fn e_new_bit(r: usize, b: usize) -> usize {
    E_NEW_BASE + WORD_BITS * r + b
}
#[inline]
pub fn a_new_bit(r: usize, b: usize) -> usize {
    A_NEW_BASE + WORD_BITS * r + b
}
#[inline]
pub fn out_carry_bit(w: usize, b: usize) -> usize {
    OUT_CARRY_BASE + w * CARRIES_PER_ADD + b
}
#[inline]
pub fn h_out_bit(w: usize, b: usize) -> usize {
    // Standard SHA-256 serializes digest words big-endian. Keep the physical
    // output region byte-identical to that digest for direct VM-table linking.
    H_OUT_BASE + w * WORD_BITS + (b ^ 24)
}

// ───────────────────────────────────────────────────────────────────────────
// Symbolic XOR-support builder
// ───────────────────────────────────────────────────────────────────────────

/// Sorted-deduplicated XOR support — a row of `A` or `B` is one such Vec.
type Sup = Vec<usize>;
/// 32 per-bit supports = one 32-bit "word" in the symbolic computation.
type Word = Vec<Sup>;

fn zero_word() -> Word {
    (0..WORD_BITS).map(|_| Sup::new()).collect()
}

fn wire_word<F: Fn(usize) -> usize>(slot: F) -> Word {
    (0..WORD_BITS).map(|b| vec![slot(b)]).collect()
}

/// Symmetric difference of two sorted Vecs.
fn xor_sup(a: &Sup, b: &Sup) -> Sup {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else if a[i] > b[j] {
            out.push(b[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

fn xor3(a: &Sup, b: &Sup, c: &Sup) -> Sup {
    xor_sup(&xor_sup(a, b), c)
}

fn xor_words(x: &Word, y: &Word) -> Word {
    (0..WORD_BITS).map(|i| xor_sup(&x[i], &y[i])).collect()
}

fn rotr(w: &Word, n: usize) -> Word {
    (0..WORD_BITS).map(|i| w[(i + n) % WORD_BITS].clone()).collect()
}

fn shr(w: &Word, n: usize) -> Word {
    (0..WORD_BITS)
        .map(|i| {
            if i + n < WORD_BITS {
                w[i + n].clone()
            } else {
                Sup::new()
            }
        })
        .collect()
}

fn rot_xor3(w: &Word, r1: usize, r2: usize, r3: usize) -> Word {
    let a = rotr(w, r1);
    let b = rotr(w, r2);
    let c = rotr(w, r3);
    (0..WORD_BITS).map(|i| xor3(&a[i], &b[i], &c[i])).collect()
}

fn sigma_xor(w: &Word, r1: usize, r2: usize, sh: usize) -> Word {
    let a = rotr(w, r1);
    let b = rotr(w, r2);
    let s = shr(w, sh);
    (0..WORD_BITS).map(|i| xor3(&a[i], &b[i], &s[i])).collect()
}

#[inline]
fn sigma_0(w: &Word) -> Word {
    sigma_xor(w, 7, 18, 3)
}
#[inline]
fn sigma_1(w: &Word) -> Word {
    sigma_xor(w, 17, 19, 10)
}
#[inline]
fn big_sigma_0(w: &Word) -> Word {
    rot_xor3(w, 2, 13, 22)
}
#[inline]
fn big_sigma_1(w: &Word) -> Word {
    rot_xor3(w, 6, 11, 25)
}

/// 32-bit modular add `x + y`. Allocates 31 carry-aux AND rows via
/// `carry_slot(i)`; the carry chain is `cin[i+1] = cin[i] ⊕ carry_aux[i]`.
/// Returns the symbolic 32-bit sum (per-bit XOR support).
fn add32_inline<F: Fn(usize) -> usize>(
    x: &Word,
    y: &Word,
    carry_slot: F,
    a_rows: &mut [Sup],
    b_rows: &mut [Sup],
) -> Word {
    let mut sum = zero_word();
    let mut cin: Sup = Sup::new();
    for i in 0..WORD_BITS {
        sum[i] = xor3(&x[i], &y[i], &cin);
        if i < CARRIES_PER_ADD {
            let slot = carry_slot(i);
            a_rows[slot] = xor_sup(&x[i], &cin);
            b_rows[slot] = xor_sup(&y[i], &cin);
            cin = xor_sup(&cin, &vec![slot]);
        }
    }
    sum
}

/// Materialize a symbolic word at fresh slots: emit 32 rows
/// `(linear support) · z[Z_CONST] = z[slot]`, return a slot-word.
fn materialize<F: Fn(usize) -> usize>(raw: &Word, slot_fn: F, a_rows: &mut [Sup], b_rows: &mut [Sup]) -> Word {
    let mut out = zero_word();
    for b in 0..WORD_BITS {
        let s = slot_fn(b);
        a_rows[s] = raw[b].clone();
        b_rows[s] = vec![Z_CONST_POS];
        out[b] = vec![s];
    }
    out
}

fn add32_alloc<F1: Fn(usize) -> usize, F2: Fn(usize) -> usize>(
    x: &Word,
    y: &Word,
    carry_slot: F1,
    sum_slot: F2,
    a_rows: &mut [Sup],
    b_rows: &mut [Sup],
) -> Word {
    let raw = add32_inline(x, y, carry_slot, a_rows, b_rows);
    materialize(&raw, sum_slot, a_rows, b_rows)
}

// ───────────────────────────────────────────────────────────────────────────
// Public matrix builder
// ───────────────────────────────────────────────────────────────────────────

/// Build `(A_0, B_0)` for one block of the hybrid SHA-256 R1CS. `C_0 = I`
/// (circuit shape); use [`build_block_r1cs`] to wrap these into a
/// [`BlockR1cs`].
pub fn build_matrices() -> (SparseBinaryMatrix, SparseBinaryMatrix) {
    let mut a_rows: Vec<Sup> = vec![Sup::new(); K];
    let mut b_rows: Vec<Sup> = vec![Sup::new(); K];

    // Z_CONST tautology: z[0]·z[0] = z[0] (boolean-pin).
    a_rows[Z_CONST_POS] = vec![Z_CONST_POS];
    b_rows[Z_CONST_POS] = vec![Z_CONST_POS];

    // H_in is pinned to the standard SHA-256 IV. M_in is free witness.
    for w in 0..H_WORDS {
        for b in 0..WORD_BITS {
            let s = h_bit(w, b);
            if (SHA256_IV[w] >> b) & 1 == 1 {
                a_rows[s] = vec![Z_CONST_POS];
                b_rows[s] = vec![Z_CONST_POS];
            }
        }
    }
    for i in 0..M_WORDS {
        for b in 0..WORD_BITS {
            let s = m_bit(i, b);
            a_rows[s] = vec![s];
            b_rows[s] = vec![Z_CONST_POS];
        }
    }

    let h_in: Vec<Word> = (0..H_WORDS).map(|w| wire_word(|b| h_bit(w, b))).collect();
    let mut w_arr: Vec<Word> = (0..M_WORDS).map(|i| wire_word(|b| m_bit(i, b))).collect();

    // Message schedule (W[16..64]). Inline sched_0, sched_1; allocate W[t] = sched_2.
    for t in 16..(16 + N_SCHED) {
        let s1 = sigma_1(&w_arr[t - 2]);
        let s0 = sigma_0(&w_arr[t - 15]);
        let w_m7 = w_arr[t - 7].clone();
        let w_m16 = w_arr[t - 16].clone();
        let sched_0 = add32_inline(&s1, &w_m7, |i| sched_carry_bit(t, 0, i), &mut a_rows, &mut b_rows);
        let sched_1 = add32_inline(&sched_0, &s0, |i| sched_carry_bit(t, 1, i), &mut a_rows, &mut b_rows);
        let w_t = add32_alloc(
            &sched_1,
            &w_m16,
            |i| sched_carry_bit(t, 2, i),
            |b| w_bit(t, b),
            &mut a_rows,
            &mut b_rows,
        );
        w_arr.push(w_t);
    }

    // Working state (a, b, c, d, e, f, g, h).
    let mut state: [Word; 8] = [
        h_in[0].clone(),
        h_in[1].clone(),
        h_in[2].clone(),
        h_in[3].clone(),
        h_in[4].clone(),
        h_in[5].clone(),
        h_in[6].clone(),
        h_in[7].clone(),
    ];

    for r in 0..N_ROUNDS {
        let a = state[0].clone();
        let bb = state[1].clone();
        let c = state[2].clone();
        let d = state[3].clone();
        let e = state[4].clone();
        let f = state[5].clone();
        let g = state[6].clone();
        let h_var = state[7].clone();

        // ch_and[r][bit] = e[bit] · (f[bit] ⊕ g[bit])
        let mut ch_and = zero_word();
        for bit in 0..WORD_BITS {
            let s = ch_and_bit(r, bit);
            a_rows[s] = e[bit].clone();
            b_rows[s] = xor_sup(&f[bit], &g[bit]);
            ch_and[bit] = vec![s];
        }
        // maj_and[r][bit] = (a[bit] ⊕ b[bit]) · (a[bit] ⊕ c[bit])
        let mut maj_and = zero_word();
        for bit in 0..WORD_BITS {
            let s = maj_and_bit(r, bit);
            a_rows[s] = xor_sup(&a[bit], &bb[bit]);
            b_rows[s] = xor_sup(&a[bit], &c[bit]);
            maj_and[bit] = vec![s];
        }
        let ch_out = xor_words(&ch_and, &g); // Ch = e·(f⊕g) ⊕ g
        let maj_out = xor_words(&maj_and, &a); // Maj = (a⊕b)·(a⊕c) ⊕ a

        // T1 chain: inline T1_0..T1_2, allocate T1.
        let t1_0 = add32_inline(
            &h_var,
            &big_sigma_1(&e),
            |i| round_carry_bit(r, 0, i),
            &mut a_rows,
            &mut b_rows,
        );
        let t1_1 = add32_inline(&t1_0, &ch_out, |i| round_carry_bit(r, 1, i), &mut a_rows, &mut b_rows);
        let k_word: Word = (0..WORD_BITS)
            .map(|i| {
                if (SHA256_K[r] >> i) & 1 == 1 {
                    vec![Z_CONST_POS]
                } else {
                    Sup::new()
                }
            })
            .collect();
        let t1_2 = add32_inline(&t1_1, &k_word, |i| round_carry_bit(r, 2, i), &mut a_rows, &mut b_rows);
        let t1 = add32_alloc(
            &t1_2,
            &w_arr[r],
            |i| round_carry_bit(r, 3, i),
            |b| t1_bit(r, b),
            &mut a_rows,
            &mut b_rows,
        );
        // T2 inlined; E_NEW, A_NEW allocated.
        let t2 = add32_inline(
            &big_sigma_0(&a),
            &maj_out,
            |i| round_carry_bit(r, 4, i),
            &mut a_rows,
            &mut b_rows,
        );
        let e_new = add32_alloc(
            &d,
            &t1,
            |i| round_carry_bit(r, 5, i),
            |b| e_new_bit(r, b),
            &mut a_rows,
            &mut b_rows,
        );
        let a_new = add32_alloc(
            &t1,
            &t2,
            |i| round_carry_bit(r, 6, i),
            |b| a_new_bit(r, b),
            &mut a_rows,
            &mut b_rows,
        );

        // Register shift: (a', b', c', d', e', f', g', h') = (A_NEW, a, b, c, E_NEW, e, f, g)
        state = [a_new, a, bb, c, e_new, e, f, g];
    }

    // Output feed-forward: H_out[w] = state[w] + H_in[w].
    for w in 0..N_OUT_WORDS {
        let _ = add32_alloc(
            &state[w],
            &h_in[w],
            |i| out_carry_bit(w, i),
            |b| h_out_bit(w, b),
            &mut a_rows,
            &mut b_rows,
        );
    }

    let to_mat = |rows| SparseBinaryMatrix {
        num_rows: K,
        num_cols: K,
        rows,
    };
    (to_mat(a_rows), to_mat(b_rows))
}

// ───────────────────────────────────────────────────────────────────────────
// Witness generator
// ───────────────────────────────────────────────────────────────────────────

fn write_word(z: &mut [bool], base: usize, v: u32) {
    for b in 0..WORD_BITS {
        z[base + b] = (v >> b) & 1 == 1;
    }
}

fn write_word_at<F: Fn(usize) -> usize>(z: &mut [bool], slot: F, v: u32) {
    for b in 0..WORD_BITS {
        z[slot(b)] = (v >> b) & 1 == 1;
    }
}

/// 32-bit add with carry-aux output. `cin[i+1] = cin[i] ⊕ carry_aux[i]`.
fn add32_w(x: u32, y: u32, carry_base: usize, z: &mut [bool]) -> u32 {
    let mut cin: bool = false;
    for i in 0..CARRIES_PER_ADD {
        let xi = ((x >> i) & 1) == 1;
        let yi = ((y >> i) & 1) == 1;
        let aux = (xi ^ cin) && (yi ^ cin);
        z[carry_base + i] = aux;
        cin ^= aux;
    }
    x.wrapping_add(y)
}

/// Build the per-block boolean witness for one SHA-256 compression
/// `f(h_in, m) → H_out`. Length = `K = 2^15`. Slot positions [USEFUL_BITS, K)
/// are zero-padded.
pub fn build_block_witness(h_in: &[u32; 8], m: &[u32; 16]) -> Vec<bool> {
    assert_eq!(h_in, &SHA256_IV, "SHA-256 VM compression pins H_in to the IV");
    let mut z = vec![false; K];
    z[Z_CONST_POS] = true;

    for w in 0..H_WORDS {
        write_word(&mut z, h_bit(w, 0), h_in[w]);
    }
    for i in 0..M_WORDS {
        write_word_at(&mut z, |b| m_bit(i, b), m[i]);
    }

    // Schedule W[16..64].
    let mut w_arr = [0u32; 64];
    w_arr[..16].copy_from_slice(m);
    for t in 16..64 {
        let s0 = w_arr[t - 15].rotate_right(7) ^ w_arr[t - 15].rotate_right(18) ^ (w_arr[t - 15] >> 3);
        let s1 = w_arr[t - 2].rotate_right(17) ^ w_arr[t - 2].rotate_right(19) ^ (w_arr[t - 2] >> 10);
        let sched_0 = add32_w(s1, w_arr[t - 7], sched_carry_bit(t, 0, 0), &mut z);
        let sched_1 = add32_w(sched_0, s0, sched_carry_bit(t, 1, 0), &mut z);
        let w_t = add32_w(sched_1, w_arr[t - 16], sched_carry_bit(t, 2, 0), &mut z);
        write_word(&mut z, w_bit(t, 0), w_t);
        w_arr[t] = w_t;
    }

    // Rounds.
    let mut state = *h_in;
    for r in 0..N_ROUNDS {
        let (a, b, c, d, e, f, g, h_var) = (
            state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7],
        );
        let ch_and = e & (f ^ g);
        write_word(&mut z, ch_and_bit(r, 0), ch_and);
        let maj_and = (a ^ b) & (a ^ c);
        write_word(&mut z, maj_and_bit(r, 0), maj_and);

        let ch_out = ch_and ^ g;
        let maj_out = maj_and ^ a;
        let s1e = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let s0a = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);

        let t1_0 = add32_w(h_var, s1e, round_carry_bit(r, 0, 0), &mut z);
        let t1_1 = add32_w(t1_0, ch_out, round_carry_bit(r, 1, 0), &mut z);
        let t1_2 = add32_w(t1_1, SHA256_K[r], round_carry_bit(r, 2, 0), &mut z);
        let t1 = add32_w(t1_2, w_arr[r], round_carry_bit(r, 3, 0), &mut z);
        write_word(&mut z, t1_bit(r, 0), t1);

        let t2 = add32_w(s0a, maj_out, round_carry_bit(r, 4, 0), &mut z);
        let e_new = add32_w(d, t1, round_carry_bit(r, 5, 0), &mut z);
        write_word(&mut z, e_new_bit(r, 0), e_new);
        let a_new = add32_w(t1, t2, round_carry_bit(r, 6, 0), &mut z);
        write_word(&mut z, a_new_bit(r, 0), a_new);

        state = [a_new, a, b, c, e_new, e, f, g];
    }

    // Output feed-forward.
    for w in 0..N_OUT_WORDS {
        let h_out = add32_w(state[w], h_in[w], out_carry_bit(w, 0), &mut z);
        write_word_at(&mut z, |b| h_out_bit(w, b), h_out);
    }
    z
}

/// Read the 8-word post-compression hash out of a single block of witness.
pub fn read_h_out(z: &[bool]) -> [u32; 8] {
    std::array::from_fn(|w| (0..WORD_BITS).fold(0u32, |acc, b| acc | ((z[h_out_bit(w, b)] as u32) << b)))
}

// ───────────────────────────────────────────────────────────────────────────
// BlockR1cs constructor
// ───────────────────────────────────────────────────────────────────────────

/// Build a [`BlockR1cs`] for `2^n_blocks_log` SHA-256 compressions batched
/// block-diagonally (one compression per block). `n_blocks_log ≥ 3` is the
/// lincheck floor.
pub fn build_block_r1cs(n_blocks_log: usize) -> BlockR1cs {
    let (a_0, b_0) = build_matrices();
    crate::binary_witness::build_block_r1cs_with_matrices(
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

// ───────────────────────────────────────────────────────────────────────────
// Lincheck circuit walker — mirrors `build_matrices`. Same structure as
// `sha2::Sha2LincheckCircuit` but uses this module's I/O-aligned slot
// positions.
// ───────────────────────────────────────────────────────────────────────────

fn scatter_add32_inline<F: Fn(usize) -> usize>(
    x: &Word,
    y: &Word,
    carry_slot: F,
    comb: &mut [F192],
    alpha: F192,
    eq_inner: &[F192],
) -> Word {
    let mut sum = zero_word();
    let mut cin: Sup = Sup::new();
    for i in 0..WORD_BITS {
        sum[i] = xor3(&x[i], &y[i], &cin);
        if i < CARRIES_PER_ADD {
            let slot = carry_slot(i);
            let row = slot;
            let e = eq_inner[row];
            let ea = alpha * e;
            for &c in xor_sup(&x[i], &cin).iter() {
                comb[c] += ea;
            }
            for &c in xor_sup(&y[i], &cin).iter() {
                comb[c] += e;
            }
            cin = xor_sup(&cin, &vec![slot]);
        }
    }
    sum
}

fn scatter_materialize<F: Fn(usize) -> usize>(
    raw: &Word,
    slot_fn: F,
    comb: &mut [F192],
    alpha: F192,
    eq_inner: &[F192],
) -> Word {
    let mut out = zero_word();
    for b in 0..WORD_BITS {
        let s = slot_fn(b);
        let e = eq_inner[s];
        let ea = alpha * e;
        for &c in raw[b].iter() {
            comb[c] += ea;
        }
        comb[Z_CONST_POS] += e;
        out[b] = vec![s];
    }
    out
}

fn scatter_add32_alloc<F1: Fn(usize) -> usize, F2: Fn(usize) -> usize>(
    x: &Word,
    y: &Word,
    carry_slot: F1,
    sum_slot: F2,
    comb: &mut [F192],
    alpha: F192,
    eq_inner: &[F192],
) -> Word {
    let raw = scatter_add32_inline(x, y, carry_slot, comb, alpha, eq_inner);
    scatter_materialize(&raw, sum_slot, comb, alpha, eq_inner)
}

pub struct Sha2LincheckCircuit;

impl crate::lincheck::LincheckCircuit for Sha2LincheckCircuit {
    fn n_cols(&self) -> usize {
        K
    }

    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        assert_eq!(eq_inner.len(), K, "eq_inner length must equal n_cols = K");
        let mut comb = vec![F192::ZERO; K];

        let e0 = eq_inner[Z_CONST_POS];
        comb[Z_CONST_POS] += alpha * e0;
        comb[Z_CONST_POS] += e0;

        for w in 0..H_WORDS {
            for b in 0..WORD_BITS {
                let s = h_bit(w, b);
                let e = eq_inner[s];
                if (SHA256_IV[w] >> b) & 1 == 1 {
                    comb[Z_CONST_POS] += alpha * e + e;
                }
            }
        }
        for i in 0..M_WORDS {
            for b in 0..WORD_BITS {
                let s = m_bit(i, b);
                let e = eq_inner[s];
                comb[s] += alpha * e;
                comb[Z_CONST_POS] += e;
            }
        }

        let h_in: Vec<Word> = (0..H_WORDS).map(|w| wire_word(|b| h_bit(w, b))).collect();
        let mut w_arr: Vec<Word> = (0..M_WORDS).map(|i| wire_word(|b| m_bit(i, b))).collect();

        for t in 16..(16 + N_SCHED) {
            let s1 = sigma_1(&w_arr[t - 2]);
            let s0 = sigma_0(&w_arr[t - 15]);
            let w_m7 = w_arr[t - 7].clone();
            let w_m16 = w_arr[t - 16].clone();
            let sched_0 = scatter_add32_inline(&s1, &w_m7, |i| sched_carry_bit(t, 0, i), &mut comb, alpha, eq_inner);
            let sched_1 = scatter_add32_inline(&sched_0, &s0, |i| sched_carry_bit(t, 1, i), &mut comb, alpha, eq_inner);
            let w_t = scatter_add32_alloc(
                &sched_1,
                &w_m16,
                |i| sched_carry_bit(t, 2, i),
                |b| w_bit(t, b),
                &mut comb,
                alpha,
                eq_inner,
            );
            w_arr.push(w_t);
        }

        let mut state: [Word; 8] = [
            h_in[0].clone(),
            h_in[1].clone(),
            h_in[2].clone(),
            h_in[3].clone(),
            h_in[4].clone(),
            h_in[5].clone(),
            h_in[6].clone(),
            h_in[7].clone(),
        ];

        for r in 0..N_ROUNDS {
            let a = state[0].clone();
            let bb = state[1].clone();
            let c = state[2].clone();
            let d = state[3].clone();
            let e = state[4].clone();
            let f = state[5].clone();
            let g = state[6].clone();
            let h_var = state[7].clone();

            let mut ch_and = zero_word();
            for bit in 0..WORD_BITS {
                let s = ch_and_bit(r, bit);
                let eq = eq_inner[s];
                let ea = alpha * eq;
                for &c2 in e[bit].iter() {
                    comb[c2] += ea;
                }
                for &c2 in xor_sup(&f[bit], &g[bit]).iter() {
                    comb[c2] += eq;
                }
                ch_and[bit] = vec![s];
            }
            let mut maj_and = zero_word();
            for bit in 0..WORD_BITS {
                let s = maj_and_bit(r, bit);
                let eq = eq_inner[s];
                let ea = alpha * eq;
                for &c2 in xor_sup(&a[bit], &bb[bit]).iter() {
                    comb[c2] += ea;
                }
                for &c2 in xor_sup(&a[bit], &c[bit]).iter() {
                    comb[c2] += eq;
                }
                maj_and[bit] = vec![s];
            }
            let ch_out = xor_words(&ch_and, &g);
            let maj_out = xor_words(&maj_and, &a);

            let t1_0 = scatter_add32_inline(
                &h_var,
                &big_sigma_1(&e),
                |i| round_carry_bit(r, 0, i),
                &mut comb,
                alpha,
                eq_inner,
            );
            let t1_1 = scatter_add32_inline(&t1_0, &ch_out, |i| round_carry_bit(r, 1, i), &mut comb, alpha, eq_inner);
            let k_word: Word = (0..WORD_BITS)
                .map(|i| {
                    if (SHA256_K[r] >> i) & 1 == 1 {
                        vec![Z_CONST_POS]
                    } else {
                        Sup::new()
                    }
                })
                .collect();
            let t1_2 = scatter_add32_inline(&t1_1, &k_word, |i| round_carry_bit(r, 2, i), &mut comb, alpha, eq_inner);
            let t1 = scatter_add32_alloc(
                &t1_2,
                &w_arr[r],
                |i| round_carry_bit(r, 3, i),
                |b| t1_bit(r, b),
                &mut comb,
                alpha,
                eq_inner,
            );
            let t2 = scatter_add32_inline(
                &big_sigma_0(&a),
                &maj_out,
                |i| round_carry_bit(r, 4, i),
                &mut comb,
                alpha,
                eq_inner,
            );
            let e_new = scatter_add32_alloc(
                &d,
                &t1,
                |i| round_carry_bit(r, 5, i),
                |b| e_new_bit(r, b),
                &mut comb,
                alpha,
                eq_inner,
            );
            let a_new = scatter_add32_alloc(
                &t1,
                &t2,
                |i| round_carry_bit(r, 6, i),
                |b| a_new_bit(r, b),
                &mut comb,
                alpha,
                eq_inner,
            );

            state = [a_new, a, bb, c, e_new, e, f, g];
        }

        for w in 0..N_OUT_WORDS {
            let _ = scatter_add32_alloc(
                &state[w],
                &h_in[w],
                |i| out_carry_bit(w, i),
                |b| h_out_bit(w, b),
                &mut comb,
                alpha,
                eq_inner,
            );
        }

        comb
    }
}

// ───────────────────────────────────────────────────────────────────────────
// Fast-path: fused (z, a, b, z_lincheck) packed witness builder.
//
// Each adder writes its carry-aux rows always; the sum row is written only
// for *slotted* adders (W[t], T1, E_NEW, A_NEW, H_out).
//
// Witness-value insight: at a carry-aux slot, `a` and `b` are the *scalar
// evaluations* of the row's linear A/B supports — `(x[i] ⊕ cin[i])` is the
// same bit value regardless of how many slots the A-row carries.
// ───────────────────────────────────────────────────────────────────────────

// ───────────────────────────────────────────────────────────────────────────
// SHA-256 reference helpers (used by witness gen).
// ───────────────────────────────────────────────────────────────────────────

#[inline]
pub(crate) fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}
#[inline]
pub(crate) fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}
#[inline]
pub(crate) fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}
#[inline]
pub(crate) fn small_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

/// 32-bit add `x + y`. Writes 31 carry-aux rows at `carry_base..+31` with
/// `(z, a, b) = (aux, left, right)` where `aux = left & right`,
/// `left = (x ⊕ cin) & 0x7FFFFFFF`, `right = (y ⊕ cin) & 0x7FFFFFFF`. Top
/// carry bit is masked so the unallocated 32nd slot isn't touched.
///
/// **No c buffer.** C = I, so c == z byte-for-byte; callers wrap z_packed
/// as the c-side input to zerocheck.
#[inline(always)]
fn add_inline_ab(x: u32, y: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64], carry_base: usize) -> u32 {
    let sum_word: u32 = x.wrapping_add(y);
    let cin: u32 = sum_word ^ x ^ y;
    const MASK_LO31: u32 = 0x7FFF_FFFF;
    let left = (x ^ cin) & MASK_LO31;
    let right = (y ^ cin) & MASK_LO31;
    let carry_aux = left & right;
    or_u32_at_bit(z, carry_base, carry_aux);
    or_u32_at_bit(a, carry_base, left);
    or_u32_at_bit(b, carry_base, right);
    sum_word
}

/// 32-bit add that ALSO materializes the sum bits at `sum_base..+32` with
/// `(z, a, b) = (sum, sum, 1)`. c == z by aliasing.
/// Build the (z, a, b) packed buffers for ONE SHA-256 compression into the
/// u64 views (one block worth: `K / 64` u64s each). Buffers must be zero on
/// entry. **No c buffer** (c == z byte-for-byte since C = I).
fn build_block_ab_packed_into(h_in: &[u32; 8], m: &[u32; 16], z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    assert_eq!(h_in, &SHA256_IV, "SHA-256 VM compression pins H_in to the IV");
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    // Z_CONST: (z, a, b) = (1, 1, 1).
    or_bit_at(z, Z_CONST_POS);
    or_bit_at(a, Z_CONST_POS);
    or_bit_at(b, Z_CONST_POS);

    // H_in: pinned SHA-256 IV rows → set bits are (1, 1, 1), clear bits zero.
    for w in 0..H_WORDS {
        let off = h_bit(w, 0);
        let v = h_in[w];
        or_u32_at_bit(z, off, v);
        or_u32_at_bit(a, off, v);
        or_u32_at_bit(b, off, v);
    }
    // M: free-witness tautologies. Store raw message bytes in physical slot
    // order; `m_bit` performs the inverse byte permutation for SHA word use.
    for i in 0..M_WORDS {
        let off = M_BASE + WORD_BITS * i;
        let v = m[i].swap_bytes();
        or_u32_at_bit(z, off, v);
        or_u32_at_bit(a, off, v);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);
    }

    // Message schedule. sched_0, sched_1 inlined; W[t] = sched_2 allocated.
    // The 3 × 31-bit sched carries per t are contiguous (93 bits at stride
    // 93) — composed in a register record and flushed once per buffer (see
    // [`BitRecord`]).
    let mut w_sched = [0u32; 64];
    w_sched[..16].copy_from_slice(m);
    const SC0: usize = 0;
    const SC1: usize = CARRIES_PER_ADD;
    const SC2: usize = 2 * CARRIES_PER_ADD;
    for t in 16..64 {
        let mut rz = BitRecord::<2>::new();
        let mut ra = BitRecord::<2>::new();
        let mut rb = BitRecord::<2>::new();

        macro_rules! add_into {
            ($pos:ident, $x:expr, $y:expr) => {{
                let (sum, left, right, carry) = add_carry_parts($x, $y);
                rz.push::<$pos>(carry);
                ra.push::<$pos>(left);
                rb.push::<$pos>(right);
                sum
            }};
        }

        let s_0 = add_into!(SC0, small_sigma1(w_sched[t - 2]), w_sched[t - 7]);
        let s_1 = add_into!(SC1, s_0, small_sigma0(w_sched[t - 15]));
        let w_t = add_into!(SC2, s_1, w_sched[t - 16]);

        let sched_base = sched_carry_bit(t, 0, 0);
        rz.flush(z, sched_base);
        ra.flush(a, sched_base);
        rb.flush(b, sched_base);

        // W[t] sum row: (z, a, b) = (w_t, w_t, 1).
        let off = w_bit(t, 0);
        or_u32_at_bit(z, off, w_t);
        or_u32_at_bit(a, off, w_t);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);

        w_sched[t] = w_t;
    }

    // 64 rounds.
    let [mut aa, mut bb, mut cc, mut dd, mut ee, mut ff, mut gg, mut hh] = *h_in;
    for r in 0..N_ROUNDS {
        // ch_and AND row: (z, a, b) = (ch, e, f⊕g); c == z = ch.
        let f_xor_g = ff ^ gg;
        let ch_and_v = ee & f_xor_g;
        let off = ch_and_bit(r, 0);
        or_u32_at_bit(z, off, ch_and_v);
        or_u32_at_bit(a, off, ee);
        or_u32_at_bit(b, off, f_xor_g);
        let ch_out = ch_and_v ^ gg;

        // maj_and AND row.
        let b_xor_a = bb ^ aa;
        let c_xor_a = cc ^ aa;
        let maj_and_v = b_xor_a & c_xor_a;
        let off = maj_and_bit(r, 0);
        or_u32_at_bit(z, off, maj_and_v);
        or_u32_at_bit(a, off, b_xor_a);
        or_u32_at_bit(b, off, c_xor_a);
        let maj_out = maj_and_v ^ aa;

        // The 7 × 31-bit round carries are contiguous (217 bits at stride
        // 217) — composed in a register record and flushed once per buffer.
        const RC0: usize = 0;
        const RC1: usize = CARRIES_PER_ADD;
        const RC2: usize = 2 * CARRIES_PER_ADD;
        const RC3: usize = 3 * CARRIES_PER_ADD;
        const RC4: usize = 4 * CARRIES_PER_ADD;
        const RC5: usize = 5 * CARRIES_PER_ADD;
        const RC6: usize = 6 * CARRIES_PER_ADD;
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

        // T1 chain: T1_0..T1_2 inlined, T1 (= T1_3) allocated.
        let t1_0 = add_into!(RC0, hh, big_sigma1(ee));
        let t1_1 = add_into!(RC1, t1_0, ch_out);
        let t1_2 = add_into!(RC2, t1_1, SHA256_K[r]);
        let t1 = add_into!(RC3, t1_2, w_sched[r]);
        let off = t1_bit(r, 0);
        or_u32_at_bit(z, off, t1);
        or_u32_at_bit(a, off, t1);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);

        // T2 inlined.
        let t2 = add_into!(RC4, big_sigma0(aa), maj_out);
        // E_NEW, A_NEW allocated.
        let e_new = add_into!(RC5, dd, t1);
        let off = e_new_bit(r, 0);
        or_u32_at_bit(z, off, e_new);
        or_u32_at_bit(a, off, e_new);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);
        let a_new = add_into!(RC6, t1, t2);
        let off = a_new_bit(r, 0);
        or_u32_at_bit(z, off, a_new);
        or_u32_at_bit(a, off, a_new);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);

        let round_base = round_carry_bit(r, 0, 0);
        rz.flush(z, round_base);
        ra.flush(a, round_base);
        rb.flush(b, round_base);

        // Register shift.
        hh = gg;
        gg = ff;
        ff = ee;
        ee = e_new;
        dd = cc;
        cc = bb;
        bb = aa;
        aa = a_new;
    }

    // Output feed-forward.
    let final_state = [aa, bb, cc, dd, ee, ff, gg, hh];
    for w in 0..N_OUT_WORDS {
        let h_out = add_inline_ab(final_state[w], h_in[w], z, a, b, out_carry_bit(w, 0));
        let off = H_OUT_BASE + WORD_BITS * w;
        let physical = h_out.swap_bytes();
        or_u32_at_bit(z, off, physical);
        or_u32_at_bit(a, off, physical);
        or_u32_at_bit(b, off, 0xFFFF_FFFF);
    }
}

/// Like [`generate_witness`] but produces F192-packed `(z, a, b, c)` AND the
/// lincheck byte-stripe in one fused parallel pass. Replaces
/// `pack_witness` + `apply_{a,b,c}_packed` + `pack_z_lincheck_from_packed`.
///
/// 8 k-blocks per parallel task (matching the lincheck stripe granularity).
pub fn generate_witness_with_ab_packed_and_lincheck(
    compressions: &[([u32; 8], [u32; 16])],
    n_blocks_log: usize,
) -> (
    Vec<primitives::field::F192>,
    Vec<primitives::field::F192>,
    Vec<primitives::field::F192>,
    Vec<u8>,
) {
    // Constant-wire pin (docs/const-wire-pin.md): fill padding blocks with a
    // valid compression (of the all-zero input) so the constant cell is 1 in
    // every block. (The chain forbids padding, so this only affects the
    // standalone batch setup.)
    compressions.iter().for_each(assert_pinned);
    let padding: ([u32; 8], [u32; 16]) = (SHA256_IV, [0u32; 16]);
    crate::binary_witness::drive_witness_packed_and_lincheck(
        compressions,
        Some(&padding),
        n_blocks_log,
        K_LOG,
        |comp: &([u32; 8], [u32; 16]), z_u64, a_u64, b_u64| {
            let (h_in, m) = comp;
            build_block_ab_packed_into(h_in, m, z_u64, a_u64, b_u64);
        },
    )
}

// ───────────────────────────────────────────────────────────────────────────
// Multi-block witness gen + Setup
// ───────────────────────────────────────────────────────────────────────────

/// Minimum `n_blocks_log` to fit `n_compressions` (one compression per
/// k-block), subject to the lincheck floor of `n_blocks_log ≥ 3`.
pub fn min_n_blocks_log(n_compressions: usize) -> usize {
    assert!(n_compressions >= 1);
    let n = n_compressions.max(8);
    n.next_power_of_two().trailing_zeros() as usize
}

/// Build the boolean witness across `2^n_blocks_log` blocks, one compression
/// per block. Parallelized via rayon.
pub fn generate_witness(compressions: &[([u32; 8], [u32; 16])], n_blocks_log: usize) -> Vec<bool> {
    use rayon::prelude::*;
    let n_total_blocks = 1usize << n_blocks_log;
    assert!(compressions.len() <= n_total_blocks);

    let mut z = vec![false; n_total_blocks * K];
    z.par_chunks_mut(K).enumerate().for_each(|(block_idx, chunk)| {
        let padding = (SHA256_IV, [0u32; 16]);
        let (h_in, m) = if block_idx < compressions.len() {
            &compressions[block_idx]
        } else {
            &padding
        };
        let block_witness = build_block_witness(h_in, m);
        chunk.copy_from_slice(&block_witness);
    });
    z
}

/// One VM hash instruction: the SHA-256 IV and one unpadded 512-bit message.
pub type Compression = ([u32; 8], [u32; 16]);

#[inline]
fn assert_pinned(block: &Compression) {
    assert_eq!(block.0, SHA256_IV, "SHA-256 VM compression must use the standard IV");
}

/// Pin a raw 512-bit message to the VM's one-compression SHA-256 primitive.
#[inline]
pub fn pinned_compression(message: [u32; 16]) -> Compression {
    (SHA256_IV, message)
}

/// Valid all-zero-message padding instance.
#[inline]
pub fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
}

/// Reference compression, using the same hardware-accelerated primitive as
/// PCS/XMSS. Message words are standard SHA-256 big-endian words.
pub fn sha256_compress(h_in: &[u32; 8], message: &[u32; 16]) -> [u32; 8] {
    assert_eq!(h_in, &SHA256_IV);
    let mut block = [0u8; 64];
    for (dst, word) in block.chunks_exact_mut(4).zip(message) {
        dst.copy_from_slice(&word.to_be_bytes());
    }
    let digest = primitives::sha256::compress(&block);
    std::array::from_fn(|i| u32::from_be_bytes(digest[4 * i..4 * i + 4].try_into().unwrap()))
}

/// Physical packed-witness slots exposed to the VM table, in canonical order
/// `[input u64 × 8, output u64 × 4]`. Both regions are raw-byte aligned.
pub const SLOTS: [usize; 12] = [
    M_BASE / 64,
    M_BASE / 64 + 1,
    M_BASE / 64 + 2,
    M_BASE / 64 + 3,
    M_BASE / 64 + 4,
    M_BASE / 64 + 5,
    M_BASE / 64 + 6,
    M_BASE / 64 + 7,
    H_OUT_BASE / 64,
    H_OUT_BASE / 64 + 1,
    H_OUT_BASE / 64 + 2,
    H_OUT_BASE / 64 + 3,
];

/// Serialize the 128-bit packed-witness subspace of F192.
fn packed_128_bytes(words: &[F192]) -> Vec<u8> {
    let mut out = Vec::with_capacity(words.len() * 16);
    for word in words {
        debug_assert_eq!(word.c2, 0);
        out.extend_from_slice(&word.c0.to_le_bytes());
        out.extend_from_slice(&word.c1.to_le_bytes());
    }
    out
}

/// Protocol-facing setup for a batch of fixed-IV SHA-256 compressions.
#[derive(Clone, Debug)]
pub struct Sha256Setup {
    pub n_blocks: usize,
    pub r1cs: BlockR1cs,
}

impl Sha256Setup {
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be >= 1");
        let r1cs = build_block_r1cs(min_n_blocks_log(n_blocks));
        r1cs.csc_lincheck_circuit();
        primitives::scratch::prewarm_prover(r1cs.m);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_iv_compression_matches_native_and_satisfies_r1cs() {
        let block: [u8; 64] = std::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11));
        let message: [u32; 16] =
            std::array::from_fn(|i| u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
        let z = build_block_witness(&SHA256_IV, &message);
        let native = primitives::sha256::compress(&block);
        let expected: [u32; 8] =
            std::array::from_fn(|i| u32::from_be_bytes(native[4 * i..4 * i + 4].try_into().unwrap()));
        assert_eq!(read_h_out(&z), expected);

        let (a, b) = build_matrices();
        for row in 0..K {
            let av = a.rows[row].iter().fold(false, |acc, &i| acc ^ z[i]);
            let bv = b.rows[row].iter().fold(false, |acc, &i| acc ^ z[i]);
            assert_eq!(av & bv, z[row], "constraint row {row}");
        }
    }
}

/// Digest binding the exact per-block SHA-256 R1CS family.
pub fn family_digest() -> [u8; 32] {
    static DIGEST: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    *DIGEST.get_or_init(|| build_block_r1cs(3).family_digest())
}

/// Process-cached per-block matrices used by native recursion aggregation.
pub fn matrices() -> &'static (SparseBinaryMatrix, SparseBinaryMatrix) {
    static MATRICES: std::sync::OnceLock<(SparseBinaryMatrix, SparseBinaryMatrix)> = std::sync::OnceLock::new();
    MATRICES.get_or_init(build_matrices)
}

/// Direct evaluation of `(u^T A w, u^T B w)` for deferred recursion claims.
pub fn bilinear_matrix_pair(u: &[F192], w: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(w.len(), K);
    let eval = |matrix: &SparseBinaryMatrix| {
        matrix
            .rows
            .iter()
            .zip(u)
            .map(|(row, &ur)| ur * row.iter().map(|&c| w[c]).fold(F192::ZERO, |acc, x| acc + x))
            .fold(F192::ZERO, |acc, x| acc + x)
    };
    let (a, b) = matrices();
    (eval(a), eval(b))
}
// ===== leanVM-b stacked SHA-256 reduction (grafted) =====
// (No Sha256StackProof struct: the zerocheck / lincheck / ring-switch scalars
// ride the shared transcript stream, and the one hash-bearing Ligerito rides
// the caller's opening channel.)

/// One claim on the committed packed SHA-256 witness `q_pkd`, as left by the
/// Flock reduction and handed to the PCS. `claim` is the `ẑ(point) = value`
/// evaluation the PCS must discharge; `s_hat_v` is the prover-only ring-switch
/// tensor weight the packed open consumes (`None` when `k_log < LOG_PACKING`,
/// and unused on the verifier side, which recovers it from `proof.open`).
#[derive(Clone, Debug)]
pub struct WitnessClaim {
    pub claim: crate::proof::ZClaim,
    pub s_hat_v: Option<Vec<F192>>,
}

/// The two claims on the committed witness `q_pkd` left by the Flock SHA-256
/// zerocheck + lincheck reduction, for the PCS to discharge:
/// - `ab`: the `A∘B` side, from lincheck.
/// - `c` : the `C` side, from zerocheck (`C = I`, so a direct z-claim).
///
/// This is the clean seam between Flock's reduction and the PCS: the reduction
/// produces these; the PCS opens them (see [`Sha256Setup::prove_reduction`]).
#[derive(Clone, Debug)]
pub struct ReducedClaims {
    pub ab: WitnessClaim,
    pub c: WitnessClaim,
}

/// Everything [`Sha256Setup::verify_reduction`] recovers: the two `(ab, c)`
/// z-claims for the PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub ab: crate::proof::ZClaim,
    pub c: crate::proof::ZClaim,
    pub zc_claim: crate::zerocheck::ZerocheckClaim,
    pub lc_claim: crate::lincheck::LincheckClaim,
}

impl Sha256Setup {
    /// **Flock reduction (prover).** Run the SHA-256 zerocheck and lincheck on
    /// the shared transcript, reducing R1CS validity of `blocks` to two
    /// evaluation claims on the committed packed witness `q_pkd`. (The
    /// statement is already transcript-bound: the embedding protocol seeds
    /// with the circuit family digest and announces the count.) Returns:
    /// - `z_packed`: the regenerated packed witness the PCS later opens against;
    /// - the [`ReducedClaims`] `(ab, c)` on `q_pkd`, with ring-switch weights.
    ///
    /// Does NOT open the PCS; the caller discharges the returned claims in the
    /// one stacked opening (`lean_vm`'s `pcs::open`, or
    /// [`Self::prove_validity_stacked`] for a standalone roundtrip).
    pub fn prove_reduction<O>(
        &self,
        blocks: &[Compression],
        ps: &mut fiat_shamir::transcript::ProverState<O>,
    ) -> (Vec<F192>, ReducedClaims) {
        assert_eq!(blocks.len(), self.n_blocks);
        let n_log = self.n_blocks_log();
        let (z_packed, a_packed_words, b_packed_words, z_packed_lincheck) =
            generate_witness_with_ab_packed_and_lincheck(blocks, n_log);

        // No bind_statement here: the embedding protocol (leanVM-b) seeds its
        // transcript with the circuit-FAMILY digest and binds the instance
        // count and commitment root before any challenge, so the statement is
        // already fully transcript-bound.

        let padding = crate::zerocheck::PaddingSpec {
            k_log: self.r1cs.k_log,
            useful_bits_per_block: self.r1cs.useful_bits,
        };
        let (zc_claim, s_hat_v_c) = {
            let a_packed = packed_128_bytes(&a_packed_words);
            let b_packed = packed_128_bytes(&b_packed_words);
            let c_packed = packed_128_bytes(&z_packed);
            crate::zerocheck::prove_packed_padded_capture_s_hat_v_c(
                &a_packed,
                &b_packed,
                &c_packed,
                self.r1cs.m,
                &padding,
                ps,
            )
        };

        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = crate::lincheck::QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
        };
        let (lc_claim, z_vec_pre) = crate::lincheck::prove_padded_capture_z_vec(
            &z_packed_lincheck,
            self.r1cs.m,
            self.r1cs.k_log,
            self.r1cs.k_skip,
            self.r1cs.useful_bits,
            self.r1cs.csc_lincheck_circuit(),
            &x_ab,
            ps,
        );

        let ab = crate::proof::ZClaim {
            point: crate::lincheck::QuirkyPoint {
                z_skip: lc_claim.r_inner_skip,
                x_inner_rest: lc_claim.r_inner_rest.clone(),
                x_outer: x_ab.x_outer.clone(),
            },
            value: lc_claim.w,
        };
        let c = crate::proof::ZClaim {
            point: crate::lincheck::QuirkyPoint {
                z_skip: zc_claim.z,
                x_inner_rest: zc_claim.r_rest[..inner_rest_len].to_vec(),
                x_outer: zc_claim.r_rest[inner_rest_len..].to_vec(),
            },
            value: zc_claim.c_eval,
        };
        let s_hat_v_ab = if self.r1cs.k_log >= pcs::pack_k::LOG_PACKING_K {
            Some(pcs::ring_switch_k::s_hat_v_from_z_vec(
                &z_vec_pre,
                &lc_claim.r_inner_rest,
            ))
        } else {
            None
        };

        let reduced = ReducedClaims {
            ab: WitnessClaim {
                claim: ab,
                s_hat_v: s_hat_v_ab,
            },
            c: WitnessClaim {
                claim: c,
                s_hat_v: Some(s_hat_v_c),
            },
        };
        (z_packed, reduced)
    }

    /// **Flock reduction (verifier).** Replay the SHA-256 zerocheck and
    /// lincheck straight off the shared transcript stream, recovering the two
    /// `(ab, c)` evaluation claims on the committed witness `q_pkd`. Mirror of
    /// [`Self::prove_reduction`]; the PCS then discharges the returned claims.
    pub fn verify_reduction<O>(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_, O>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        // Mirror of prove_reduction: the statement is bound by the embedding
        // protocol's seed (family digest) + announced count + commitment root.

        let zc_claim = crate::zerocheck::verify(self.r1cs.m, vs).map_err(verifier::VerifyError::Zerocheck)?;
        let inner_rest_len = self.r1cs.k_log - self.r1cs.k_skip;
        let x_ab = crate::lincheck::QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
            x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
        };
        // Replay the same CSC-backed lincheck used by the prover.
        let lc_claim = crate::lincheck::verify(
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

        let ab = crate::proof::ZClaim {
            point: crate::lincheck::QuirkyPoint {
                z_skip: lc_claim.r_inner_skip,
                x_inner_rest: lc_claim.r_inner_rest.clone(),
                x_outer: x_ab.x_outer.clone(),
            },
            value: lc_claim.w,
        };
        let c = crate::proof::ZClaim {
            point: crate::lincheck::QuirkyPoint {
                z_skip: zc_claim.z,
                x_inner_rest: zc_claim.r_rest[..inner_rest_len].to_vec(),
                x_outer: zc_claim.r_rest[inner_rest_len..].to_vec(),
            },
            value: zc_claim.c_eval,
        };
        Ok(ReductionReplay {
            ab,
            c,
            zc_claim,
            lc_claim,
        })
    }
}
