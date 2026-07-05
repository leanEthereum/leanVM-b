# 64-bit transition: performance report

Where the K-design stands against `main` (the GHASH F128 design), why proving
is currently slower despite doing less work, and what is being done about it.
All numbers: XMSS aggregation, N = 1024, `RAYON_NUM_THREADS=10`, M-series.

## Scoreboard

| metric | main (F128) | transition, first port | now |
|---|---|---|---|
| cycles / XMSS | 3472.7 | 4692.6 | **3200.8** |
| throughput | 229.6 XMSS/s | ~106 XMSS/s | **210.5 XMSS/s** |
| proof size | 778.3 KiB | 666.0 KiB | **666.0 KiB** |
| verification | 7.6 ms | 11.4 ms | ~10 ms |
| committed bits | 2^33.96 | 2^33.23 | **2^33.23** |

The program does less work (7% fewer VM cycles), commits 40% fewer bits, and
produces a 14% smaller proof. Most of what looked like a design regression
was implementation debt (memory cliffs, serial builds, day-one field
kernels), all since fixed. The remaining ~9% deficit has three structural
sources, quantified below: opening cost scales with element count rather
than bits, pure E x E phases pay a ~1.8x per-op tax against GHASH, and the
power-of-two padding doubles the opened positions at this instance size.

## Why "we commit more elements than main"

The committed witness grew from 2^26.96 to 2^27.23 *elements*, but an element
halved (8 bytes instead of 16), so the committed *bits* fell by 40%. The
element growth has three sources:

1. **Memory table.** Every 256-bit value (digest, chain tip, tweak) spans
   4 cells instead of 2, so the program's heap footprint in cells roughly
   doubles, and the memory table with it. Dominant driver.
2. **DEREF rows +47%/XMSS.** BLAKE3 operands bridge 4 cells per operand
   through the frame instead of 2 (12 DEREFs per hash instead of 6).
3. **BLAKE3 table width.** 12 memory-bus operations per row instead of 6.

Commitment cost tracks bits, not elements: encoding bytes, Merkle bytes and
query-opening bytes all shrank. The proof-size drop is this effect.

## The field question: is GHASH F128 fundamentally faster than the tower?

Mostly no, but a measurable residue remains. `field_bench` numbers (latency
= serial dependency chain; throughput = 8 independent chains, ns/multiply),
before and after the kernel rewrite that made the tower vector-resident with
PMULL-based folds:

| op | PMULLs | day-one lat/tput | rewritten lat/tput |
|---|---|---|---|
| F128 GHASH mul (reference) | 5-6 | 5.89 / 0.70 | unchanged |
| F128T tower mul (E x E) | 5 | 10.19 / 3.41 | **6.91 / 1.28** |
| F128T mul2, paired | 8 / pair | 6.17 / 2.18 | 3.49 / 1.46 |
| F64 mul (K x K) | 1 | 4.85 / 0.64 | 4.82 / 0.50 |
| F128T mul_base (K x E) | 2 | 6.57 / 1.16 | **5.14 / 0.70** |

The day-one smoking gun was the F64 row: a one-PMULL 64-bit multiply merely
tying the GHASH multiply on throughput cannot be explained by math; the
overhead was everything around the PMULLs:

1. **Reduction strategy.** GHASH reduces once, at the end, with PMULL by the
   sparse constant 0x87, staying entirely inside the vector registers (about
   4 extra vector ops). Our K reduction uses a ~10-instruction shift-XOR fold
   chain, and the tower multiply performs three such reductions. Pure NEON
   port pressure.
2. **Register-domain crossings.** Our kernels extract 64-bit lanes to feed
   `vmull_p64` and reassemble results through general-purpose registers.
   Every crossing costs cycles and issue slots; GHASH-shaped code never
   leaves the vector file.
3. **A serial fold.** The tower reduction y^2 = y + x^61 has a *multiply*
   inside the reduction chain: reduce the high coefficient, multiply it by
   the constant, reduce again. GHASH's reduction is one shot. This is the
   only genuinely structural cost of the tower, and it affects latency
   (roughly 1.3x), not throughput.

The rewrite fixed (1) and (2): folds are now PMULL-based and the kernels
never leave the vector file; the tower's serial y-fold was even parallelized
(the x^61-shifted high product folds directly with per-word constants,
including x^128 mod P for the top word). What remains after all that is
E x E at 1.28 vs GHASH's 0.70 ns/op, a 1.8x residue whose causes are the
reduction granularity (a two-limb tower folds at 64-bit boundaries, three
sub-reductions per product, where GHASH folds a 256-bit product once by one
sparse constant) plus twenty years of AES-GCM kernel lineage on the other
side. mul_base landed at exact GHASH-mul parity per op (0.70): two PMULLs
of work, but the fold overhead eats the theoretical 3x. Deferred-reduction
accumulators (XOR unreduced Karatsuba triples, reduce once per sum, which
the GHASH pipeline already does via F256Unreduced) are the identified next
step for the accumulation-shaped loops and would close part of the residue.

### What the tower buys that GHASH cannot offer

GHASH F128 has no 64-bit subfield you can address in its representation:
committed data must be 128-bit words and every product is a full multiply.
The tower gives three cheaper operation classes that dominate the system:

- K x K at 1 PMULL: all trace arithmetic (MUL_NATIVE, address chains).
- K x E at 2 PMULL (`mul_base`): every sumcheck round 0, leaf fingerprints,
  base-field NTT butterflies against E-folded codewords.
- Committed words at 64 bits: half the committed bits for the same data.

The phases that stay pure E x E (the GKR product tree, later sumcheck
rounds) pay the residual tower tax: GKR runs 939 ms vs main's ~750 (was
1327 ms before the kernel rewrite).

## Where the original 2x wall-clock regression actually came from

Phase profiling against main found the slowdown was mostly *not* arithmetic:

| cause | cost | fix |
|---|---|---|
| `stack.to_vec()` per prove | 2.1 GB copy | prover borrows the witness |
| `vec![F128T::ZERO; 2^28]` | 4.3 GB zeroed single-threaded (custom structs miss the calloc fast path) | uninit alloc + parallel fill |
| paging from the two above | taxed every phase | gone with them |
| serial per-claim eq tables in the stacked opener | 2.4 s | parallel gamma-seeded builder + scratch reuse |
| serial suffix tensors in ring-switch prove | 0.5 s | parallel builder |
| bit-scan `fold_1b_rows_k` | 0.16 s | method-of-four-Russians kernel |
| serial claim decomposition | 0.3 s | parallel MLE evals, transcript order preserved |
| SET+MUL per constant heap index (compiler) | +1220 cycles/XMSS | fold constants into DEREF's beta immediate |

Every fix is transcript-byte-identical (hash-pinned proofs). Phase profile
now (`LEANVM_PROFILE=1`):

| phase | main | now | note |
|---|---|---|---|
| commit | 736 ms | 759 ms | same bytes; F64 NTT extra layer offsets the bit halving |
| bus (leaves+GKR+decompose) | 1095 ms | 1056 ms | GKR 939 is the E x E tax; decompose 36 |
| constraints | 240 ms | 223 ms | mixed round 0 wins |
| flock reduction | ~850 ms | 878 ms | same GHASH code both sides |
| stack open | ~550 ms | 1158 ms | 2x padded positions + E arithmetic + ring switch |
| **total prove** | **4.46 s** | **4.87 s** | 229.6 vs 210.5 XMSS/s |

## The PCS head to head, bits committed + opened per second

Same witness bits, Secure profile, commit + one opening (post kernel
rewrite). Commit is near parity (same bytes encoded and hashed); open is
~1.5x slower because opening cost scales with ELEMENT COUNT, not bits: the
eq-weight vector is one 16-byte E element per committed word whatever the
word width, so the 128-bit design amortizes each weight over 128 bits, ours
over 64.

| witness bits | GHASH F128 | F64 commit / E open | ratio |
|---|---|---|---|
| 2^24 | 3.4 Gbit/s | 3.0 Gbit/s | 0.88x |
| 2^26 | 7.6 | 6.5 | 0.86x |
| 2^28 | 13.7 | 11.1 | 0.81x |
| 2^30 | 18.0 | 14.3 | 0.79x |

Per machine WORD (the VM view: same data, half the bytes): 1.2x to 1.34x
FASTER, which is where the smaller proofs come from.

At the XMSS instance size the position count is further doubled by padding
luck: the real stack (2^27.23 words) pads to 2^28 (74% waste) while main's
2^26.96 pads to 2^27 (3% waste), so the stacked opening processes 2x the
positions for 1.2x the real data. Instance-size dependent, not structural.

## What remains, and what is deliberately left alone

Remaining field-specific levers (paused on request):

1. **Deferred-reduction accumulators for the tower** (parity with GHASH's
   F256Unreduced): would shave part of the E x E residue in GKR summands and
   the opening inner products.
2. **The padding sensitivity**: the 2x opened positions at this instance
   size is rounding luck; sizing programs against the padding boundary, or a
   non-power-of-two-friendly stacking, would reclaim most of the stack-open
   delta.

Deliberately NOT pursued, to keep the comparison against main honest: any
optimization that would speed main equally (witness generation, GKR
even/odd fold fusion, buffer reuse). Those are field-agnostic and would pad
our side of the ledger. For the record, the 2-wide mul2 kernel was built,
measured in place, and reverted: the GKR loops are port-bound, not
latency-bound.
The structural floor stays: the opening's per-word work (one E-valued
weight and one fold slot per committed word) is inherent to committing K
words, and is paid back by the 40% bit reduction in commit/query bytes and
the smaller proof. On the VM side, walk-call inlining in the XMSS dispatch
arms would save ~600 cycles/sig at the cost of doubling the bytecode.

## Verdict

The transition delivers on its statement-level promises today: fewer cycles,
40% fewer committed bits, 14% smaller proofs, one ring switch, 64-bit machine
words. The prover wall-clock deficit (9% at this instance size) decomposes
into: the opening's element-count scaling amplified by unlucky padding, the
1.8x E x E residue in GKR, and mul_base landing at parity per op instead of
its theoretical 3x advantage. None of these erase the design's statement:
the trade is bit volume against position count, and at other instance sizes
(or with the identified field-specific levers) it tilts the other way.
