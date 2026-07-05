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

TLDR: no, but a 1.8x per-multiply residue remains on E x E after our best
rewrite, and it matters only in the phases that are pure E x E (GKR).

| ns/op, lat / tput | day one | after rewrite | GHASH ref |
|---|---|---|---|
| E x E | 10.19 / 3.41 | 6.91 / **1.28** | 5.89 / 0.70 |
| K x E (`mul_base`) | 6.57 / 1.16 | 5.14 / **0.70** | = one GHASH mul |
| K x K | 4.85 / 0.64 | 4.82 / **0.50** | |

- PMULL counts favor the tower (5 vs 5-6); the day-one gap was overhead
  (shift-XOR folds, GPR crossings), now fixed with PMULL folds and fully
  vector-resident kernels.
- The residue is structural granularity: a two-limb tower reduces at 64-bit
  boundaries (three sub-folds per product, one behind the y^2 = y + x^61
  multiply) where GHASH folds a 256-bit product once by one sparse
  constant. Plus twenty years of AES-GCM tuning on GHASH's side.
- mul_base ended at exact per-op parity with a full GHASH multiply, so the
  mixed-product phases cost the same per element as the old design's full
  multiplies, over more elements.
- What GHASH cannot offer at any speed: addressable 64-bit words (half the
  committed bits), 1-PMULL trace arithmetic, and the subfield structure the
  single ring switch needs. Next identified kernel lever: deferred-reduction
  accumulators (parity with GHASH's F256Unreduced).

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
| 2^24 (2 MiB) | 3.4 Gbit/s | 3.0 Gbit/s | 0.88x |
| 2^26 (8 MiB) | 7.6 | 6.5 | 0.86x |
| 2^28 (32 MiB) | 13.7 | 11.1 | 0.81x |
| 2^30 (128 MiB) | 18.0 | 14.3 | 0.79x |

Units: gigaBITS per second; 18 Gbit/s is 2.2 GiB/s of witness. That rate is
real and mundane: at 2^30 the commit (39 ms) is a bandwidth-bound NTT over
the 256 MiB rate-1/2 codeword (~18 ms) plus multi-threaded BLAKE3 Merkle
over the same bytes (~21 ms, about 1.2 GB/s per core across 10 threads),
and the open (21 ms) is one folding pass over the 128 MiB witness plus
geometrically shrinking levels and a few hundred query paths. Throughput
grows with size because fixed costs amortize; it would plateau once the
codeword outgrows the last-level cache's streaming advantage.

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
