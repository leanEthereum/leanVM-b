# 64-bit transition: performance report

Where the K-design stands against `main` (the GHASH F128 design), why proving
is currently slower despite doing less work, and what is being done about it.
All numbers: XMSS aggregation, N = 1024, `RAYON_NUM_THREADS=10`, M-series.

## Scoreboard

| metric | main (F128) | transition, first port | now |
|---|---|---|---|
| cycles / XMSS | 3472.7 | 4692.6 | **3200.8** |
| throughput | 229.6 XMSS/s | ~106 XMSS/s | **180.2 XMSS/s** |
| proof size | 778.3 KiB | 666.0 KiB | **666.0 KiB** |
| verification | 7.6 ms | 11.4 ms | ~10 ms |
| committed bits | 2^33.96 | 2^33.23 | **2^33.23** |

The program does less work (7% fewer VM cycles), commits 40% fewer bits, and
produces a 14% smaller proof. The wall-clock deficit is concentrated in the
prover's extension-field arithmetic, and most of what looked like a design
regression turned out to be implementation debt. The path from 106 to 180
XMSS/s was four fixes; the remaining 22% gap is field-kernel quality, being
addressed now.

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

No. It is currently faster in our code for implementation reasons, measured
precisely in `field_bench` (latency = serial dependency chain; throughput =
8 independent chains, ns per multiply):

| op | PMULLs | latency | throughput |
|---|---|---|---|
| F128 GHASH mul | 6 | 5.89 | **0.70** |
| F128T tower mul (E x E) | 5 | 10.19 | 3.41 |
| F128T mul2, paired | 8 / pair | 6.17 | 2.18 |
| F64 mul (K x K) | 1 | 4.85 | 0.64 |
| F128T mul_base (K x E) | 2 | 6.57 | 1.16 |

The smoking gun is the F64 row: a one-PMULL 64-bit multiply merely *ties* the
six-PMULL GHASH multiply on throughput. That cannot be explained by the math;
the multiply counts favor the tower. The overhead is in everything around the
PMULLs:

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

Add to this that the GHASH kernel inherits two decades of AES-GCM tuning
while the tower kernels are day-one code. A careful rewrite (PMULL-based
folds, fully vector-resident) should bring E x E within ~1.5x of GHASH and
make K x K and mul_base decisively cheaper than a GHASH multiply, which is
the entire premise of the transition.

### What the tower buys that GHASH cannot offer

GHASH F128 has no 64-bit subfield you can address in its representation:
committed data must be 128-bit words and every product is a full multiply.
The tower gives three cheaper operation classes that dominate the system:

- K x K at 1 PMULL: all trace arithmetic (MUL_NATIVE, address chains).
- K x E at 2 PMULL (`mul_base`): every sumcheck round 0, leaf fingerprints,
  base-field NTT butterflies against E-folded codewords.
- Committed words at 64 bits: half the committed bits for the same data.

The phases that stay pure E x E (the GKR product tree, later sumcheck rounds)
pay the tower tax, currently 1.65x in GKR. That tax is what the kernel
rewrite attacks.

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
| commit | 736 ms | 968 ms | F64 NTT extra layer at equal bytes |
| bus: leaves | | 87 ms | mul_base, cheap |
| bus: GKR | ~700 ms | 1321 ms | pure E x E, the tower tax |
| bus: decompose | | 40 ms | |
| constraints | 240 ms | 267 ms | |
| flock reduction | ~850 ms | 838 ms | same GHASH code both sides |
| stack open | ~550 ms | 1348 ms | 2x positions + E arithmetic |
| **total prove** | **4.46 s** | **5.68 s** | |

## What remains, ranked

1. **Field kernels** (in flight): PMULL-based folds and vector-resident
   scheduling for F64 and F128T. Targets: K x K <= 0.4 ns/op, mul_base <= 0.7,
   E x E <= 1.5. Feeds directly into GKR (1.32 s), the opening sumchecks, and
   the NTT.
2. **GKR structure**: fusing the even/odd folds and reusing layer buffers
   (memory-bound at the top layers). The 2-wide mul2 kernel was built,
   measured in place, and honestly reverted: those loops are port-bound, not
   latency-bound.
3. **Commit**: the F64 NTT's extra layer costs ~230 ms at equal bytes; a
   pmull-fold butterfly may claw some back.
4. **Structural floor**: the stacked opening handles 2^28 positions instead
   of 2^27 (E-valued weight vector over twice the words). This is inherent
   to committing K words; it is paid back by the 40% bit reduction in
   commit/query bytes and the smaller proof.
5. **VM cycles**: walk-call inlining in the XMSS dispatch arms would save
   ~600 cycles/sig at the cost of doubling the bytecode (2^14 to 2^15).

## Verdict

The transition delivers on its statement-level promises today: fewer cycles,
40% fewer committed bits, 14% smaller proofs, one ring switch, 64-bit machine
words. The prover wall-clock deficit is not a property of the tower design:
it is one part implementation maturity of brand-new field kernels against the
most-optimized binary-field kernel in existence, and one part the 2x position
count in the E-valued phases, which the halved bit volume was always going to
trade against. The kernel rewrite should close most of the remaining 22%.
