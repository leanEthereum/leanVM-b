# Replacing BLAKE2s with SHA-3

Working plan for the `sha3` branch, forked from `main` at `e2d18a7d`. Scope is a full swap of the one hash function, its VM opcode, its GF(2) circuit and all three verifiers: about 80 files across 9 crates.

## Decisions

Settled before implementation, and not revisited below:

| Question | Decision |
| --- | --- |
| Variant | **SHA3-256**, FIPS 202: Keccak-f[1600], 24 rounds, rate 1088 b (136 B), capacity 512 b |
| Padding | **Byte-exact FIPS 202**: `pad10*1` with the `0x06` domain byte, interoperable with any SHA3-256 |
| Block dimension | `K_LOG = 16`, forced by the AND count |
| Merkle arity | **Binary**, unchanged. 4-ary is a separate follow-up |
| Scope | The whole migration, phases 1 to 10 |

The circuit encodes the **raw Keccak-f[1600] permutation**, not the sponge. Padding and absorption live above it: in Rust natively, and as zkDSL constants in the guest. For a fixed-length input the pad is a constant bit pattern, so a 64-byte hash is still exactly one permutation and the `0x06` and `0x80` bytes cost nothing in-circuit.

## TL;DR

- **Standard SHA-3 costs `2^16` flock rows per permutation, and that is a hard floor.** The multiplicative complexity of Keccak's `chi` is exactly 5 AND gates per 5-bit row (proof below), so 24 rounds is 38,400 AND rows and no pinning or encoding trick moves it. This is accepted, not a fork: the 12-round variants are recorded in section 1 for context only.
- **Keccak wins on wide absorbs and loses on narrow ones.** Fiat-Shamir currently spends one compression to bind 192 bits, while the sponge binds 1088 per permutation, so transcript work needs 5.7x fewer hash calls. But one XMSS verification is 99 WOTS chain steps of 48 bytes each, which no rate can help, and that workload goes to roughly **3.8x the flock rows**. This cost is accepted; 4-ary Merkle remains the follow-up lever against it.
- **The engineering is the `sha2` migration plus four new problems.** Commit `25b2c531` is a good template for the mechanical part, but Keccak changes the primitive's shape: `FiatShamirState` becomes a real sponge (a protocol redesign, and the soundness-relevant part), the hash opcode goes from 18 to 50 value lanes, flock loses every adder gadget, and no pins are needed at all.
- **Sequencing:** phases 1 and 2 are additive and sit alongside BLAKE2s, so the tree stays green through them. Phases 3 to 9 change the protocol and land together, because the Rust verifier, the Python verifier and the recursion guest have to agree at every intermediate state. Phase 10 is docs and benchmarks.

## 1. Pick the variant first

Keccak's only nonlinear layer is `chi`, and its cost is not negotiable. Each five-bit row computes `y_i = x_i + x_{i+2} + x_{i+1}*x_{i+2}` over GF(2), so the five outputs have quadratic parts equal to five distinct degree-two monomials, which are linearly independent. Four AND gates produce products of affine forms spanning at most a four-dimensional space of quadratic forms, so four cannot cover five independent ones. The multiplicative complexity of `chi_5` is exactly 5.

That fixes 1,600 AND rows per round: 320 rows for each of the five sheets across 64 bit positions. This is a real difference from SHA-256, where choosing which words to materialize was the whole design problem. Here the only free parameter is the round count.

One flock instance is one permutation. Committed slots are the AND wires plus the free input state, the pinned output state and the constant wire, so the block dimension follows directly.

| Variant | Rounds | AND rows | Useful | Block | Absorb | Rows/bit | 64-byte hash |
| --- | --- | --- | --- | --- | --- | --- | --- |
| BLAKE2s (today, on main) | 10 | 14,720 | 16,000 | `2^14` | 512 b | 32.0 | 16,384 |
| SHA-256 (the `sha2` branch) | 64 | 22,456 | 29,113 | `2^15` | 512 b | 64.0 | 32,768 |
| SHA3-256 (Keccak-f[1600], c=512) | 24 | 38,400 | 41,601 | `2^16` | 1088 b | 60.2 | 65,536 |
| SHAKE128 (Keccak-f[1600], c=256) | 24 | 38,400 | 41,601 | `2^16` | 1344 b | 48.8 | 65,536 |
| TurboSHAKE256 (Keccak-p[1600,12]) | 12 | 19,200 | 22,401 | `2^15` | 1088 b | 30.1 | 32,768 |
| TurboSHAKE128 (Keccak-p[1600,12]) | 12 | 19,200 | 22,401 | `2^15` | 1344 b | 24.4 | 32,768 |

Absorb width is the sponge rate, or the message block for the two Merkle-Damgard schemes. Rows per bit is the flock cost of absorbing one bit at full rate.

**Chosen: SHA3-256, the first 24-round row.** The 12-round rows are kept in the table only to record what was given up. `N_ROUNDS` stays a named constant because that is good structure, not because the value is still open.

## 2. Cost model: wide absorbs win, narrow ones lose

The rate is the whole story. Today the Fiat-Shamir chain spends one 64-byte compression to absorb a single `F192` scalar, which is three `F64` limbs plus a domain tag in the fourth lane. That is 192 bits of transcript per hash. A sponge absorbs a full rate block per permutation: 1088 bits for SHA3-256, 1344 for SHAKE128 and TurboSHAKE128.

So transcript absorption needs 5.7x to 7x fewer hash calls. Even at four times the rows per call, SHA3-256 comes out ahead on that workload. Narrow hashing gets the opposite treatment: a WOTS chain step is 48 bytes and a Merkle parent is 64, both far under the rate, so they pay for a full permutation and use a fraction of it.

| Workload | Shape | BLAKE2s | SHA3-256 | TurboSHAKE128 |
| --- | --- | --- | --- | --- |
| Transcript absorb, per 1344 bits bound | wide | 7 hashes, 114,688 rows | 2 perms, 131,072 rows (1.14x) | 1 perm, 32,768 rows (0.29x) |
| Merkle parent, binary, 64 B | narrow | 1 hash, 16,384 rows | 1 perm, 65,536 rows (4.0x) | 1 perm, 32,768 rows (2.0x) |
| Merkle parent, 4-ary, 128 B | fits rate | 3 hashes, 49,152 rows | 1 perm, 65,536 rows (1.33x) | 1 perm, 32,768 rows (0.67x) |
| One XMSS verification | mostly narrow | 144 hashes, 2.36 M rows | 138 perms, 9.04 M rows (3.8x) | 138 perms, 4.52 M rows (1.9x) |

XMSS counts follow `crates/xmss/src/hash.rs`: 2 encoding blocks, 99 chain steps, 11 WOTS tips, 32 Merkle nodes. Under a sponge the encoding collapses to 1 permutation and the tips to about 6, both because they exceed 64 bytes, while the chains and the path do not move.

**The concern, stated once.** XMSS aggregation is the repo's primary goal and it is dominated by 48-byte chain steps that no rate can help. Standard SHA-3 makes that workload roughly 3.8x more expensive in flock rows, and TurboSHAKE128 still makes it 1.9x. Recursion goes the other way and may come out ahead. Both are worth building, but the leaf benchmark is the number that decides whether the migration ships or stays a measurement.

Two things soften it:

- **4-ary Merkle becomes free.** Four 32-byte children are 1024 bits, inside either rate, so a 4-ary node is one permutation. That halves path lengths in the PCS tree, the XMSS authentication path and the guest's Merkle work. There is already an `origin/4-ary-Merkle-XMSS` branch to draw on.
- **The native side gets faster.** This machine reports `FEAT_SHA3`, so `BCAX` computes `chi` in one instruction and `EOR3`, `RAX1` and `XAR` cover `theta` and `rho`. Witness generation, the PCS Merkle tree and the grinding loop all benefit.

## 3. What the sha2 migration did not have to solve

BLAKE2s and SHA-256 are the same shape: a 64-byte block, a 256-bit chaining value, one compression per opcode. That let commit `25b2c531` be a large but mechanical swap. Keccak is a 1600-bit permutation in sponge mode, which touches four things the `sha2` branch left alone.

- **The Fiat-Shamir state stops being 256 bits.** `FiatShamirState` is a Merkle-Damgard chaining value today, domain-separated by putting a tag in lane 3 of every block. A sponge carries 1600 bits, absorbs into the rate at a position, and separates domains by framing rather than per-block tags. This is a protocol redesign, not a substitution, and it is the soundness-relevant part of the migration.
- **The opcode gets wide.** `Blake2sTable` carries 18 value lanes over 8 cells. A permutation opcode carries 25 lanes in and 25 out, so 50 value lanes over 26 cells, all routed to `q_flock` as virtual columns. Table rows drop because there are fewer hash calls, but per-row bus flushes nearly triple.
- **flock loses its adder gadgets entirely.** Keccak has no modular addition, so `walk_add`, `walk_add3_fused` and both transposes disappear, along with `add_carry_parts` and `add3_fused_parts` in `witness.rs`. What is left is `walk_and`, `walk_pin`, their transposes, and XOR/rotate helpers on 64-bit lanes. `gf2.rs` gets substantially smaller.
- **No pins are needed.** Every `chi` output is an AND wire and therefore committed by construction, so the affine depth between committed wires is one `theta` layer, about 11 terms. The pin families that dominate the SHA-256 layout have no analogue here. The only lin-id rows are the output state.

Two things get easier. The opcode has no metadata immediate, since a permutation has no counter and no final-block flag, so `PINNED_T`, `PINNED_F0` and the `MD0`/`MD1` lanes all go away. And `R1CS_DIGEST` is now just a chosen constant mirrored in three places, since main no longer builds the matrices it used to be a hash of.

## 4. Phases

The grouping matters more than the numbering.

### Landing A: additive, independently testable

Phases 1 and 2 can live alongside BLAKE2s on the branch, which is what makes the cost model checkable before committing to the rest.

**Phase 1: native Keccak in `primitives`.** A new `sha3` module mirroring every surface `blake2s` exports, since the callers are written against that shape. Keep the length-prefixed trick: absorb the length as the first rate block so `iv_for_len(n)` is a compile-time constant state and an n-byte hash of known length is exactly `ceil(n/rate)` permutations, with no `pad10*1` and no domain byte to reproduce in-circuit.

- Files: new `crates/primitives/src/sha3.rs`, new `crates/primitives/tests/sha3_bench.rs`, `crates/primitives/src/lib.rs`.
- Surfaces: `permute`, `hash`, `Hasher`, `hash_many::<LEN>`, `hash_many_dyn{,_from_state}`, `hash_from_state`, `zero_prefix_state`, `LANES`. Two backends: aarch64 on the `FEAT_SHA3` instructions, and a lane-parallel AVX-512 path for x86.
- Exit: NIST known-answer vectors pass; `sha3_bench` reports 64-byte and batched throughput next to the BLAKE2s numbers.

**Phase 2: the flock circuit.** A new `flock::sha3` built on the walk API main just landed, so the circuit is described twice and no matrix is ever materialized. `WireWord` becomes a 64-lane array and the state is a 5x5 grid of them; `forward_walk` threads `theta`, `rho`, `pi`, `chi`, `iota` and `marginal_walk_side` is its reverse-mode transpose.

- Files: new `crates/flock/src/sha3.rs`, new `crates/flock/tests/sha3_batch.rs`, plus `gf2.rs` (drop the adders), `lib.rs`, `witness.rs`, `reduction_tests.rs`.
- Port the test set the `sha2` branch settled on: layout tiling, witness matches the native permutation, honest witness satisfies, mutated witness fails, constant-wire pin rejects all-zero, and the transpose check that pins the backward walk to the forward one.
- Exit: `sha3_reduction_roundtrip` and the tamper tests pass; `sha3_batch_prove_verify` gives real prove and verify times per permutation, which is the number the decision in section 1 turns on.

### Landing B: one commit, all three verifiers

Phases 3 to 9 change the protocol, so they land together or nothing verifies.

**Phase 3: Fiat-Shamir as a real sponge.** The highest-risk phase and the one that pays for the migration. Replace the 256-bit chaining value with a 1600-bit state plus a rate position. Absorb `F192` limbs into successive rate lanes and permute only when the rate fills; squeeze reads rate lanes and permutes on exhaustion. Domain separation has to be redesigned, since the per-block tag lane does not survive: scalars, byte strings and squeezes need explicit framing. Note that in the guest the transcript walk is fully unrolled and every rate boundary is a compile-time constant, so position tracking costs nothing in-circuit.

- Files: `crates/fiat_shamir/src/{lib,transcript,merkle}.rs`, `crates/lean_vm/src/vmhash.rs`.
- Exit: the PoW grind predicate, `state()` and the carried recursion state all have defined sponge equivalents, written down before any caller is touched.

**Phase 4: the VM opcode and its table.** `Op::Keccak` reading 13 cells of state and writing 13, no metadata immediate. New table columns, bus flushes routed to `q_flock`, and the fixed slot correspondence between table value lanes and circuit witness positions. `fs_seed` takes a fresh label and a fresh `R1CS_DIGEST`. At `K_LOG = 16` the `q_flock` stack region doubles per instance, so check `layout.rs` and the `MU_MIN` floor.

- Files: `crates/lean_vm/src/cpu/{isa,execute,filler,trace,layout,mod}.rs`, `crates/lean_vm/src/tables.rs`, rename `blake2s_flock.rs` to `sha3_flock.rs`, `crates/lean_vm/src/{lib,pcs,leaf,witness}.rs`.
- Exit: `cargo test -p lean_vm --release` green, including the Python verifier pin.

**Phase 5: compiler and zkDSL.** The `keccak(...)` builtin, its lowering, and the CSE and filler paths that special-case the hash opcode. The signature changes shape: state in, state out, no counter or final flag.

- Files: `crates/lean_compiler/snark_lib.py`, `zkDSL.md`, `src/{ast,ir,lower,cse,filler,lib}.rs`, `tests/programs/*.py`, `tests/suite/*`.
- Exit: the compiler suite green.

**Phase 6: PCS Merkle tree.** Leaf hashing moves to `sha3::hash_many`, `BATCH_LEAVES` follows the new `LANES`, and the zero-prefix optimization needs its sponge equivalent. Decide arity here: the rate makes 4-ary natural and it is the main lever against the narrow-hash regression.

- Files: `crates/pcs/src/{merkle,whir,ring_switch}.rs`.
- Exit: `pcs_throughput` and the WHIR round trip green at both rates.

**Phase 7: XMSS.** `tweak_hash` over the new hash, then recount. Update the standalone spec to match.

- Files: `crates/xmss/src/{hash,lib,wots,xmss}.rs`, `doc/xmss/`.
- Exit: XMSS sign and verify round trip; the per-verification permutation count recorded in the module docs.

**Phase 8: the recursion guest.** The largest single file to touch, and where the sponge redesign is most expensive: about 47 hash call sites across the Fiat-Shamir helpers, Merkle verification, the WOTS walk, the leaf hasher and the statement digest. Every one is a fixed-size unrolled block, so each has to be re-derived against the new rate.

- Files: `crates/rec_aggregation/guests/aggregate.py`, `crates/rec_aggregation/src/{aggregation,hash_chain,fibonacci,signers_cache}.rs`.
- Exit: `aggregate_two_to_one`, then the ignored adversarial set: `aggregate_statement_binds`, `aggregate_hints_bind`, `aggregate_rejects_a_bad_signature`, `aggregate_three_levels`.

**Phase 9: Python verifier.** Mirror of phases 3, 4 and 6: the sponge, the new `sha3_row_values` forward walk with its layout constants, and the digest. It is pinned by a Rust test, so it is also the cheapest place to catch a protocol drift.

- Files: `python-verifier/verifier.py`.
- Exit: `lean_vm/tests/verifiers/python_verifier.rs` green, which is the gate on the whole landing.

### Landing C: documentation and numbers

**Phase 10: specification and benchmarks.** Annex C's circuit section, the ISA and instruction-table sections, the end-to-end protocol, the macros and the bibliography. Then rerun both headline benchmarks and replace the README block, which is currently carrying BLAKE2s numbers.

- Files: `doc/leanvm/body/{01,02,04,07,08,09,c}*.tex`, `preamble/macros.tex`, `refs.bib`, `AGENTS.md`, `README.md`.
- Exit: `latexmk` clean, and the two benchmark commands in AGENTS.md rerun at `--repeat 3`.

## 5. Risks

| Severity | Risk |
| --- | --- |
| High | **The leaf benchmark regresses and does not come back.** The XMSS chain steps are irreducibly narrow. If the 3.8x row model holds and 12 rounds is unacceptable, there is no third lever, and the honest outcome is that the branch stays a measurement. Phase 2's exit criterion exists to find this out before phases 3 to 9 are written. |
| High | **Sponge domain separation is a soundness change.** The current scheme is easy to reason about because every compression carries its role in one lane. Rate-based framing has more ways to be subtly wrong, and a collision between a scalar absorb and a byte-string absorb would not show up in any round-trip test. This wants written justification, not just passing tests. |
| Medium | **50 value lanes on the bus.** The hash table's per-row flush cost nearly triples. Fewer rows should more than pay for it, but the bus and the memory argument are where that assumption could fail. Measurable at the end of phase 4. |
| Medium | **Padding waste at `2^16`.** 41,601 useful bits in a 65,536-bit block is 63% utilization, against 89% for SHA-256 today. Zerocheck handles the padding, but the committed witness carries it, so the PCS pays for the empty slots. |
| Low | **The guest's log-size fixed point moves.** `unified_guest` compiles to a fixed point on its own size, and both the hash count and the per-hash instruction count change. Expect a couple of iterations, not a redesign, and watch `Program::min_log_committed` against the `MU_MIN` floor. |
| Low | **Variable-length in-circuit hashing.** Fixed-length pads are constants and cost nothing, but any guest site hashing a runtime-length message has to constrain `pad10*1` itself. Audit the guest for such a site; there should be none. |

## 6. Order of work

Phases 1 and 2 are additive: the new modules sit next to `blake2s` and the tree stays green, so the leaf cost becomes measurable before the protocol moves. Everything after that is the switch.

Sizing comes from `crates/flock/src/blake2s.rs`, `crates/xmss/src/hash.rs` and `crates/fiat_shamir/src/lib.rs` on main at `e2d18a7d`. Row counts are exact; workload ratios are modelled and want confirming against a benchmark.
