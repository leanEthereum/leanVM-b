# Aggregation performance research handoff

Date: 2026-08-08

## Purpose

This branch preserves the exact measured seven-component research lineage and currently integrates upstream `main` at `ffc1a6af29f87ea428d1f889de4fd161537c9752`. The two-kernel performance campaign remains bound to the earlier integration at `e9cd16d49ef33909d9732778451ec73fbbedfd4a`. It is intended for technical review and current-source reproduction. It is not proposed as a merge-ready production patch.

## Source identities

| Role | Commit |
|---|---|
| Measured upstream freeze | `84fbd3ef49573537950f83c7ff66fd489476ca5d` |
| Six-component measured candidate | `b61a0ee64a9e5f41c368f937c56cdbb74fd3908b` |
| Seven-component measured candidate | `256928f9127c812749e40b08b4cf9744185c6b61` |
| Hardened L0 policy | `7be45deb92135c615dee0aaa4b294390b2de6902` |
| L0 boundary tests | `a2c10248d2b38c4e1381687b7e193eca081f612c` |
| Upstream integrated for the two-kernel campaign | `e9cd16d49ef33909d9732778451ec73fbbedfd4a` |
| Measured-source integration merge | `ae08017b89fdc03bfa0af31d31b08bf3c11eaa9d` |
| Current-source two-kernel measured candidate | `a5477b369ee44ef7aea91b0799f7b920b349632f` |
| Current upstream integration | `ffc1a6af29f87ea428d1f889de4fd161537c9752` |

The earlier six-component all-off/on campaign binds to `b61a0ee`; the incremental L0/seven-component campaign binds to `256928f`. Neither binds to the integration merge. The integration merge initially established source compatibility and test acceptance only. The separate current-source campaign described below binds to descendant `a5477b3` and measures only the two additional kernels.

## Accepted stack

1. Direct fold-6 for stacked opening.
2. Uninitialized GKR fold output with complete-write tests.
3. Uninitialized Bus leaf output with canonical-layout checks.
4. Quaternary Bus leaf capacity.
5. Quaternary retained GKR-layer capacity.
6. AVX-512 Bus MLE pure-extension folds on eligible x86-64 builds.
7. Narrow L0 induction dispatch to the existing exact transposed-NTT path for inverse-rate log 2, 113 queries and columns 19 through 21.

The first six mechanisms retain literal replay selectors because the retained campaigns compared enabled and disabled modes in the same binary. The L0 policy is default-on only for its measured family, preserves the inherited heuristic elsewhere and retains a fail-closed force-dense replay hook. The branch also retains the measurement seam used to produce fixtures, durable proof artifacts and phase events.

## Measured result

The retained full-system campaigns ran on an AMD EPYC 9354 Zen 4 host with 15 workers, 85.4 GiB available memory, zero swap and `pclmulqdq`, AVX2, VPCLMULQDQ, AVX-512F and AVX-512VL. The canonical child workload was 8 hashes and 64,000 iterations per child, with outer inverse-rate log 2.

| Comparison | Topology | Outer prove | Process wall | Peak physical memory |
|---|---:|---:|---:|---:|
| Six components versus all off | N2 | -30.91% | -20.72% | -22.98% |
| Six components versus all off | N8 | -31.87% | -26.85% | -32.44% |
| L0 NTT versus dense on the six-component stack | N2 | -7.07% | -3.51% | -2.48% |
| L0 NTT versus dense on the six-component stack | N8 | -6.51% | -4.46% | -3.27% |

The incremental L0 induction span fell 78.02% at N2 and 74.10% at N8. After all seven components, the N2 median phase cluster was Bus 0.687050 s, PCS opening 0.527055 s, constraints 0.518037 s and Flock reduction 0.336672 s. At N8, Bus led six of eight runs and PCS led two. The result moves the previously dominant PCS bottleneck; it does not establish that the complete aggregation system meets an agreed production budget.

All 142 retained proofs were byte-identical within topology and passed the unchanged inspection path. The canonical artifacts were 229,588 bytes for N2, 240,292 bytes for N4 and 258,204 bytes for N8.

## Current-source validation

The following passed locally on an Apple M4 Pro, but those local logs are not part of the sealed evidence pack:

- `cargo testall`: 293 passed, 0 failed and 9 ignored, including doctests.
- `cargo test --release --workspace --all-features`: 293 passed, 0 failed and 9 ignored, including doctests.
- `cargo clippyall`.
- `cargo fmt --all -- --check`.
- `cargo docall`.

The AVX-512 component is not selected on this Apple host. The sealed regression receipt is the Linux run on exact measured commit `a5477b3`: `cargo testall` passed 293 tests with 0 failures and 10 ignored tests, including doctests; Clippy, formatting and documentation also passed. GitHub reported no CI checks for PR #5 when this disclosure was prepared.

After integrating upstream `f7b4330`, the same unsealed M4 host passed `cargo testall`, `cargo test --release --workspace --all-features`, `cargo clippyall`, `cargo fmt --all -- --check`, `cargo docall`, Ruff formatting and lint checks for the Python verifier, and the complete LaTeX build. A forced `LEANVM_PCS_DIRECT_FOLD6=1` run passed both `recursion_2to1` variants and confirmed direct-fold6 selection on production-shaped openings under the new PCS batching protocol. The ignored `recursion_soundness_binds` adversarial suite also passed with direct-fold6 forced. These are compatibility and soundness-regression checks, not a replacement performance campaign.

After integrating upstream `ffc1a6a`, the same unsealed M4 host again passed both complete release suites with zero failures, Clippy, formatting, documentation, Ruff, the LaTeX build, the native and mixed 2-to-1 recursion tests, and the ignored `recursion_soundness_binds` adversarial suite with direct-fold6 forced. A current canonical one-shot workload of two children, eight hashes and 64,000 iterations produced and verified a recursive proof. These checks establish compatibility only; they are not a performance campaign.

## Evidence boundary

The evidence pack contains raw run order, command and environment records, 25 ms process-memory samples, host samples, phase events, serialized proofs, inspection logs, fixtures, source bundles and campaign checksum manifests. Its root manifest names 2,137 files and has SHA-256 `b6ae60e665294629bfc9dc599ed44472cf38fef4b487553f9aba5464b13dcd71`. The pack is retained outside this source branch and can be transferred separately.

Before relabeling the earlier seven-component medians as a current-main result, rerun that complete comparison on this integration branch or a later descendant. Upstream commits after the old measured freeze changed the recursion guest, native recursion code and Python verifier. The two-kernel campaign below does not retroactively transfer the old seven-component percentages to the integrated head.

The 2026-08-08 integration of `f7b4330` also includes `53631e8`, which replaced the per-query equality challenge with one power-weight batching challenge per PCS level. The conflict resolution keeps that current transcript and verifier protocol while retaining the research timing spans, direct-fold path and hardened L0 induction selector. Consequently, serialized proof hashes and performance receipts from before `53631e8` remain evidence only for their named frozen commits. They are not current-head proof-byte or performance claims.

The later `ffc1a6a` integration replaces the Bus tuple's univariate power fingerprint with multilinear equality weights and aligns the bytecode deferred claim with those four fingerprint challenges. This changes the native, Python and recursive verifier transcript. The retained fixture and proof-artifact envelopes still use wire version 2, but that version identifies their encoding rather than protocol compatibility. Fixtures and artifacts produced before `ffc1a6a` must not be reused on the merged head; generate fresh inputs and outputs instead.

## Current-source two-kernel result

Commit `a5477b369ee44ef7aea91b0799f7b920b349632f` adds two replayable, default-off experiments on top of the integrated stack:

1. `LEANVM_CONSTRAINT_NODE_SKIP=1` evaluates one Boolean endpoint and the third interpolation node for each constraints sumcheck message. It derives the omitted endpoint from the running claim, with a separate exact branch for `zeta == 1` where the usual denominator vanishes.
2. `FLOCK_PACKED_128_PARALLEL=1` serializes the three live packed Flock witnesses in one parallel dispatch over disjoint, completely initialized output chunks. The legacy serial route remains the default.

Both overrides accept only literal `0` or `1` and fail closed otherwise. Unit tests establish byte-identical transcript streams, unchanged claims and acceptance by the unchanged verifier. The constraints test covers the parallel two-node reducer at `tau = 12`, including the exceptional `zeta == 1` recovery branch. The packed-copy tests cover empty, boundary and non-power-of-two lengths as well as the complete reduction transcript, and the helper's complete-write contract is enforced by a `[MaybeUninit<u8>; 16]` parameter rather than a debug-only length assertion.

The canonical N2 campaign used one AMD EPYC 9354 NUMA domain, CPUs 8 through 15, and the same binary for a repeated Williams-square 2-by-2 factorial design. It retained four pilots and 32 measured fresh processes. All 36 proofs were 230,804 bytes, had SHA-256 `c05561327b52c3a11466511dc4ccde942d89086f4541b13eb9d27ae1cf0d3e79`, and passed the unchanged proof-inspection command.

| Factorial effect | Paired-block median | Favorable blocks |
|---|---:|---:|
| Node skip on `Prove constraints` | -62.897 ms | 8 / 8 |
| Parallel serialization on packed copy | -118.250 ms | 8 / 8 |
| Parallel serialization on Flock reduction | -124.799 ms | 8 / 8 |
| Combined versus control on outer prove | -189.041 ms | 8 / 8 |
| Combined versus control on process wall | -175.106 ms | 8 / 8 |
| Combined versus control on peak physical memory | -3.781 MB | 5 / 8 |

Relative to the control-arm medians, the paired combined effect is approximately -6.31% of outer-prove time and -3.02% of process wall time. The median peak footprint is effectively unchanged. Cgroup CPU throttling, swap, memory fail counts and full-memory PSI did not increase during the campaign.

The decision rules were not prospectively preregistered. They were authored at 07:25:04 UTC after 16 measured processes had completed and the seventeenth was active, then copied to the host at 07:25:19 after 18 of 32 measured processes had completed. The exposed console observation contained admission lines rather than outcomes, but non-observation of already-written result files is not independently provable. Treat the record as a timestamped mid-campaign analysis decision, not a prospective preregistration.

Under that record, the mechanism and direction gates passed, while the deliberately stronger system-materiality rule required an outer-prove delta of at least -350 ms and failed at -189.041 ms. The direct mechanism measurements are exact and repeatedly favorable. The -189 ms outer and -175 ms wall effects are descriptive paired system measurements, not a confirmatory end-to-end acceptance claim, and they do not establish that aggregation meets a production budget.

Selection of the single-NUMA campaign was also data-driven after the valid split-NUMA `_02` campaign. In `_02`, packed copy and Flock were favorable in 8/8 blocks, constraints in 6/8, and combined outer and wall effects in only 4/8. Effective CPU service was 2.136–2.885 cores and pooled wall/service correlation was -0.773. The single-NUMA `_04` repeat narrowed service to 3.280–3.442 cores; its pooled correlation was still -0.593, while within-arm correlations were much weaker (-0.278, +0.193, -0.348 and +0.253). Campaigns `_01` and `_03` failed before retaining a proof because of, respectively, a non-native binary and a non-login `PATH` without `rustc`.

The node skip removed one of three per-row constraint evaluations and reduced the constraints phase by 13.59%. If the three evaluations have approximately equal cost, that implies about 40.8% of the phase is evaluation arithmetic and about 59.2% is traversal/materialization. This is a calibration inference rather than direct instrumentation; it points the next constraints work toward traversal fusion rather than more node algebra.

A separate 24-observation-per-arm component sweep on the same eight cores found that the packed path crosses over between 2^12 and 2^14 words: it is slower at 2^10 and 2^12, 1.226 times faster at 2^14, and 2.073 to 3.351 times faster from 2^16 through 2^22. Any automatic production policy should therefore retain a size threshold rather than enabling the parallel dispatch for every shape.

The complete single-NUMA campaign checksum manifest has SHA-256 `d7f9bedf61556cd6b0d17f052d70d4e791dfb77047bca45e054ac47228d3f03a`. An independent validator rehashed all 548 entries and reconstructed every metric and factorial effect from raw run records. On the same exact commit, Linux release validation passed 293 tests with 0 failures and 10 ignored tests, plus Clippy, formatting and documentation.

## Fast-upstream procedure

Fetch `origin/main` immediately before review. If `git rev-list --count HEAD..origin/main` is nonzero, inspect the changed files first, merge the exact new head into this branch and rerun the validation commands. Do not rewrite commits `256928f`, `7be45de` or `a2c1024`, because the retained evidence and source bundles identify those exact objects.
