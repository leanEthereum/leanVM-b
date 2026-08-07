# Aggregation performance research handoff

Date: 2026-08-07

## Purpose

This branch preserves the exact measured seven-component research lineage and integrates upstream `main` at `e9cd16d49ef33909d9732778451ec73fbbedfd4a`. It is intended for technical review and current-source reproduction. It is not proposed as a merge-ready production patch.

## Source identities

| Role | Commit |
|---|---|
| Measured upstream freeze | `84fbd3ef49573537950f83c7ff66fd489476ca5d` |
| Six-component measured candidate | `b61a0ee64a9e5f41c368f937c56cdbb74fd3908b` |
| Seven-component measured candidate | `256928f9127c812749e40b08b4cf9744185c6b61` |
| Hardened L0 policy | `7be45deb92135c615dee0aaa4b294390b2de6902` |
| L0 boundary tests | `a2c10248d2b38c4e1381687b7e193eca081f612c` |
| Upstream integrated for this handoff | `e9cd16d49ef33909d9732778451ec73fbbedfd4a` |
| Integration merge | `ae08017b89fdc03bfa0af31d31b08bf3c11eaa9d` |

The statistical performance campaigns bind to `256928f`, not to the integration merge. The integration merge establishes source compatibility and test acceptance only. It has not received a fresh full-system performance campaign.

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

On the integration merge, the following passed on an Apple M4 Pro:

- `cargo testall`: 293 passed, 0 failed and 9 ignored, including doctests.
- `cargo test --release --workspace --all-features`: 293 passed, 0 failed and 9 ignored, including doctests.
- `cargo clippyall`.
- `cargo fmt --all -- --check`.
- `cargo docall`.

The AVX-512 component is not selected on this Apple host. Its system measurements and x86 exactness coverage belong to the sealed Zen 4 campaign.

## Evidence boundary

The evidence pack contains raw run order, command and environment records, 25 ms process-memory samples, host samples, phase events, serialized proofs, inspection logs, fixtures, source bundles and campaign checksum manifests. Its root manifest names 2,137 files and has SHA-256 `b6ae60e665294629bfc9dc599ed44472cf38fef4b487553f9aba5464b13dcd71`. The pack is retained outside this source branch and can be transferred separately.

Before drawing a current-main performance conclusion, rerun the canonical N2 campaign on this integration branch or a later descendant. Upstream commits after the measured freeze changed the recursion guest, native recursion code and Python verifier, so the old medians must not be relabeled as measurements of the integrated head.

## Fast-upstream procedure

Fetch `origin/main` immediately before review. If `git rev-list --count HEAD..origin/main` is nonzero, inspect the changed files first, merge the exact new head into this branch and rerun the validation commands. Do not rewrite commits `256928f`, `7be45de` or `a2c1024`, because the retained evidence and source bundles identify those exact objects.
