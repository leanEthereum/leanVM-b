import SphincsSecurity.Proof.OtsProbeHistoryRootSampling
import SphincsSecurity.Proof.OuterHashQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledCanonicalHashCut
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    ProbComp (Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache))) :=
  Prod.fst <$> sampledCanonicalAfterRootTrace parameter ftsSecret fuel fun root => outerHashQueryCutAt (continuation root) ordinal

theorem probEvent_sampledCanonicalHashCut_unresolvedStart_le
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (hordinal : ordinal ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit (hashCutCandidate parameter) | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] ≤
      (∑' result, Pr[= result | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] *
        historyUnresolvedStartCharge (hashCutCandidate parameter) result) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) + ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  exact probEvent_sampledCanonicalAfterRoot_unresolvedStart_le parameter ftsSecret fuel ordinal
    (fun root => outerHashQueryCutAt (continuation root) ordinal) (hashCutCandidate parameter)
    (fun root => outerHashQueryCutAt_hashBound (continuation root) ordinal) hordinal

theorem sum_sampledCanonicalHashCut_unresolvedStart_le
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit (hashCutCandidate parameter) |
      sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal]) ≤
      (∑ ordinal ∈ Finset.range q, ∑' result,
        Pr[= result | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] *
        historyUnresolvedStartCharge (hashCutCandidate parameter) result) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ ordinal ∈ Finset.range q,
        ((∑' result, Pr[= result | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] *
          historyUnresolvedStartCharge (hashCutCandidate parameter) result) *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) + ((2 ^ 216 : Nat) : ENNReal)⁻¹) := by
      apply Finset.sum_le_sum
      intro ordinal hmem
      exact probEvent_sampledCanonicalHashCut_unresolvedStart_le parameter ftsSecret fuel continuation ordinal
        ((Nat.le_of_lt (Finset.mem_range.mp hmem)).trans hq)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_mul]

theorem evalDist_sampledCanonicalHashCut_eq_original
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    evalDist (sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal) =
      evalDist (do
        let table ← sampleOtsHashTable
        let option ← runResolvedFromTable
          { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
        match option with
        | none => pure none
        | some result =>
            runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter result.value.1 table ftsSecret)
              (outerHashQueryCutAt (continuation result.value.1) ordinal) result.context result.remaining table result.value.2) := by
  simp only [sampledCanonicalHashCut, sampledCanonicalAfterRootTrace, canonicalStartErasureAfterRoot, map_bind]
  apply evalDist_bind_congr
  intro table _
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp
  | some result =>
      have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hoption
      exact runCanonicalStartErasureTrace_projection parameter result.value.1 table ftsSecret
        (outerHashQueryCutAt (continuation result.value.1) ordinal) result.context result.remaining result.value.2
        false hcore.2.1 hcore.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
