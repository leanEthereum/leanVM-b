import SphincsSecurity.Proof.JointOverlapParentRun
import SphincsSecurity.Proof.SharedFailureDiscardTrace
import SphincsSecurity.Proof.InitializedJointCollisionCoverageOverlap
import SphincsSecurity.Proof.InitializedSharedParentRefund
import SphincsSecurity.Proof.RetainedCollisionCacheReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedJointCoverageAfterParentRefund (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  min 1 ((q : ENNReal) * initialRawIndexRate q) *
      Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] +
    ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedJointCollisionCoverageAfterParentRefund parameter initial.2.1 otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone

theorem initialized_sharedParentDiscard_add_remainder_le_overlap
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedSharedParentDiscard adversary parameter otsTable ftsTable q fuel * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
      initializedJointCoverageAfterParentRefund adversary parameter otsTable ftsTable q fuel ≤
      initializedJointCollisionCoverageOverlap adversary parameter otsTable ftsTable q fuel := by
  rw [initializedSharedParentDiscard, initializedJointCoverageAfterParentRefund, initializedJointCollisionCoverageOverlap, add_left_comm]
  apply add_le_add le_rfl
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [mul_assoc, ← mul_add]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
      (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
    rw [expectedSharedFailureDiscard_retainedComputation _ _ adversary parameter initial.2.1 otsTable ftsTable q htrace]
    have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hfinite := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
    apply expected_sharedParentDiscard_add_remainder_le_overlap parameter initial.2.1 otsTable ftsTable q q _ initial.1 (initial.2.2, []) false initial.1.isNone hfinite
    intro result hr
    have hm : result.1.2.1.2 ∈ support ((fun result => result.1.2.1.2) <$>
        runWithFailure (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
          (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 initial.2.2 false initial.1.isNone) := by
      rw [support_map]
      exact ⟨result, hr, rfl⟩
    rw [← runWithFailure_retainedComputation_cache_projection _ adversary parameter initial.2.1 otsTable ftsTable q htrace, support_map] at hm
    obtain ⟨retained, hretained, heq⟩ := hm
    have hfull : retained ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel) := by
      rw [runRetainedWithFailure, mem_support_bind_iff]
      exact ⟨initial, hi, hretained⟩
    rw [← heq]
    exact (runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp otsTable ftsTable hfts fuel retained hfull).trans
      (Nat.cast_le.mpr hqMax)
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
