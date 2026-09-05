import SphincsSecurity.Proof.OtsProbeOrdinaryCharge
import SphincsSecurity.Proof.OtsOpeningQueryReserve

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem ftsOpeningQueryReserve_eq_zero_of_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position) :
    ftsOpeningQueryReserve secretKey cache input = 0 := by
  classical
  have hnone : ¬ ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
    rintro ⟨probe, hinput⟩
    apply hat.not_atPosition (.ftsLeaf probe.index probe.tree probe.leafIdx)
    rw [← hinput]
    exact ⟨digestBytes probe.candidate, rfl⟩
  simp only [ftsOpeningQueryReserve, FtsProbeSimulation.ftsHashQueryCharge, if_neg hnone, zero_mul]

theorem otsOpeningQueryReserve_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position) :
    otsOpeningQueryReserve secretKey cache input =
      if cache input = none then
        if HasEncodingTarget cache secretKey position then 2
        else if EncodingMessageSettledAt cache secretKey position then 1 else 0
      else 3 := by
  classical
  rw [otsOpeningQueryReserve,
    ftsOpeningQueryReserve_eq_zero_of_atEncodingPosition secretKey cache input position hat, tsub_zero]
  have hexists : ∃ candidate : EncodingPosition, AtEncodingPosition secretKey.parameter input candidate :=
    ⟨position, hat⟩
  have hselected : Classical.choose hexists = position :=
    atEncodingPosition_unique (Classical.choose_spec hexists) hat
  unfold residualPrimitiveQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge
  by_cases hfresh : cache input = none
  · simp only [hfresh, if_true, hexists, ↓reduceDIte, hselected, TightEncoding.encodingStageIncrement]
    split_ifs <;> norm_num
    · exact (ENNReal.eq_sub_of_add_eq' (by norm_num)
        (show (2 : ℝ≥0∞) + 1 = 3 by norm_num)).symm
    · exact (ENNReal.eq_sub_of_add_eq' (by norm_num)
        (show (1 : ℝ≥0∞) + 2 = 3 by norm_num)).symm
  · simp [hfresh]

theorem otsOpeningQueryReserve_ge_two_of_encodingTarget
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position)
    (htarget : HasEncodingTarget cache secretKey position) :
    2 ≤ otsOpeningQueryReserve secretKey cache input := by
  rw [otsOpeningQueryReserve_atEncodingPosition secretKey cache input position hat]
  by_cases hfresh : cache input = none <;> simp [hfresh, htarget]
  norm_num

namespace OtsProbeSimulation

theorem probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ 4 / 3 := by
  have hfactor : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  calc
    _ ≤ (ordinaryContinuationCharge (fun _ _ _ => 0)
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) context fuel +
        (materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞)) *
          (4 / 3) := by
      rw [add_mul]
      exact add_le_add (by simpa only [mul_one] using mul_le_mul' le_rfl hfactor) le_rfl
    _ ≤ _ := mul_le_of_le_one_left (by positivity)
      (probingHashQueryAfterRootAwarePublicPlan_ordinaryCharge_add_materialized_le_one
        parameter input publicState plan cache context fuel)

theorem probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_reserve_of_encodingTarget
    (secretKey : SecretKey) (actualCache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position)
    (htarget : HasEncodingTarget actualCache secretKey position)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan secretKey.parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? secretKey.parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ otsOpeningQueryReserve secretKey actualCache input :=
  (probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds
    secretKey.parameter input publicState plan cache context fuel).trans
      ((by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num : (4 / 3 : ℝ≥0∞) ≤ 2).trans
        (otsOpeningQueryReserve_ge_two_of_encodingTarget secretKey actualCache input position hat htarget))

theorem probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_reserve_after_sign
    (secretKey : SecretKey) (message : Message)
    (beforeCache afterCache actualCache : QueryCache HashSpec) (result : Option Signature)
    (hrun : (result, afterCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run beforeCache))
    (hcache : afterCache ≤ actualCache)
    (position : EncodingPosition) (payload : HashInput)
    (hbefore : beforeCache (tweakableHashInput secretKey.parameter position.domain payload) = none)
    (hafter : afterCache (tweakableHashInput secretKey.parameter position.domain payload) ≠ none)
    (hvalid : TargetSum.ValidDigest (truncateHash (fromCache afterCache
      (tweakableHashInput secretKey.parameter position.domain payload))))
    (input : HashInput) (hat : AtEncodingPosition secretKey.parameter input position)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan secretKey.parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? secretKey.parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ otsOpeningQueryReserve secretKey actualCache input := by
  apply probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_reserve_of_encodingTarget
    secretKey actualCache input position hat
  exact (hasEncodingTarget_of_sign_transition secretKey message beforeCache afterCache result
    hrun position payload hbefore hafter hvalid).mono hcache

end OtsProbeSimulation

end SphincsSecurity.Concrete
