import SphincsSecurity.Proof.CachedTargetEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem newTargetEnvelopeCharge_cacheQuery (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    newTargetEnvelopeCharge key before (before.cacheQuery input output) log uniform reuse arrival queries signings groups remaining =
      if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key (before.cacheQuery input output) log (payloadOf input) (hashOutputFewTimeView output)) groups remaining else 0 := by
  unfold newTargetEnvelopeCharge
  rw [cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh,
    cacheMessageWeight_fresh_restriction, zero_add]
  simp only [hfresh, if_true]

theorem expected_randomOracle_newCachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((randomOracle input).run before), QueryCache.enncard result.2 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      newCachedTargetEnvelope key q signatures before (result.2, log) groups remaining) ≤
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        rawIndexCacheEnvelope key q signatures (before, log) groups remaining := by
  by_cases hfresh : before input = none
  · have hafter (output : HashOutput) : QueryCache.enncard (before.cacheQuery input output) ≤ q := by
      apply hcap (output, before.cacheQuery input output)
      rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map]
      have hout : output ∈ support ($ᵗ HashOutput : ProbComp HashOutput) := by simp
      exact ⟨output, hout, rfl⟩
    rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    calc
      _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          newTargetEnvelopeCharge key before (before.cacheQuery input output) log (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
            (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (messageCacheSlotCount key.parameter q before) signatures groups remaining := by
        apply ENNReal.tsum_le_tsum
        intro output
        exact mul_le_mul' le_rfl (newCachedTargetEnvelope_le_fixed key q signatures before (before.cacheQuery input output, log)
          (QueryCache.le_cacheQuery before hfresh) (hafter output) groups remaining hvalid)
      _ ≤ _ := by
        simp only [newTargetEnvelopeCharge_cacheQuery key before log _ _ _ _ _ groups remaining input _ hfresh]
        by_cases hmessage : MessageHashInput key.parameter input
        · obtain ⟨payload, rfl⟩ := hmessage
          simp only [show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
            true_and, payloadOf_tweakableHashInput]
          rw [expected_cacheQuery_freshTargetEnvelope key before log payload hfresh hsigned _ _ _ _ _ groups remaining hvalid]
          unfold rawIndexCacheEnvelope observedRawIndexShapeVector
          rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
        · simp only [hmessage, false_and, if_false, mul_zero, tsum_zero, zero_le]
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    rw [newCachedTargetEnvelope, cacheMessageWeight_fresh_restriction]
    exact bot_le

end SphincsSecurity.Concrete
