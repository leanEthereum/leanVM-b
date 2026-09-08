import SphincsSecurity.Proof.RemainingRawIndexEnvelope
import SphincsSecurity.Proof.InitialRawIndexEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_adaptive_validRawIndexShape_le_remaining {α : Type} (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      (if SigningTranscript.Valid result.2.2 then observedRawIndexShapeVector key result.2 groups remaining else 0)) ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value =>
      rw [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, cappedRemainingRawIndexEnvelope]
      split_ifs
      · exact le_targetShapeEnvelope _ _ _ _ _ _ groups remaining
      · exact le_rfl
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
      have hstep := expected_logTraced_cappedRemainingRawIndex_le key cap budget hcap state hsigned hbefore input hcost groups remaining hvalid
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ hstep
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · exact mul_le_mul' le_rfl (ih result.1 (budget - signingExecutionHashCost input) result.2
          (expanded_query_bound_signing_execution key input next budget hbound state result hr).2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hr) (htail result hr))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem remainingRawIndexEnvelope_initial (key : SecretKey) (cap budget signatures : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingRawIndexEnvelope key cap budget signatures (cache, []) groups remaining =
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures
        initialTargetIndexVector groups.card remaining.card := by
  have h : remainingRawIndexEnvelope key cap budget signatures (cache, []) groups remaining =
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures
        (targetIndexMoments key cache []) groups.card remaining.card :=
    targetShapeEnvelope_lift _ _ _ budget signatures _ groups remaining hvalid
  rw [targetIndexMoments_initial key cache hnone] at h
  exact h

theorem expected_adaptive_validRawIndex_le_remaining_initial {α : Type} (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ cap) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedRawIndexShapeVector key result.2 groups remaining else 0)) ≤
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatureLimit
        initialTargetIndexVector groups.card remaining.card := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have h := expected_adaptive_validRawIndexShape_le_remaining key cap budget hcap computation (cache, []) hbound hsigned hcache groups remaining hvalid
  simpa only [cappedRemainingRawIndexEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), List.length_nil,
    Nat.sub_zero, remainingRawIndexEnvelope_initial key cap budget signatureLimit cache hnone groups remaining hvalid] using h

end SphincsSecurity.Concrete
