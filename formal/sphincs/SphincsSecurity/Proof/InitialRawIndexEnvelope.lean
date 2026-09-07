import SphincsSecurity.Proof.AdaptiveRawIndex

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def initialTargetIndexVector (power degree : Nat) : ENNReal :=
  if power = 0 ∧ degree = 0 then Fintype.card Index else 0

theorem targetIndexMoments_initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    targetIndexMoments key cache [] = initialTargetIndexVector := by
  have hcount (index : Index) : cachedIndexMultiplicity key.parameter cache index = 0 :=
    cacheMessageWeight_of_no_message key.parameter _ cache hnone
  funext power degree
  simp only [targetIndexMoments, hcount, observedOptionalSigningViews, signingSlotsAtIndex]
  cases power <;> cases degree <;> simp [initialTargetIndexVector]

theorem rawIndexCacheEnvelope_eq_index (key : SecretKey) (q signatures : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexCacheEnvelope key q signatures state groups remaining =
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (cacheSlotCount q state.1) signatures
        (targetIndexMoments key state.1 state.2) groups.card remaining.card :=
  targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid

theorem expected_adaptive_validRawIndex_le_initial {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then targetIndexMoments key result.2.1 result.2.2 groups.card remaining.card else 0)) ≤
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit initialTargetIndexVector groups.card remaining.card := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hbound := expected_adaptive_validRawIndexShape_le key q hq computation (cache, []) hsigned hbudget groups remaining hvalid
  simp only [cappedRawIndexCacheEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), List.length_nil, Nat.sub_zero] at hbound
  apply hbound.trans
  apply (targetShapeEnvelope_queries_mono _ _ _ signatureLimit (observedRawIndexShapeVector key (cache, []))
    (show cacheSlotCount q cache ≤ q from Nat.sub_le _ _) groups remaining hvalid).trans_eq
  unfold observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ q signatureLimit _ groups remaining hvalid, targetIndexMoments_initial key cache hnone]

end SphincsSecurity.Concrete
