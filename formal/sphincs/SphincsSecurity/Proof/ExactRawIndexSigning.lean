import SphincsSecurity.Proof.ExactSignerReuse
import SphincsSecurity.Proof.FreshSigningEnvelopeGap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem expected_signWithView_targetIndexMoments_le_exactReuse
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) ≤
        targetIndexSigning (freshDigestSelectionProbability key message before *
          (Fintype.card Index : ENNReal)⁻¹) (exactDigestReuseWeight key message before)
          (targetIndexMoments key before log) power degree :=
  expected_signWithView_targetIndexMoments_le_of_reuseWeight key message before log power degree hsigned
    (exactDigestReuseWeight key message before) (fun input =>
      probEvent_signWithView_fixedPrehit_le_exactWeight key message before input (fun _ => True))

theorem expected_logTraced_sign_rawIndexShape_le_exactReuse
    (key : SecretKey) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedRawIndexShapeVector key result.2 groups remaining) ≤
        targetShapeSigning (freshDigestSelectionProbability key message state.1 *
          (Fintype.card Index : ENNReal)⁻¹) (exactDigestReuseWeight key message state.1)
          (observedRawIndexShapeVector key state) groups remaining :=
  expected_logTraced_sign_rawIndexShape_le_of_reuseWeight key state hsigned message
    (exactDigestReuseWeight key message state.1) (fun input =>
      probEvent_signWithView_fixedPrehit_le_exactWeight key message state.1 input (fun _ => True))
    groups remaining hvalid

theorem targetShapeSigning_add_cached_and_exhaustion
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (uniform : ENNReal)
    (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeSigning (freshDigestSelectionProbability key message cache * uniform)
        (exactDigestReuseWeight key message cache) f groups remaining +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) *
        exactDigestReuseWeight key message cache * uniform * targetFreshSigningIncrement f groups remaining +
      digestExhaustionProbability key message cache * uniform * targetFreshSigningIncrement f groups remaining =
      targetShapeSigning uniform (exactDigestReuseWeight key message cache) f groups remaining := by
  have hmass := freshSelection_add_count_exactWeight_add_exhaustion key message cache
  unfold targetShapeSigning targetFreshSigningIncrement
  calc
    _ = f groups remaining +
        (freshDigestSelectionProbability key message cache +
          cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) *
            exactDigestReuseWeight key message cache + digestExhaustionProbability key message cache) * uniform *
        (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
          targetCacheLower (targetTreeLower f) groups remaining) +
        exactDigestReuseWeight key message cache * targetReuseStep f groups remaining := by ring
    _ = _ := by rw [hmass, one_mul]

theorem expected_logTraced_sign_rawIndexShape_add_cached_and_exhaustion_le
    (key : SecretKey) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedRawIndexShapeVector key result.2 groups remaining) +
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) *
        exactDigestReuseWeight key message state.1 * (Fintype.card Index : ENNReal)⁻¹ *
        targetFreshSigningIncrement (observedRawIndexShapeVector key state) groups remaining +
      digestExhaustionProbability key message state.1 * (Fintype.card Index : ENNReal)⁻¹ *
        targetFreshSigningIncrement (observedRawIndexShapeVector key state) groups remaining ≤
      targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (exactDigestReuseWeight key message state.1)
        (observedRawIndexShapeVector key state) groups remaining :=
  (add_le_add (add_le_add
    (expected_logTraced_sign_rawIndexShape_le_exactReuse key state hsigned message groups remaining hvalid) le_rfl) le_rfl).trans_eq
    (targetShapeSigning_add_cached_and_exhaustion key message state.1 _ _ groups remaining)

end SphincsSecurity.Concrete
