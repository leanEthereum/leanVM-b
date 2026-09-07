import SphincsSecurity.Proof.ClosedRawIndexSigning
import SphincsSecurity.Proof.RawIndexQuery
import SphincsSecurity.Proof.TargetShapeExpectation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedRawIndexShapeVector (key : SecretKey) (state : CoverLogState) : TargetShapeVector :=
  liftTargetIndexVector (targetIndexMoments key state.1 state.2)

theorem expected_logTraced_sign_rawIndexShape_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedRawIndexShapeVector key result.2 groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
          (observedRawIndexShapeVector key state) groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  apply (expected_signWithView_targetIndexMoments_le key message state.1 state.2 groups.card remaining.card hsigned q hq hcache).trans_eq
  exact (targetShapeSigning_lift _ _ _ groups remaining hvalid).symm

theorem expected_fresh_rawIndexShape_le (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedRawIndexShapeVector key (before.cacheQuery input output, log) groups remaining) ≤
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (observedRawIndexShapeVector key (before, log)) groups remaining := by
  change (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
    targetIndexMoments key (before.cacheQuery input output) log groups.card remaining.card) ≤ _
  by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input
  · rw [expected_message_targetIndexMoments key groups.card remaining.card before log input hfresh hsigned hmessage]
    apply le_of_eq
    change _ = targetShapeQuery _ (liftTargetIndexVector (targetIndexMoments key before log)) groups remaining
    rw [targetShapeQuery_lift]
    simp only [liftTargetIndexVector, targetIndexQuery, targetIndexCacheLower, div_eq_mul_inv]
    ring
  · have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
    simp only [targetIndexMoments_cacheQuery key groups.card remaining.card before log input _ hfresh hsigned,
      hmessage, false_and, if_false, add_zero, ENNReal.tsum_mul_right, hmass, one_mul]
    exact le_self_add

theorem expected_logTraced_sign_rawIndexEnvelope_le (key : SecretKey) (q queries signatures : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
        (observedRawIndexShapeVector key result.2) groups remaining) ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries (signatures + 1)
        (observedRawIndexShapeVector key state) groups remaining := by
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ queries signatures
    (fun G R hv => expected_logTraced_sign_rawIndexShape_le key q hq state hsigned hcache message G R hv) groups remaining hvalid).trans
      (targetShapeEnvelope_signing_le _ _ _ queries signatures _ groups remaining hvalid)

theorem expected_fresh_rawIndexEnvelope_le (key : SecretKey) (q queries signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
        (observedRawIndexShapeVector key (before.cacheQuery input output, log)) groups remaining) ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (queries + 1) signatures
        (observedRawIndexShapeVector key (before, log)) groups remaining := by
  rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
  exact targetShapeEnvelope_mono _ _ _ queries signatures
    (fun G R _ => expected_fresh_rawIndexShape_le key before log input hfresh hsigned G R) groups remaining hvalid

end SphincsSecurity.Concrete
