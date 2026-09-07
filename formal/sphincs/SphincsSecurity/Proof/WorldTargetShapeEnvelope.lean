import SphincsSecurity.Proof.ConcreteTargetShapeQuery
import SphincsSecurity.Proof.TargetShapeExpectation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedTargetShapeVector (key : SecretKey) (payload : HashInput) (target : FewTimeView) (state : CoverLogState) : TargetShapeVector :=
  targetShapeMoments key state.1 state.2 payload target

theorem expected_logTraced_sign_targetShape_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedTargetShapeVector key payload target result.2 groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
          (observedTargetShapeVector key payload target state) groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  exact expected_signWithView_targetShapeMoments_le key message state.1 state.2 payload target groups remaining hvalid hsigned q hq hcache

theorem expected_fresh_targetShape_le (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedTargetShapeVector key payload target (before.cacheQuery input output, log) groups remaining) ≤
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (observedTargetShapeVector key payload target (before, log)) groups remaining := by
  have h := expected_randomOracle_targetShapeMoments_le key before log payload target groups remaining hvalid input hsigned
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul] at h
  exact h

theorem expected_logTraced_sign_targetEnvelope_le (key : SecretKey) (q queries signatures : Nat) (hq : q ≤ 2 ^ 127)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
        (observedTargetShapeVector key payload target result.2) groups remaining) ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries (signatures + 1)
        (observedTargetShapeVector key payload target state) groups remaining := by
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ queries signatures
    (fun G R hv => expected_logTraced_sign_targetShape_le key q hq payload target state hsigned hcache message G R hv) groups remaining hvalid).trans
      (targetShapeEnvelope_signing_le _ _ _ queries signatures _ groups remaining hvalid)

theorem expected_fresh_targetEnvelope_le (key : SecretKey) (q queries signatures : Nat) (payload : HashInput) (target : FewTimeView)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
        (observedTargetShapeVector key payload target (before.cacheQuery input output, log)) groups remaining) ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (queries + 1) signatures
        (observedTargetShapeVector key payload target (before, log)) groups remaining := by
  rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
  exact targetShapeEnvelope_mono _ _ _ queries signatures
    (fun G R hv => expected_fresh_targetShape_le key payload target before log input hfresh hsigned G R hv) groups remaining hvalid

end SphincsSecurity.Concrete
