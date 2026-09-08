import SphincsSecurity.Proof.RemainingRawIndexEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def remainingTargetEnvelope (key : SecretKey) (cap budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures
    (observedTargetShapeVector key payload target state)

theorem remainingTargetEnvelope_budget_mono (key : SecretKey) (cap : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingTargetEnvelope key cap smaller payload target signatures state groups remaining ≤
      remainingTargetEnvelope key cap larger payload target signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ signatures _ hbudget groups remaining hvalid

theorem expected_randomOracle_remainingTarget_le (key : SecretKey) (cap budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      remainingTargetEnvelope key cap budget payload target signatures (result.2, state.2) groups remaining) ≤
      remainingTargetEnvelope key cap (budget + 1) payload target signatures state groups remaining := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    exact expected_fresh_targetEnvelope_le key cap budget signatures payload target state.1 state.2 input hfresh hsigned groups remaining hvalid
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact remainingTargetEnvelope_budget_mono key cap payload target signatures state (Nat.le_succ _) groups remaining hvalid

theorem expected_logTraced_world_remainingTarget_le (key : SecretKey) (cap budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      remainingTargetEnvelope key cap budget payload target signatures result.2 groups remaining) ≤
      remainingTargetEnvelope key cap (budget + signingExecutionHashCost (.inl input)) payload target signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_remainingTarget_le key cap budget payload target signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        remainingTargetEnvelope key cap budget payload target signatures (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_logTraced_sign_remainingTarget_le (key : SecretKey) (cap budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (hcap : cap ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      remainingTargetEnvelope key cap budget payload target signatures result.2 groups remaining) ≤
      remainingTargetEnvelope key cap budget payload target (signatures + 1) state groups remaining :=
  expected_logTraced_sign_targetEnvelope_le key cap budget signatures hcap payload target state hsigned hcache message groups remaining hvalid

end SphincsSecurity.Concrete
