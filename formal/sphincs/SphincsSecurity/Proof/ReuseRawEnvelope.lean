import SphincsSecurity.Proof.ExactRawIndexSigning
import SphincsSecurity.Proof.SigningExecutionBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def reuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
    (observedRawIndexShapeVector key state)

theorem expected_fresh_reuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      reuseRawEnvelope key reuse queries signatures (before.cacheQuery input output, log) groups remaining) ≤
      reuseRawEnvelope key reuse (queries + 1) signatures (before, log) groups remaining := by
  unfold reuseRawEnvelope
  rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
  exact targetShapeEnvelope_mono _ _ _ queries signatures
    (fun G R _ => expected_fresh_rawIndexShape_le key before log input hfresh hsigned G R) groups remaining hvalid

theorem expected_hash_reuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      reuseRawEnvelope key reuse queries signatures (result.2, log) groups remaining) ≤
      reuseRawEnvelope key reuse (queries + 1) signatures (before, log) groups remaining := by
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    exact expected_fresh_reuseRawEnvelope_le key reuse queries signatures before log input hfresh hsigned groups remaining hvalid
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    exact targetShapeEnvelope_queries_mono _ _ _ _ _ (Nat.le_succ queries) groups remaining hvalid

theorem expected_world_reuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcost : signingExecutionHashCost (.inl input) ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      reuseRawEnvelope key reuse (budget - signingExecutionHashCost (.inl input)) signatures
        (result.2, log) groups remaining) ≤ reuseRawEnvelope key reuse budget signatures (before, log) groups remaining := by
  cases input with
  | inl sample =>
      change (∑' result : unifSpec.Range sample × QueryCache HashSpec,
        Pr[= result | (fun answer => (answer, before)) <$> (liftM (unifSpec.query sample) : ProbComp _)] *
          reuseRawEnvelope key reuse budget signatures (result.2, log) groups remaining) ≤ _
      rw [tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  | inr input =>
      have hbudget : budget - 1 + 1 = budget := Nat.sub_add_cancel hcost
      change (∑' result, Pr[= result | (randomOracle input).run before] *
        reuseRawEnvelope key reuse (budget - 1) signatures (result.2, log) groups remaining) ≤ _
      simpa only [hbudget] using
        expected_hash_reuseRawEnvelope_le key reuse (budget - 1) signatures before log input hsigned groups remaining hvalid

theorem expected_logTraced_world_reuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcost : signingExecutionHashCost (.inl input) ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseRawEnvelope key reuse (budget - signingExecutionHashCost (.inl input)) signatures result.2 groups remaining) ≤
      reuseRawEnvelope key reuse budget signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using
    expected_world_reuseRawEnvelope_le key reuse budget signatures state.1 state.2 input hsigned hcost groups remaining hvalid

theorem expected_logTraced_sign_reuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseRawEnvelope key reuse (budget - signingExecutionHashCost (.inr message)) signatures result.2 groups remaining) ≤
      reuseRawEnvelope key reuse budget (signatures + 1) state groups remaining := by
  have hstep : TargetShapeLE
      (fun G R => ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
        observedRawIndexShapeVector key result.2 G R)
      (targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse (observedRawIndexShapeVector key state)) := by
    intro G R hv
    apply (expected_logTraced_sign_rawIndexShape_le_exactReuse key state hsigned message G R hv).trans
    unfold targetShapeSigning
    exact add_le_add (add_le_add le_rfl (mul_le_mul'
      (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message state.1)) le_rfl))
      (mul_le_mul' hreuse le_rfl)
  unfold reuseRawEnvelope
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ _ _ hstep groups remaining hvalid).trans
    ((targetShapeEnvelope_signing_le _ _ _ _ _ _ groups remaining hvalid).trans
      (targetShapeEnvelope_queries_mono _ _ _ _ _ (Nat.sub_le _ _) groups remaining hvalid))

end SphincsSecurity.Concrete
