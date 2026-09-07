import SphincsSecurity.Proof.InterleavedCoverDecomposition
import SphincsSecurity.Proof.RetainedCompletion

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signingTraceComputation_fst {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Prod.fst <$> signingTraceComputation computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, map_bind]
      apply bind_congr
      intro reply
      rw [Functor.map_map]
      exact ih reply

theorem expanded_unloggedRetainedRest_queryBound (adversary : Adversary) (key : SecretKey) (q : Nat)
    (hbound : (gameRest scheme adversary ⟨key.root, key.parameter⟩ key).IsQueryBoundP (· matches Sum.inr _) q) :
    (simulateQ (expandedAdversaryImpl key)
      (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q := by
  have h := simulateQ_expanded_retainedGameRestComputation_isQueryBoundP adversary key q hbound
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, isQueryBoundP_map_iff] at h
  have heq : Prod.fst <$> simulateQ (expandedAdversaryImpl key)
      (signingTraceComputation (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) =
        simulateQ (expandedAdversaryImpl key) (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) := by
    rw [← simulateQ_map, signingTraceComputation_fst]
  exact (isQueryBoundP_iff_of_map_eq (p := (· matches Sum.inr _)) heq).mp h

theorem retainedRoot_expanded_rest_queryBound (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest)
    (q : Nat) (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q)
    (rootResult : Digest × QueryCache HashSpec)
    (hroot : rootResult ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)) :
    (simulateQ (expandedAdversaryImpl
      ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩)
      (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q := by
  have hrootSupport : rootResult.1 ∈ support
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) := by
    apply support_simulateQ_run'_subset romImpl _ ∅
    rw [StateT.run'_eq, support_map]
    refine ⟨rootResult, ?_, rfl⟩
    rwa [simulateQ_romImpl_liftM]
  rw [gameAfterSecrets] at hbound
  exact expanded_unloggedRetainedRest_queryBound adversary _ q (isQueryBoundP_of_bind hbound rootResult.1 hrootSupport)

theorem retainedRoot_rest_cache_bound (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest)
    (q : Nat) (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q)
    (rootResult : Digest × QueryCache HashSpec)
    (hroot : rootResult ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅))
    (result : (Forgery × Bool) × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl
      ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩)
      (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩)).run (rootResult.2, []))) :
    QueryCache.enncard result.2.1 ≤ q := by
  apply actualRetainedGameAfterSecrets_cache_bound adversary parameter otsSecret table q hbound
    ((rootResult.1, (interleavedRetainedProjection result).1), result.2.1)
  rw [actualRetainedGameAfterSecrets, mem_support_bind_iff]
  refine ⟨rootResult, hroot, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨interleavedRetainedProjection result, ?_, ?_⟩
  · rw [retainedGameRestComputation_interleaved, support_map]
    exact ⟨result, hresult, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff]
    rfl

noncomputable def expectedRetainedSigningCoverCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  ∑' rootResult, Pr[= rootResult | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] *
    expectedSigningCoverCharge
      ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
      (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])

theorem expectedRetainedCoverCharge_le_worldBudget_add_signing (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    expectedRetainedCoverCharge adversary parameter otsSecret table q ≤
      (q : ENNReal) * (7 * (2 : ENNReal) ^ 40 + expectedRetainedCompletionReuseCharge adversary parameter otsSecret table q) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ + expectedRetainedSigningCoverCharge adversary parameter otsSecret table q := by
  let rootRun := (simulateQ (randomOracle : QueryImpl HashSpec _)
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅
  let reuse := fun rootResult : Digest × QueryCache HashSpec =>
    ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
      expectedCompletionReuseCharge
        ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q (degree + 1)
        (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])
  let signing := fun rootResult : Digest × QueryCache HashSpec => expectedSigningCoverCharge
    ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
    (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])
  let fixed : ENNReal := (q : ENNReal) * (7 * (2 : ENNReal) ^ 40) * ((2 ^ 176 : Nat) : ENNReal)⁻¹
  have hstep (rootResult : Digest × QueryCache HashSpec) (hroot : rootResult ∈ support rootRun) :
      expectedValidInterleavedCoverCharge
        ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
        (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, []) ≤
          (fixed + (q : ENNReal) * reuse rootResult * ((2 ^ 176 : Nat) : ENNReal)⁻¹) + signing rootResult := by
    have hsigned : SigningDigestsCached parameter rootResult.2 rootResult.1 [] := by
      intro entry hentry
      simp only [List.not_mem_nil] at hentry
    have hbudget := retainedRoot_expanded_rest_queryBound adversary parameter otsSecret table q hbound rootResult hroot
    apply (expectedValidInterleavedCoverCharge_le_expanded_queryBound _ q _ q hbudget (rootResult.2, []) hsigned).trans
    simp only [frozenCoverWeight, ← mul_assoc, ENNReal.tsum_mul_right]
    have hmoment := expected_adaptive_frozenOccupancy_le_seven_add_reuse _ q hq _ rootResult.2
      (retainedRoot_rest_cache_bound adversary parameter otsSecret table q hbound rootResult hroot)
    exact (add_le_add (mul_le_mul' (mul_le_mul' le_rfl hmoment) le_rfl) le_rfl).trans_eq (by dsimp only [fixed, signing, reuse]; ring)
  rw [expectedRetainedCoverCharge]
  apply le_trans (b := ∑' rootResult, Pr[= rootResult | rootRun] *
    ((fixed + (q : ENNReal) * reuse rootResult * ((2 ^ 176 : Nat) : ENNReal)⁻¹) + signing rootResult))
  · apply ENNReal.tsum_le_tsum
    intro rootResult
    by_cases hroot : rootResult ∈ support rootRun
    · exact mul_le_mul' le_rfl (hstep rootResult hroot)
    · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]
  · have hreusesum : (∑' rootResult, Pr[= rootResult | rootRun] *
        ((q : ENNReal) * reuse rootResult * ((2 ^ 176 : Nat) : ENNReal)⁻¹)) =
          (q : ENNReal) * expectedRetainedCompletionReuseCharge adversary parameter otsSecret table q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
      simp_rw [← mul_assoc, mul_right_comm (Pr[= _ | _]) (q : ENNReal)]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      dsimp only [expectedRetainedCompletionReuseCharge, rootRun, reuse]
      ring
    simp_rw [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hreusesum]
    apply (add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl) le_rfl).trans_eq
    dsimp only [fixed, signing, expectedRetainedSigningCoverCharge, rootRun]
    ring

end SphincsSecurity.Concrete.FtsProbeSimulation
