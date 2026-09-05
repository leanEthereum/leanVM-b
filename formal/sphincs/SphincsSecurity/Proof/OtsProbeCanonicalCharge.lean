import SphincsSecurity.Proof.OtsProbeResolvedComputedCoupling
import SphincsSecurity.Proof.MappedQueryCharge
import SphincsSecurity.Proof.CoupledQueryCost

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def expectedCanonicalQueryCharge
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ℝ≥0∞ := by
  classical
  exact OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next context fuel table cache =>
      if DeferredCompletable table context then
        charge input context fuel cache +
          ∑' result, Pr[= result |
            canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
            match result with
            | none => 0
            | some result => next result.value.1 result.context result.remaining result.table result.value.2
      else 0) computation

theorem expectedCanonicalQueryCharge_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedCanonicalQueryCharge parameter root ftsSecret charge (OracleSpec.query input >>= next)
      context fuel table cache =
      if DeferredCompletable table context then
        charge input context fuel cache +
          ∑' result, Pr[= result |
            canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
            match result with
            | none => 0
            | some result => expectedCanonicalQueryCharge parameter root ftsSecret charge (next result.value.1)
                result.context result.remaining result.table result.value.2
      else 0 := by
  classical
  rfl

theorem expectedCanonicalQueryCharge_eq_zero_of_not_completable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnot : ¬DeferredCompletable table context) :
    expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [expectedCanonicalQueryCharge_query_bind, if_neg hnot]

set_option maxRecDepth 100000 in
theorem expectedCanonicalQueryCharge_le_outerQueryCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (actualCharge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hcharge : ∀ input context fuel cache actualCache,
      ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache →
      VisibleResolvedComputationsCached parameter table context actualCache →
      PublishedValues context.state → DeferredComputationsClosed context →
      charge input context fuel cache ≤ outerHashQueryCharge actualCharge input actualCache)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache ≤
      expectedOuterQueryCharge
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey) actualCharge computation actualCache := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  change _ ≤ expectedOuterQueryCharge secretKey actualCharge computation actualCache
  induction computation using OracleComp.inductionOn generalizing context fuel cache actualCache with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind, if_pos hinvariant.2.2.2.1,
        expectedOuterQueryCharge_query_bind]
      apply add_le_add (hcharge input context fuel cache actualCache hinvariant hvisible hpublished hcomputed)
      have hstep := canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel cache actualCache hinvariant hvisible hpublished
      have hsupported := FtsProbeSimulation.relTriple_and_left_support hstep
        (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
          intro left hleft result heq
          subst left
          exact hcomputed.of_mem_canonicalChronologicalQuery parameter root table ftsSecret input
            context fuel cache result hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hleft)
      have hcost := expected_cost_le_of_relTriple hsupported
        (fun left => match left with
          | none => 0
          | some result => expectedCanonicalQueryCharge parameter root ftsSecret charge (next result.value.1)
              result.context result.remaining result.table result.value.2)
        (fun right => expectedOuterQueryCharge secretKey actualCharge (next right.1) right.2)
        (fun _ => 0) (by
          intro left right hrelation
          simp only [add_zero]
          cases left with
          | none => exact bot_le
          | some result =>
              dsimp only
              have hresultComputed := hrelation.2 result rfl
              rcases hrelation.1 with hclean | hdoomed
              · rw [hclean.1, ← hclean.2.1]
                exact ih result.value.1 result.context result.remaining result.value.2 right.2
                  hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hresultComputed
              · rw [expectedCanonicalQueryCharge_eq_zero_of_not_completable parameter root ftsSecret charge
                  (next result.value.1) result.context result.remaining result.table result.value.2 (by
                    rw [hdoomed.1]
                    exact hdoomed.2.2.2)]
                exact bot_le)
      simpa only [mul_zero, tsum_zero, add_zero] using hcost

end SphincsSecurity.Concrete.OtsProbeSimulation
