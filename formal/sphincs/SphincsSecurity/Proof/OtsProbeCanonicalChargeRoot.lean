import SphincsSecurity.Proof.OtsProbeCanonicalChargeGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def canonicalJointChargeAfterTable
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' result, Pr[= result | runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedCanonicalQueryCharge parameter result.value.1 ftsSecret
        (canonicalJointOuterCharge parameter)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

set_option maxRecDepth 100000 in
theorem canonicalJointChargeAfterTable_le_gameReserve
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve
        (primitiveAccountingKey parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let actualCost := fun result : Digest × QueryCache HashSpec =>
    expectedQueryCharge (otsOpeningRefinedQueryReserve accountingKey)
      (gameRest scheme adversary ⟨result.1, parameter⟩ ⟨parameter, result.1, otsSecret, ftsSecret⟩) result.2
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact deferredComputationsClosed_empty.of_mem_runResolved _ _ fuel table result hleft)
  have hcost : canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    have hbound := expected_cost_le_of_relTriple hsupported
      (fun left => match left with
        | none => 0
        | some result => expectedCanonicalQueryCharge parameter result.value.1 ftsSecret
            (canonicalJointOuterCharge parameter)
            (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
            result.context result.remaining table result.value.2)
      actualCost (fun _ => 0) (by
        intro left right hrelation
        simp only [add_zero]
        cases left with
        | none => exact bot_le
        | some result =>
            dsimp only
            rcases hrelation.1 with hclean | hdoomed
            · have hcomputed := hrelation.2 result rfl
              have hlocal := expectedCanonicalJointCharge_le_actualReserve parameter result.value.1 table ftsSecret
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining result.value.2 right.2 hclean.2.2.1
                hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
              have hreserve : otsOpeningRefinedQueryReserve
                  (⟨parameter, result.value.1, otsSecret, ftsSecret⟩ : SecretKey) =
                  otsOpeningRefinedQueryReserve accountingKey :=
                otsOpeningRefinedQueryReserve_set_root accountingKey result.value.1
              rw [hreserve, expectedQueryCharge_retained_eq_gameRest] at hlocal
              simpa only [actualCost, ← hclean.2.1] using hlocal
            · rw [expectedCanonicalQueryCharge_eq_zero_of_not_completable parameter result.value.1 ftsSecret
                (canonicalJointOuterCharge parameter)
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining table result.value.2 hdoomed.2.2.2]
              exact bot_le)
    simpa only [canonicalJointChargeAfterTable, treeRoot, otsSecret, mul_zero, tsum_zero, add_zero] using hbound
  apply hcost.trans
  change _ ≤ expectedQueryCharge (otsOpeningRefinedQueryReserve accountingKey)
    (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
  rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
  exact le_add_self

end SphincsSecurity.Concrete.OtsProbeSimulation
