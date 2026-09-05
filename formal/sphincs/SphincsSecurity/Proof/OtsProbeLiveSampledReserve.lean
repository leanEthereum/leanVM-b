import SphincsSecurity.Proof.OtsProbeLiveJointReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def liveOtsChargeAfterTable
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedLiveNativeOuterCharge
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret)
        (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal))
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

theorem liveOtsChargeAfterTable_le_gameDirectCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    liveOtsChargeAfterTable adversary parameter table ftsSecret fuel ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let actualCost := fun result : Digest × QueryCache HashSpec =>
    expectedQueryCharge (directOtsQueryCharge parameter)
      (gameRest scheme adversary ⟨result.1, parameter⟩ ⟨parameter, result.1, otsSecret, ftsSecret⟩) result.2
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hcost : liveOtsChargeAfterTable adversary parameter table ftsSecret fuel ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    have hbound := expected_cost_le_of_relTriple hroot
      (fun left => match left with
        | none => 0
        | some result => expectedLiveNativeOuterCharge
            (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret)
            (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal))
            (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
            result.context result.remaining table result.value.2)
      actualCost (fun _ => 0) (by
        intro left right hrelation
        simp only [add_zero]
        cases left with
        | none => exact bot_le
        | some result =>
            dsimp only
            rcases hrelation with hclean | hdoomed
            · have hlocal := expectedLiveChronologicalOtsCharge_le_directCharge parameter result.value.1 table ftsSecret
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining result.value.2 right.2 hclean.2.2.1
                hclean.2.2.2.1 hclean.2.2.2.2
              rw [expectedQueryCharge_retained_eq_gameRest] at hlocal
              simpa only [actualCost, ← hclean.2.1] using hlocal
            · rw [expectedLiveNativeOuterCharge_eq_zero_of_not_completable
                (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret)
                (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal))
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining table result.value.2 hdoomed.2.2.2]
              exact bot_le)
    simpa only [liveOtsChargeAfterTable, treeRoot, otsSecret, mul_zero, tsum_zero, add_zero] using hbound
  apply hcost.trans
  change _ ≤ expectedQueryCharge (directOtsQueryCharge parameter)
    (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
  rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
  exact le_add_self

noncomputable def sampledLiveOtsCharge (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' table, Pr[= table | sampleOtsHashTable] *
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        liveOtsChargeAfterTable adversary parameter table ftsSecret fuel

theorem sampledLiveOtsCharge_le_directCharge (adversary : Adversary) (fuel : Nat) :
    sampledLiveOtsCharge adversary fuel ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary := by
  unfold sampledLiveOtsCharge sampledQueryCharge
  simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      liveOtsChargeAfterTable adversary parameter table ftsSecret fuel)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedQueryCharge (directOtsQueryCharge parameter)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (liveOtsChargeAfterTable_le_gameDirectCharge adversary parameter table ftsSecret fuel))
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero, primitiveAccountingKey] using hcoupled

theorem sampledLiveOtsCharge_add_remaining_le_refinedReserve (adversary : Adversary) (fuel : Nat) :
    sampledLiveOtsCharge adversary fuel + sampledQueryCharge remainingOtsQueryReserve adversary ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  exact (add_le_add (sampledLiveOtsCharge_le_directCharge adversary fuel) le_rfl).trans_eq
    (sampled_direct_add_remaining_otsQueryReserve adversary)

end SphincsSecurity.Concrete.OtsProbeSimulation
