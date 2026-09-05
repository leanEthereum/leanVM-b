import SphincsSecurity.Proof.OtsProbeLiveKnownRootCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem rootEncodingQueryCharge_set_root (secretKey : SecretKey) (root : Digest) :
    rootEncodingQueryCharge { secretKey with root := root } = rootEncodingQueryCharge secretKey := rfl

noncomputable def initializedKnownRootChargeAfterTable
    (targets : Finset Position)
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' result, Pr[= result | runResolvedFromTable
    (ensuredInitialContext targets)
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedLiveNativeContextCharge
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (knownEncodingRootOuterCharge parameter)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

set_option maxRecDepth 100000 in
theorem initializedKnownRootChargeAfterTable_le_gameRootCharge
    (targets : Finset Position)
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel ≤
      expectedQueryCharge (rootEncodingQueryCharge
        (primitiveAccountingKey parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let actualCost := fun result : Digest × QueryCache HashSpec =>
    expectedQueryCharge (rootEncodingQueryCharge accountingKey)
      (gameRest scheme adversary ⟨result.1, parameter⟩ ⟨parameter, result.1, otsSecret, ftsSecret⟩) result.2
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    (ensuredInitialContext targets)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
    (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact (ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table result hleft)
  have hcost : initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    have hbound := expected_cost_le_of_relTriple hsupported
      (fun left => match left with
        | none => 0
        | some result => expectedLiveNativeContextCharge
            (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (knownEncodingRootOuterCharge parameter)
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
              have hlocal := expectedLiveKnownRootCharge_le_actualRootCharge parameter result.value.1 table ftsSecret
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining result.value.2 right.2 hclean.2.2.1
                hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
              have hreserve : rootEncodingQueryCharge
                  (⟨parameter, result.value.1, otsSecret, ftsSecret⟩ : SecretKey) =
                  rootEncodingQueryCharge accountingKey :=
                rootEncodingQueryCharge_set_root accountingKey result.value.1
              rw [hreserve, expectedQueryCharge_retained_eq_gameRest] at hlocal
              simpa only [actualCost, ← hclean.2.1] using hlocal
            · rw [expectedLiveNativeContextCharge_eq_zero_of_not_completable
                (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (knownEncodingRootOuterCharge parameter)
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining table result.value.2 hdoomed.2.2.2]
              exact bot_le)
    simpa only [initializedKnownRootChargeAfterTable, treeRoot, otsSecret, mul_zero, tsum_zero, add_zero] using hbound
  apply hcost.trans
  change _ ≤ expectedQueryCharge (rootEncodingQueryCharge accountingKey)
    (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
  rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
  exact le_add_self

noncomputable def sampledInitializedKnownRootCharge
    (targets : Finset Position)
    (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' table, Pr[= table | sampleOtsHashTable] *
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel

theorem sampledInitializedKnownRootCharge_le_rootCharge
    (targets : Finset Position)
    (adversary : Adversary) (fuel : Nat) :
    sampledInitializedKnownRootCharge targets adversary fuel ≤ sampledQueryCharge rootEncodingQueryCharge adversary := by
  unfold sampledInitializedKnownRootCharge sampledQueryCharge
  simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedQueryCharge (rootEncodingQueryCharge (primitiveAccountingKey parameter otsSecret ftsSecret))
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (initializedKnownRootChargeAfterTable_le_gameRootCharge targets
        adversary parameter table ftsSecret fuel))
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled

theorem sampledInitializedNativeDirectRisk_add_knownRootCharge_le_refinedReserve
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q +
      sampledInitializedKnownRootCharge targets adversary fuel * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add le_rfl (mul_le_mul'
    (sampledInitializedKnownRootCharge_le_rootCharge targets adversary fuel) le_rfl)).trans
  exact sampledInitializedNativeDirectRisk_add_rootEncodingCharge_le_refinedReserve targets adversary fuel q hq

end SphincsSecurity.Concrete.OtsProbeSimulation
