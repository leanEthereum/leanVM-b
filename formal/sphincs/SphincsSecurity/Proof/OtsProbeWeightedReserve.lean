import SphincsSecurity.Proof.OtsProbeCanonicalWeightedCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def canonicalChargeAfterTable
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' result, Pr[= result | runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedCanonicalQueryCharge parameter result.value.1 ftsSecret
        charge
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

set_option maxRecDepth 100000 in
theorem canonicalChargeAfterTable_le_gameReserve
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (hcharge : ∀ input context remaining cache,
      charge input context remaining cache ≤ canonicalOtsOuterCharge parameter input context remaining cache) :
    canonicalChargeAfterTable charge adversary parameter table ftsSecret fuel ≤
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
  have hcost : canonicalChargeAfterTable charge adversary parameter table ftsSecret fuel ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    have hbound := expected_cost_le_of_relTriple hsupported
      (fun left => match left with
        | none => 0
        | some result => expectedCanonicalQueryCharge parameter result.value.1 ftsSecret
            charge
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
              have hlocal := (expectedCanonicalQueryCharge_mono parameter result.value.1 ftsSecret charge
                (canonicalOtsOuterCharge parameter) hcharge
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining table result.value.2).trans
                  (expectedCanonicalOtsCharge_le_actualReserve parameter result.value.1 table ftsSecret
                    (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                    result.context result.remaining result.value.2 right.2 hclean.2.2.1
                    hclean.2.2.2.1 hclean.2.2.2.2 hcomputed)
              have hreserve : otsOpeningRefinedQueryReserve
                  (⟨parameter, result.value.1, otsSecret, ftsSecret⟩ : SecretKey) =
                  otsOpeningRefinedQueryReserve accountingKey :=
                otsOpeningRefinedQueryReserve_set_root accountingKey result.value.1
              rw [hreserve, expectedQueryCharge_retained_eq_gameRest] at hlocal
              simpa only [actualCost, ← hclean.2.1] using hlocal
            · rw [expectedCanonicalQueryCharge_eq_zero_of_not_completable parameter result.value.1 ftsSecret
                charge
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
                result.context result.remaining table result.value.2 hdoomed.2.2.2]
              exact bot_le)
    simpa only [canonicalChargeAfterTable, treeRoot, otsSecret, mul_zero, tsum_zero, add_zero] using hbound
  apply hcost.trans
  change _ ≤ expectedQueryCharge (otsOpeningRefinedQueryReserve accountingKey)
    (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
  rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
  exact le_add_self

noncomputable def sampledCanonicalCharge
    (charge : PublicParameter → (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' table, Pr[= table | sampleOtsHashTable] *
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        canonicalChargeAfterTable (charge parameter) adversary parameter table ftsSecret fuel

theorem sampledCanonicalCharge_le_refinedReserve
    (charge : PublicParameter → (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (fuel : Nat)
    (hcharge : ∀ parameter input context remaining cache,
      charge parameter input context remaining cache ≤ canonicalOtsOuterCharge parameter input context remaining cache) :
    sampledCanonicalCharge charge adversary fuel ≤ sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  unfold sampledCanonicalCharge sampledQueryCharge
  simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      canonicalChargeAfterTable (charge parameter) adversary parameter table ftsSecret fuel)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter otsSecret ftsSecret))
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (canonicalChargeAfterTable_le_gameReserve (charge parameter)
        adversary parameter table ftsSecret fuel (hcharge parameter)))
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled

noncomputable def sampledCanonicalWeightedCharge (adversary : Adversary) (fuel : Nat) : ENNReal :=
  sampledCanonicalCharge canonicalWeightedOuterCharge adversary fuel

theorem sampledCanonicalWeightedCharge_le_refinedReserve (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalWeightedCharge adversary fuel ≤ sampledQueryCharge otsOpeningRefinedQueryReserve adversary :=
  sampledCanonicalCharge_le_refinedReserve canonicalWeightedOuterCharge adversary fuel canonicalWeightedOuterCharge_le_ots

theorem sampledCanonicalComponentCharge_le_refinedReserve (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalCharge canonicalComponentOuterCharge adversary fuel ≤ sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  apply sampledCanonicalCharge_le_refinedReserve
  intro parameter input context remaining cache
  exact (canonicalComponentOuterCharge_le_weighted parameter input context remaining cache).trans
    (canonicalWeightedOuterCharge_le_ots parameter input context remaining cache)

theorem sampledCanonicalCharge_add
    (left right : PublicParameter → (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalCharge (fun parameter input context fuel cache => left parameter input context fuel cache +
      right parameter input context fuel cache) adversary fuel =
      sampledCanonicalCharge left adversary fuel + sampledCanonicalCharge right adversary fuel := by
  simp only [sampledCanonicalCharge, canonicalChargeAfterTable]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro table
  rw [← mul_add, ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro ftsSecret
  rw [← mul_add, ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro option
  cases option with
  | none => simp
  | some result =>
      dsimp only
      rw [expectedCanonicalQueryCharge_add, mul_add]

theorem sampledCanonicalCharge_mul
    (charge : PublicParameter → (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (factor : ENNReal) (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalCharge (fun parameter input context fuel cache => charge parameter input context fuel cache * factor) adversary fuel =
      sampledCanonicalCharge charge adversary fuel * factor := by
  simp only [sampledCanonicalCharge, canonicalChargeAfterTable]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro parameter
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  congr 1
  apply tsum_congr
  intro table
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  congr 1
  apply tsum_congr
  intro ftsSecret
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  congr 1
  apply tsum_congr
  intro option
  cases option with
  | none => simp
  | some result =>
      dsimp only
      rw [expectedCanonicalQueryCharge_mul, mul_assoc]

theorem sampledCanonical_components_le_refinedReserve (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalCharge unresolvedStartOuterCharge adversary fuel * (4 / 3) +
      sampledCanonicalCharge unresolvedPositionOuterCharge adversary fuel +
      sampledCanonicalCharge materializedOuterCandidateCharge adversary fuel * (4 / 3) ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  have hbound := sampledCanonicalComponentCharge_le_refinedReserve adversary fuel
  change sampledCanonicalCharge (fun parameter input context remaining cache =>
    unresolvedStartOuterCharge parameter input context remaining cache * (4 / 3) +
      unresolvedPositionOuterCharge parameter input context remaining cache +
      materializedOuterCandidateCharge parameter input context remaining cache * (4 / 3)) adversary fuel ≤ _ at hbound
  rw [sampledCanonicalCharge_add, sampledCanonicalCharge_add, sampledCanonicalCharge_mul, sampledCanonicalCharge_mul] at hbound
  exact hbound

theorem sampledCanonicalAccumulatedCharge_retained_eq
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    sampledCanonicalAccumulatedCharge parameter ftsSecret fuel
        (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩) charge =
      ∑' table, Pr[= table | sampleOtsHashTable] * canonicalChargeAfterTable charge adversary parameter table ftsSecret fuel := by
  unfold sampledCanonicalAccumulatedCharge canonicalChargeAfterTable
  apply tsum_congr
  intro table
  congr 1
  apply tsum_congr
  intro option
  by_cases hsupport : option ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases option with
    | none => rfl
    | some result =>
        dsimp only
        rw [(resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hsupport).1]
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

theorem sampledCanonicalCharge_eq_accumulated
    (charge : PublicParameter → (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalCharge charge adversary fuel =
      ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          sampledCanonicalAccumulatedCharge parameter ftsSecret fuel
            (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩) (charge parameter) := by
  simp only [sampledCanonicalCharge, sampledCanonicalAccumulatedCharge_retained_eq]
  apply tsum_congr
  intro parameter
  congr 1
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro ftsSecret
  apply tsum_congr
  intro table
  ring

end SphincsSecurity.Concrete.OtsProbeSimulation
