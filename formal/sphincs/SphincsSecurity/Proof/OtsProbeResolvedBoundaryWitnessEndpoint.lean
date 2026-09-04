import SphincsSecurity.Proof.OtsProbeResolvedBoundaryWitnessLift

/-!
# Retained boundary witness endpoint

The adaptive witness lift is specialized to the retained game after the public root. Finalization
cannot create a private structural failure from the related completable contexts, so any remaining
failure there is ordinary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def rootAwareMaterializedDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  rootAwareMaterializedDetailedBoundaryObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationDetailedObserve table value.1)
    context fuel table value.2

set_option maxRecDepth 100000 in
theorem relTriple_privateWitnessPlan_retainedFinalization_detailed
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (value : RetainedRestResult)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache) (candidates : List Probe)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (retainedResolvedFinalizationPrivateWitnessPlanObserve table root left leftFuel
        (value, leftCache) candidates)
      (retainedResolvedFinalizationDetailedObserve table root right rightFuel
        (value, rightCache))
      WitnessOrOrdinaryCovers := by
  have hleftNotPrivate := not_privateStructuralHit_of_deferredCompletable
    hcontext.leftCompletable
  have hrightNotPrivate := not_privateStructuralHit_of_deferredCompletable
    hcontext.rightCompletable
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve
    retainedResolvedFinalizationDetailedObserve classifyDirectObserve
  simp only [hleftNotPrivate, hrightNotPrivate, ↓reduceDIte, hcontext.rightCompletable,
    ↓reduceIte]
  have hbase : RelTriple
      (pure (none, candidates) : ProbComp PrivateWitnessPlanOutput)
      (DirectBoundaryOutcome.ofFailed <$>
        resolvedFinalizationObserve table right rightFuel ((root, value), rightCache))
      (fun _ _ ↦ True) := relTriple_true _ _
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro source outcome hrelation
  rcases hrelation with ⟨_, houtcome⟩
  rw [support_map] at houtcome
  rcases houtcome with ⟨failed, _hfailed, rfl⟩
  cases failed <;> simp [WitnessOrOrdinaryCovers, DirectBoundaryOutcome.ofFailed,
    DirectBoundaryOutcome.failed, DirectBoundaryOutcome.ordinary]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_granularPrivateWitnessPlan_rootAwareMaterializedDetailedRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : DeferredContext) (leftFuel rightFuel q : Nat)
    (leftCache rightCache : SplitHashCache)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (hqLeft : q ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + q ≤ rightFuel) :
    RelTriple
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret left leftFuel (root, leftCache) [])
      (rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret
        right rightFuel (root, rightCache))
      WitnessOrOrdinaryCovers := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    rootAwareMaterializedDetailedRetainedRestObserve
  apply relTriple_normalizedPrivateWitness_rootAwareMaterializedDetailed parameter root ftsSecret
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
      (retainedResolvedFinalizationPrivateWitnessPlanObserve table root)
      (retainedResolvedFinalizationDetailedObserve table root) [] left right leftFuel rightFuel
      table leftCache rightCache q q hbound hcontext hcache hrevealed hvalues hpublished
      hrightMaterialized hcanonical hqLeft hleftUpper hrightLower
  intro value nextLeft nextRight nextLeftFuel nextRightFuel nextLeftCache nextRightCache
    nextCandidates hnextContext _hnextFuel _hnextCache _hnextRevealed _hnextValues
    _hnextPublished _hnextMaterialized _hnextCanonical
  simpa only using
    (relTriple_privateWitnessPlan_retainedFinalization_detailed table root value nextLeft nextRight
      nextLeftFuel nextRightFuel nextLeftCache nextRightCache nextCandidates hnextContext)

noncomputable def rootAwareMaterializedBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (fun context remaining value =>
      classifyDirectDetailedObserve table
        (rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret)
        context remaining value)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    (2 * fuel) table (maskedPublishedTreeRoot.run emptySplitHashCache)

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_granularAllCanonicalPrivateWitnessPlan_rootAwareMaterializedBoundary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret q)
      (rootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret q)
      WitnessOrOrdinaryCovers := by
  let initial : DeferredContext := emptyWitnessDeferredContext
  let materializedInitial : DeferredContext :=
    directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
  have hcontext : FinalizationContextLE table initial materializedInitial :=
    finalizationContextLE_empty table
  have hstep := (witnessMaterializedStableCouples_maskedPublishedTreeRoot table)
    initial materializedInitial q (2 * q) emptySplitHashCache emptySplitHashCache hcontext
      (by omega) rfl rfl (fun _ _ hvalue => hvalue) publishedValues_empty rfl
  unfold granularAllCanonicalPrivateWitnessPlan
    rootAwareMaterializedBoundaryDetailedRetainedOutcome runDirectWitnessPlanObserve
    runDirectDetailedObserve
  apply relTriple_finishDirectWitnessPlan_detailed_of_materializedStable table
  · simpa [initial, materializedInitial] using hstep
  · intro leftResult rightResult hleftSupport hrightSupport hclean
    have hcanonicalRun := hclean.canonicalize_left
    let canonical := canonicalizeMaterializedValues table leftResult.context
    have hleftCompletable := hcanonicalRun.context_le.leftCompletable
    have hleftNotPrivate :=
      not_privateStructuralHit_of_deferredCompletable hleftCompletable
    have hrightNotPrivate :=
      not_privateStructuralHit_of_deferredCompletable
        hcanonicalRun.context_le.rightCompletable
    simp only [canonicalizeDirectWitnessPlanObserve, hleftNotPrivate, ↓reduceDIte,
      hclean.left_published, ↓reduceIte, classifyDirectWitnessPlanObserve,
      hleftCompletable, classifyDirectDetailedObserve, hrightNotPrivate,
      hcanonicalRun.context_le.rightCompletable]
    have hleftFuelPreserved : q ≤ leftResult.remaining := by
      have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table leftResult 0
        (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (by
          simpa [initial] using hleftSupport)
      omega
    have hrightFuelPreserved : 2 * q ≤ rightResult.remaining := by
      have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) materializedInitial (2 * q) table
        rightResult 0 (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (by
          simpa [materializedInitial] using hrightSupport)
      omega
    have hleftRemainingUpper : leftResult.remaining ≤ q :=
      remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table leftResult (by
          rw [← map_erase_runDirectResolvedWitnessFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table, support_map]
          exact ⟨.done leftResult, by simpa [initial] using hleftSupport, rfl⟩)
    change RelTriple
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret canonical leftResult.remaining
          (leftResult.value.1, leftResult.value.2) [])
      (rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret
        rightResult.context rightResult.remaining
          (rightResult.value.1, rightResult.value.2))
      WitnessOrOrdinaryCovers
    rw [← hclean.value_eq]
    exact relTriple_granularPrivateWitnessPlan_rootAwareMaterializedDetailedRetainedRest
        adversary parameter leftResult.value.1 table ftsSecret canonical rightResult.context
        leftResult.remaining rightResult.remaining q leftResult.value.2 rightResult.value.2
        (hbound leftResult.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
        hcanonicalRun.revealed_eq hcanonicalRun.values_le hcanonicalRun.left_published
        hcanonicalRun.right_materialized
        (canonicalizeMaterializedValues_canonical table leftResult.context
          hclean.context_le.view.leftConsistent)
        hleftFuelPreserved hleftRemainingUpper (by omega)
  · intro leftRun rightResult _hrightSupport hdoomed
    have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
      rightResult.context hdoomed.2
    have hnotCompletable : ¬DeferredCompletable table rightResult.context :=
      hdoomed.1.2.2.2
    simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
      (relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers leftRun)

end SphincsSecurity.Concrete.OtsProbeSimulation
