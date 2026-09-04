import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedResolved

/-!
# Reverse signer normalization

The complete masked signer preserves exact clean-finalization semantics across a deferred context
and its materialized shadow. Canonicalizing a direct result and rematerializing it recovers the
operational state, while published canonical observers depend only on the common finalization view.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_maskedSignAfterDigest
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    FinalizationMaterializedCouples table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
    (finalizationMaterializedCouples_ordinaryHashImpl table)
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro ftsPath
  apply (finalizationMaterializedCouples_sequenceFin
    (fun lay : Layer ↦ maskedSignLayer parameter ftsSecret index lay)
    (fun lay ↦ finalizationMaterializedCouples_maskedSignLayer table parameter ftsSecret
      index lay)).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact finalizationMaterializedCouples_pure table none
  | some parts =>
      apply (finalizationMaterializedCouples_sequenceFin
        (fun lay : Layer ↦ revealLayerValues index lay (parts lay).2)
        (fun lay ↦ finalizationMaterializedCouples_revealLayerValues table index lay
          (parts lay).2)).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree ↦ ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay ↦ (parts lay).1
          chainValue := fun lay ↦ (revealed lay).1
          authPath := flattenPaths fun lay ↦ (revealed lay).2 }
      exact finalizationMaterializedCouples_pure table (some signature)

set_option maxRecDepth 100000 in
theorem finalizationMaterializedCouples_maskedSign
    (table : OtsSecretIndex → HashOutput) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    FinalizationMaterializedCouples table
      (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (finalizationMaterializedCouples_simulateQ ordinaryRomImpl
    (finalizationMaterializedCouples_ordinaryRomImpl table)
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ ↦ 0, ftsSecret⟩ message)).bind
  intro selected
  cases selected with
  | none => exact finalizationMaterializedCouples_pure table none
  | some data =>
      exact finalizationMaterializedCouples_maskedSignAfterDigest table parameter ftsSecret
        data.1 data.2.1 data.2.2

theorem finalizationContextEq_materializedDeferredContext
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    FinalizationContextEq table (some context)
      (some (materializedDeferredContext context)) := by
  have hle := finalizationContextLE_materializedDeferredContext hvalid hcompletable
  refine ⟨{
    leftConsistent := hle.view.leftConsistent
    rightConsistent := hle.view.rightConsistent
    leftStarts := hle.view.leftStarts
    rightStarts := hle.view.rightStarts
    valueEq := hle.view.valueEq
    leftClean := hle.view.leftClean
    rightClean := hle.view.rightClean
    pendingEq := ?_ }, hvalid, hle.rightValid, hcompletable⟩
  intro coordinate _hnone
  rfl

theorem materializedDeferredState_canonicalize_direct_eq
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hstarts : StartTableAgrees state table)
    (hchainValid : ChainState.ValidFor (fun _ ↦ True) state) :
    materializedDeferredState
        (canonicalizeMaterializedValues table (directDeferredContext state)) = state := by
  cases state with
  | mk pending values revealed ensured =>
    simp only [materializedDeferredState, canonicalizeMaterializedValues,
      directDeferredContext]
    congr
    funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        by_cases hrevealed : Coordinate.chainStart lay tree leafIdx chainIdx ∈ revealed
        · have hvalue := (hchainValid (.chainStart lay tree leafIdx chainIdx)
            (by simp [IsChainCoordinate])).2.1 hrevealed
          obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
          have htable := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output houtput
          simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue]
          have houtput' : values (.chainStart lay tree leafIdx chainIdx) = some output := by
            simpa using houtput
          exact (congrArg some htable).symm.trans houtput'.symm
        · have hvalue : values (.chainStart lay tree leafIdx chainIdx) = none := by
            by_contra hne
            exact hrevealed ((hchainValid (.chainStart lay tree leafIdx chainIdx)
              (by simp [IsChainCoordinate])).1 hne)
          simp [publicMaterializedValues, hrevealed, hvalue]
    | position position =>
        by_cases hrevealed : Coordinate.position position ∈ revealed
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            resolvedCompletionValue, DeferredContext.positionValue, directDeferredValues]
          cases values (.position position) <;> simp
        · simp only [publicMaterializedValues, hrevealed, ↓reduceIte,
            DeferredContext.positionValue, directDeferredValues]

theorem evalDist_negatedCanonicalizeDirectDelayedObserve_eq_of_finalizationContextEq_published
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hrevealed : left.state.revealed = right.state.revealed)
    (hleftPublished : PublishedValues left.state)
    (hrightPublished : PublishedValues right.state)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    evalDist
        (negatedDirectDelayedObserve
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations left fuel value) =
      evalDist
        (negatedDirectDelayedObserve
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations right fuel value) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  have hleftCanonical := valid_completable_canonicalizeMaterializedValues table left
    hleftValid hleftCompletable
  have hrightCanonical := valid_completable_canonicalizeMaterializedValues table right
    hrightValid hrightCompletable
  have hleftNoHit : ¬PrivateStructuralHit (canonicalizeMaterializedValues table left) :=
    not_privateStructuralHit_of_deferredCompletable hleftCanonical.2
  have hrightNoHit : ¬PrivateStructuralHit (canonicalizeMaterializedValues table right) :=
    not_privateStructuralHit_of_deferredCompletable hrightCanonical.2
  unfold negatedDirectDelayedObserve canonicalizeDirectDelayedSelectedRootIndicator
  simp only [hleftNoHit, hrightNoHit, hleftPublished, hrightPublished,
    hleftCanonical.2, hrightCanonical.2, ↓reduceIte]
  have hcanonical := canonicalizedFinalizationContextEq
    (⟨hview, hleftValid, hrightValid, hleftCompletable⟩ :
      FinalizationContextEq table (some left) (some right)) hrevealed
  exact ObserverSynchronized.eq_of_synchronized
    (table := table)
    (observe := negatedDirectDelayedObserve observe snapshots observations)
    (canonicalizeMaterializedValues table left)
    (canonicalizeMaterializedValues table right) fuel value hcanonical.1 hcanonical.2 hrevealed

theorem relTriple_finishObserve_reverse_of_finalizationMaterialized
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (Option (ResolvedRunResult (α × SplitHashCache))))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hstep : RelTriple leftRun rightRun (FinalizationMaterializedRunEq table))
    (hrecursive : ∀ left right,
      FinalizationMaterializedRunEq table (some left) (some right) →
      RelTriple
        (rightObserve right.context right.remaining right.value)
        (leftObserve left.context left.remaining left.value)
        BoolImp) :
    RelTriple
      (rightRun >>= finishObserve rightObserve)
      (leftRun >>= finishObserve leftObserve)
      BoolImp := by
  apply relTriple_bind (relTriple_symm hstep)
  intro right left hrelation
  cases right with
  | none =>
      cases left with
      | none => exact relTriple_pure_pure (by simp [BoolImp])
      | some left => simp [FinalizationMaterializedRunEq] at hrelation
  | some right =>
      cases left with
      | none => simp [FinalizationMaterializedRunEq] at hrelation
      | some left => exact hrecursive left right hrelation

set_option maxRecDepth 100000 in
theorem evalDist_complement_observed_probeFree_eq_runDirectResolvedObserve
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (continuation : LazyRevealProbe.State Coordinate → Nat → α → ProbComp Bool)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    evalDist (Bool.not <$> (runObservedCleanFromTable observations state fuel table computation >>=
      fun result ↦ match result with
      | none => pure false
      | some result => continuation result.state result.remaining result.value)) =
      evalDist (runDirectResolvedObserve
        (fun context remaining value ↦
          Bool.not <$> continuation context.state remaining value)
        (directDeferredContext state) fuel table computation) := by
  rw [map_bind]
  have hobserved := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
    observations state fuel table hprobeFree
  rw [← hobserved, map_eq_bind_pure_comp, bind_assoc]
  have hclean := map_projectResolvedRunResult_runDirect_eq_runClean computation state fuel table
  rw [← hclean, map_eq_bind_pure_comp, bind_assoc]
  unfold runDirectResolvedObserve
  apply evalDist_bind_congr
  intro result _hresult
  cases result <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
