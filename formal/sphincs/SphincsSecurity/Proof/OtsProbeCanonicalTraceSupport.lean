import SphincsSecurity.Proof.OtsProbeCanonicalRetainedTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem mem_support_raw_of_synchronizedCanonicalRom
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (result : ResolvedRunResult (α × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support (runSynchronizedResolved
      (fun query => canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl query))
      computation context fuel table cache)) :
    some result ∈ support (runResolvedFromTable context fuel table ((simulateQ (probingRomImpl parameter) computation).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure _ value context fuel table cache hcomplete] at hresult
        simpa [simulateQ_pure, runResolvedFromTable] using hresult
      · rw [runSynchronizedResolved_pure_of_not_completable _ value context fuel table cache hcomplete] at hresult
        simp at hresult
  | query_bind input next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · simp only [dif_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨stepOption, hstep, htail⟩ := hresult
        have hraw := (mem_support_iff_of_evalDist_eq
          (evalDist_canonicalChronologicalAdversaryImpl_oracle_eq_raw parameter root ftsSecret input context fuel table cache
            hconsistent hstarts hcanonical hpublished) stepOption).mp hstep
        cases stepOption with
        | none => simp at htail
        | some step =>
            have hcore := resolvedCore_of_mem_runResolvedFromTable ((probingRomImpl parameter input).run cache)
              context fuel table step hconsistent hstarts hraw
            have hnextCanonical := canonicalMaterializedValues_of_mem_probingRomImpl parameter input context fuel table cache
              step hconsistent hstarts hcanonical hpublished hraw
            have hnextPublished := resolvedPreservesPublishedValuesImpl_probingRomImpl parameter input context cache fuel table
              step hpublished hraw
            change some result ∈ support (runSynchronizedResolved
              (fun query => canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl query))
              (next step.value.1) step.context step.remaining step.table step.value.2) at htail
            rw [hcore.1] at htail
            rw [simulateQ_query_bind, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff]
            refine ⟨some step, hraw, ?_⟩
            dsimp only
            rw [hcore.1]
            exact ih step.value.1 step.context step.remaining step.value.2 hcore.2.1 hcore.2.2 hnextCanonical hnextPublished htail
      · simp [hcomplete] at hresult

set_option maxRecDepth 100000 in
theorem deferredCompletable_of_mem_synchronized
    (impl : ResolvedQueryImpl spec) (computation : OracleComp spec α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hresult : some result ∈ support (runSynchronizedResolved impl computation context fuel table cache)) :
    DeferredCompletable result.table result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure impl value context fuel table cache hcomplete] at hresult
        simp only [mem_support_pure_iff, Option.some.injEq] at hresult
        subst result
        exact hcomplete
      · rw [runSynchronizedResolved_pure_of_not_completable impl value context fuel table cache hcomplete] at hresult
        simp at hresult
  | query_bind input next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      split_ifs at hresult
      · rw [mem_support_bind_iff] at hresult
        obtain ⟨stepOption, _hstep, htail⟩ := hresult
        cases stepOption with
        | none => simp at htail
        | some step => exact ih step.value.1 step.context step.remaining step.table step.value.2 htail
      · simp at hresult

theorem mem_support_synchronized_of_canonicalQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : result ∈ support (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    result.1 ∈ support (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      computation context fuel table cache) := by
  apply (mem_support_iff_of_evalDist_eq (runCanonicalQueryTrace_synchronized_projection parameter root ftsSecret
    computation context fuel table cache hconsistent hstarts) result.1).mp
  rw [support_map]
  exact ⟨result, hresult, rfl⟩

theorem mem_support_runResolved_map_value
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (mapValue : α → β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    some (ResolvedRunResult.mk result.context result.remaining (mapValue result.value) result.table) ∈
      support (runResolvedFromTable context fuel table (mapValue <$> computation)) := by
  rw [map_eq_bind_pure_comp, runResolvedFromTable_bind, mem_support_bind_iff]
  refine ⟨some result, hresult, ?_⟩
  simp [runResolvedFromTable]

theorem mem_support_canonicalVerifierFinish_of_rest
    (parameter : PublicParameter) (root : Digest) (forgeryLog : Forgery × QueryLog SigningSpec)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (RetainedRestResult × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((simulateQ (probingRomImpl parameter) (do
        let verified ← scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature
        pure (forgeryLog, verified))).run cache))) :
    some (retainedResultWithRoot root result) ∈ support
      (runResolvedFromTable context fuel table ((canonicalVerifierFinish parameter root forgeryLog).run cache)) := by
  have hmap := mem_support_runResolved_map_value _ (fun value : RetainedRestResult × SplitHashCache =>
    ((root, value.1), value.2)) context fuel table result hresult
  simpa only [retainedResultWithRoot, canonicalVerifierFinish, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure] using hmap

set_option maxRecDepth 100000 in
theorem mem_support_split_of_synchronizedCanonicalRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (result : ResolvedRunResult (RetainedRestResult × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context)
    (hresult : some result ∈ support (runSynchronizedResolved
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (retainedGameRestComputation adversary ⟨root, parameter⟩) context fuel table cache)) :
    some (retainedResultWithRoot root result) ∈ support (do
      let step ← runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel table cache
      canonicalVerifierContinuation parameter root step) := by
  unfold retainedGameRestComputation at hresult
  rw [runSynchronizedResolved_bind, mem_support_bind_iff] at hresult
  obtain ⟨stepOption, hstep, htail⟩ := hresult
  cases stepOption with
  | none => simp at htail
  | some step =>
      have hcore := resolvedCore_of_mem_runSynchronizedResolved_canonicalChronological parameter root table ftsSecret
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel cache step
        hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hstep
      have hnextCanonical := canonicalMaterializedValues_of_mem_synchronizedCanonical parameter root ftsSecret
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel table cache step
        hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hcanonical hstep
      have hrel := relTriple_runSynchronizedResolved_reachable
        (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel cache actualCache hinvariant hvisible hpublished
      obtain ⟨actual, _hactual, hrelation⟩ := exists_right_of_relTriple_of_mem_support hrel hstep
      dsimp only at htail
      rw [hcore.1] at htail
      rcases hrelation with hclean | hdoomed
      · have hlift : liftOracleWorldLeft (do
            let verified ← scheme.verify ⟨root, parameter⟩ step.value.1.1.message step.value.1.1.signature
            pure (step.value.1, verified)) = (do
              let verified ← liftOracleWorldLeft
                (scheme.verify ⟨root, parameter⟩ step.value.1.1.message step.value.1.1.signature)
              pure ((step.value.1.1, step.value.1.2), verified)) := by
          simp only [liftOracleWorldLeft, liftM_bind, liftM_pure]
        rw [← hlift, runSynchronizedResolved_liftOracleWorldLeft] at htail
        have hraw := mem_support_raw_of_synchronizedCanonicalRom parameter root ftsSecret _ step.context step.remaining
          table step.value.2 result hcore.2.1 hcore.2.2 hnextCanonical hclean.2.2.2.2 htail
        rw [mem_support_bind_iff]
        refine ⟨some step, hstep, ?_⟩
        dsimp only [canonicalVerifierContinuation]
        rw [hcore.1]
        exact mem_support_canonicalVerifierFinish_of_rest parameter root step.value.1 step.context step.remaining
          table step.value.2 result hraw
      · rw [runSynchronizedResolved_of_not_completable _ _ step.context step.remaining table step.value.2 hdoomed.2.2.2] at htail
        simp at htail

set_option maxRecDepth 100000 in
theorem canonicalChronologicalSupported_of_root_and_retainedTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (rootResult : ResolvedRunResult (Digest × SplitHashCache))
    (result : ResolvedRunResult (RetainedRestResult × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hroot : some rootResult ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (htrace : (some result, history) ∈ support (runCanonicalQueryTrace parameter rootResult.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
      rootResult.context rootResult.remaining rootResult.table rootResult.value.2)) :
    CanonicalChronologicalSupported adversary parameter table ftsSecret fuel
      (retainedResultWithRoot rootResult.value.1 result) := by
  have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel rootResult hroot
  rw [hcore.1] at htrace
  have hrun := mem_support_synchronized_of_canonicalQueryTrace parameter rootResult.value.1 ftsSecret _ rootResult.context
    rootResult.remaining table rootResult.value.2 (some result, history) hcore.2.1 hcore.2.2 htrace
  dsimp only at hrun
  have hcanonical := canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel rootResult hroot
  have hrel := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  obtain ⟨actual, _hactual, hrelation⟩ := exists_right_of_relTriple_of_mem_support hrel hroot
  rcases hrelation with hclean | hdoomed
  · unfold CanonicalChronologicalSupported canonicalChronologicalRetainedRunAfterFtsSecrets
    rw [mem_support_bind_iff]
    refine ⟨some rootResult, hroot, ?_⟩
    dsimp only
    rw [hcore.1]
    exact mem_support_split_of_synchronizedCanonicalRetainedRest adversary parameter rootResult.value.1 table ftsSecret
      rootResult.context rootResult.remaining rootResult.value.2 actual.2 result hclean.2.2.1 hclean.2.2.2.1
      hclean.2.2.2.2 hcanonical hrun
  · rw [runSynchronizedResolved_of_not_completable _ _ rootResult.context rootResult.remaining table rootResult.value.2
      hdoomed.2.2.2] at hrun
    simp at hrun

theorem supported_and_completable_of_mem_canonicalRetainedTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) (history : List CanonicalQuerySelection)
    (htrace : (some result, history) ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)) :
    CanonicalChronologicalSupported adversary parameter table ftsSecret fuel result ∧
      DeferredCompletable result.table result.context := by
  unfold canonicalRetainedQueryTrace at htrace
  rw [mem_support_bind_iff] at htrace
  obtain ⟨rootOption, hroot, hrest⟩ := htrace
  cases rootOption with
  | none => simp at hrest
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨restOption, restHistory⟩, hrest, hreturn⟩ := hrest
      cases restOption with
      | none => simp at hreturn
      | some rest =>
          simp only [Option.map_some, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hreturn
          obtain ⟨rfl, rfl⟩ := hreturn
          refine ⟨canonicalChronologicalSupported_of_root_and_retainedTrace adversary parameter table ftsSecret fuel
            rootResult rest history hroot hrest, ?_⟩
          have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel rootResult hroot
          rw [hcore.1] at hrest
          have hrun := mem_support_synchronized_of_canonicalQueryTrace parameter rootResult.value.1 ftsSecret _ rootResult.context
            rootResult.remaining table rootResult.value.2 (some rest, history) hcore.2.1 hcore.2.2 hrest
          exact deferredCompletable_of_mem_synchronized _ _ _ _ _ _ rest hrun

theorem not_winningRetainedVerifyProbe_of_canonicalRetainedTrace_relation
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) (history : List CanonicalQuerySelection)
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (htrace : (some result, history) ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result) (actualValue, actualCache)) :
    ¬WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret (actualValue, actualCache) := by
  intro hwitness
  obtain ⟨hsupported, hcomplete⟩ := supported_and_completable_of_mem_canonicalRetainedTrace adversary parameter table ftsSecret
    fuel result history htrace
  have hnot := not_deferredCompletable_of_winningRetainedVerifyProbe_canonical adversary parameter table ftsSecret fuel result
    actualValue actualCache hsupported hactual hrelation hwitness
  have htable : result.table = table := by
    rcases hrelation with hclean | hdoomed
    · exact hclean.1
    · exact hdoomed.1
  exact hnot (htable ▸ hcomplete)

end SphincsSecurity.Concrete.OtsProbeSimulation
