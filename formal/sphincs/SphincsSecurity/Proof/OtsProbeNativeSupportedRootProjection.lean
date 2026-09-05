import SphincsSecurity.Proof.OtsProbeNativeSupportedAllowances
import SphincsSecurity.Proof.OtsProbeNativeRootHitProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem nativeTrace_rootHistoryMatch_selectedHit_of_hashLength
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hsource : ¬UnknownSourceFinalRootMatch parameter (some result, history))
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : result.context.positionValue (layerRootPosition lay tree) = some output)
    (hhidden : .position (layerRootPosition lay tree) ∉ result.context.state.revealed)
    (hmatch : truncateHash output ∈ nativeRootCandidateHistory parameter (layerRootPosition lay tree) history)
    (q : Nat) (hlength : (nativeHashQueryHistory history).length ≤ q) :
    ∃ ordinal ∈ Finset.range q,
      NativeRootHistorySelectionHit parameter (layerRootPosition lay tree) (nativeHashHistorySelection history ordinal) := by
  obtain ⟨completion, hcompletion⟩ := (nativeTrace_finalCore parameter root ftsSecret computation context fuel table cache result history
    hconsistent hstarts hresult).2.2
  obtain ⟨prior, selection, suffix, hhistory, hprior, hstored, hhidden, hcandidate⟩ :=
    nativeTrace_rootHistoryMatch_firstCharged parameter root ftsSecret computation context fuel table cache result history completion
      hconsistent hstarts hmat hclosed hresult hcompletion hsource lay tree output hvalue hhidden hmatch
  have hhash : IsOuterHash selection.input := by
    cases hinput : selection.input with
    | inl query =>
        cases query with
        | inl n => simp [chargedNativeRootQueryCandidate, hinput] at hcandidate
        | inr input => trivial
    | inr message => simp [chargedNativeRootQueryCandidate, hinput] at hcandidate
  have hpriorLength : (nativeHashQueryHistory prior).length < q := by
    rw [hhistory] at hlength
    simp only [nativeHashQueryHistory, List.filter_append, List.filter_cons, hhash, decide_true, ↓reduceIte,
      List.length_append, List.length_cons] at hlength ⊢
    omega
  refine ⟨(nativeHashQueryHistory prior).length, Finset.mem_range.mpr hpriorLength,
    nativeHashQueryHistory prior, selection, output, ?_, hstored, hhidden, ?_, hcandidate⟩
  · rw [hhistory]
    exact nativeHashHistorySelection_append_hash prior selection suffix hhash
  · simpa only [nativeRootCandidateHistory_hashHistory] using hprior

theorem probEvent_nativeFinalRootHistoryMatch_le_cutHitSum_of_supportedCount
    (parameter : PublicParameter) (root : Digest) (lay : Layer) (tree : TreeIndex) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (q : Nat) (hbound : ∀ trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache),
      canonicalTraceHashCount trace.2 ≤ q) :
    Pr[NativeFinalRootHistoryMatch parameter (layerRootPosition lay tree) |
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] ≤
      ∑ ordinal ∈ Finset.range q,
        Pr[fun b => b = false | originalChargedRootCutObservation parameter root (layerRootPosition lay tree) ftsSecret computation
          context fuel table cache ∅ ordinal (fun pair => pair.2 = some (truncateHash pair.1))] := by
  calc
    _ ≤ Pr[fun trace => ∃ ordinal ∈ Finset.range q,
        NativeRootHistorySelectionHit parameter (layerRootPosition lay tree) (nativeHashHistorySelection trace.2 ordinal) |
        runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] := by
      apply probEvent_mono
      rintro ⟨option, history⟩ htrace ⟨result, output, heq, hvalue, hhidden, hmatch, hsource⟩
      dsimp only at heq
      subst option
      exact nativeTrace_rootHistoryMatch_selectedHit_of_hashLength parameter root ftsSecret computation context fuel table cache result history
        hconsistent hstarts hmat hclosed htrace hsource lay tree output hvalue hhidden hmatch q (by rw [← canonicalTraceHashCount_eq_nativeHashLength]; exact hbound (some result, history) htrace)
    _ ≤ ∑ ordinal ∈ Finset.range q,
        Pr[fun trace => NativeRootHistorySelectionHit parameter (layerRootPosition lay tree) (nativeHashHistorySelection trace.2 ordinal) |
          runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] :=
      probEvent_exists_finset_le_sum (Finset.range q) _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ordinal _
      exact probEvent_nativeHistorySelectionHit_le_originalChargedRootCut parameter root (layerRootPosition lay tree) ftsSecret computation ordinal
        context fuel table cache hconsistent hstarts

theorem probEvent_nativeRetainedFinalRootMatch_le_initializedCutHitSum
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) (lay : Layer) (tree : TreeIndex) :
    Pr[NativeFinalRootHistoryMatch parameter (layerRootPosition lay tree) |
      nativeChainTraceAfterRoot targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] ≤
      ∑ ordinal ∈ Finset.range q,
        Pr[fun b => b = false | initializedChargedRootCutObservation targets adversary parameter (layerRootPosition lay tree)
          table ftsSecret fuel ordinal (fun pair => pair.2 = some (truncateHash pair.1))] := by
  unfold nativeChainTraceAfterRoot initializedChargedRootCutObservation
  simp only [probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro root
  by_cases hroot : root ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases root with
    | none => simp [NativeFinalRootHistoryMatch]
    | some root =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext targets) fuel table root
          (ensuredInitialContext_valid targets).valuesConsistent
          (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hroot
        have hmat := rootMaterializationPreserving_maskedPublishedTreeRoot (ensuredInitialContext targets) fuel table emptySplitHashCache root
          (layerRootsMaterialized_ensuredInitialContext targets) (ensuredInitialContext_computed targets) hroot
        have hclosed := (ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table root hroot
        simp only [← Finset.mul_sum, hcore.1]
        apply mul_le_mul_right
        apply probEvent_nativeFinalRootHistoryMatch_le_cutHitSum_of_supportedCount parameter root.value.1 lay tree ftsSecret
          (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩) root.context root.remaining table root.value.2
          hcore.2.1 hcore.2.2 hmat hclosed q
        intro trace htrace
        apply nativeRetainedTraceAfterRoot_hashCount_le targets adversary q hq parameter hparameter table ftsSecret hfts fuel trace
        rw [nativeChainTraceAfterRoot, mem_support_bind_iff]
        refine ⟨some root, hroot, ?_⟩
        simpa only [hcore.1] using htrace
  · simp [probOutput_eq_zero_of_not_mem_support hroot]

theorem probEvent_exists_nativeRetainedFinalRootMatch_le_initializedCutHitSum
    (targets roots : Finset Position) (hroots : ∀ target ∈ roots, IsLayerRoot target)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun trace => ∃ target ∈ roots, NativeFinalRootHistoryMatch parameter target trace |
      nativeChainTraceAfterRoot targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] ≤
      ∑ target ∈ roots, ∑ ordinal ∈ Finset.range q,
        Pr[fun b => b = false | initializedChargedRootCutObservation targets adversary parameter target
          table ftsSecret fuel ordinal (fun pair => pair.2 = some (truncateHash pair.1))] := by
  apply (probEvent_exists_finset_le_sum roots _ _).trans
  apply Finset.sum_le_sum
  intro target htarget
  obtain ⟨lay, tree, rfl⟩ := hroots target htarget
  exact probEvent_nativeRetainedFinalRootMatch_le_initializedCutHitSum targets adversary q hq parameter hparameter table ftsSecret hfts fuel lay tree

end SphincsSecurity.Concrete.OtsProbeSimulation
