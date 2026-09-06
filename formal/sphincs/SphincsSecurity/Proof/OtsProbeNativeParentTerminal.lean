import SphincsSecurity.Proof.OtsProbeNativeParentTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem mem_support_raw_of_nativeQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (htrace : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    some result ∈ support (runResolvedFromTable context fuel table
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)) := by
  have hm : some result ∈ support (Prod.fst <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) := by
    rw [support_map]
    exact ⟨(some result, history), htrace, rfl⟩
  rw [mem_support_iff_of_evalDist_eq (runNativeQueryTrace_result_projection parameter root ftsSecret computation context fuel table cache
    hconsistent hstarts), support_map] at hm
  obtain ⟨raw, hraw, hretain⟩ := hm
  cases raw with
  | none => simp [retainCompletableResult] at hretain
  | some raw =>
      simp only [retainCompletableResult] at hretain
      split_ifs at hretain
      · cases Option.some.inj hretain
        exact hraw

theorem maskedChronologicalRetainedGame_eq_root_rest
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache = (do
      let root ← maskedPublishedTreeRoot.run emptySplitHashCache
      let rest ← (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root.1 ftsSecret)
        (retainedGameRestComputation adversary ⟨root.1, parameter⟩)).run root.2
      pure ((root.1, rest.1), rest.2)) := by
  simp only [simulateQ_chronological_retainedGameRestComputation,
    maskedChronologicalRetainedGameAfterFtsSecrets, maskedChronologicalRetainedPrefixAfterFtsSecrets,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

theorem mem_support_raw_of_nativeRetainedParentTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hresult : (some result, history) ∈ support (nativeRetainedParentTrace adversary parameter table ftsSecret fuel)) :
    some result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)) := by
  rw [nativeRetainedParentTrace, mem_support_bind_iff] at hresult
  obtain ⟨root, hroot, hrest⟩ := hresult
  cases root with
  | none => simp at hrest
  | some root =>
      dsimp only at hrest
      rw [bind_pure_comp, support_map] at hrest
      obtain ⟨⟨rest, restHistory⟩, hrest, heq⟩ := hrest
      cases rest with
      | none => simp at heq
      | some rest =>
          have hresultEq : retainedResultWithRoot root.value.1 rest = result := Option.some.inj (congrArg Prod.fst heq)
          subst result
          have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext ∅) fuel table root
            (ensuredInitialContext_valid ∅).valuesConsistent
            (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table)) hroot
          have hraw := mem_support_raw_of_nativeQueryTrace parameter root.value.1 ftsSecret _ root.context root.remaining
            root.table root.value.2 rest restHistory hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hrest
          have hmap := mem_support_runResolved_map_value _
            (fun value : RetainedRestResult × SplitHashCache => ((root.value.1, value.1), value.2))
            root.context root.remaining root.table rest hraw
          have hempty : ensuredInitialContext ∅ =
              ({ state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } : DeferredContext) := by
            simp only [ensuredInitialContext, Finset.image_empty]
            rfl
          rw [← hempty, maskedChronologicalRetainedGame_eq_root_rest, runResolvedFromTable_bind, mem_support_bind_iff]
          refine ⟨some root, hroot, ?_⟩
          simpa only [bind_pure_comp, retainedResultWithRoot] using hmap

theorem nativeRetainedParentTrace_finish
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (nativeRetainedParentTrace adversary parameter table ftsSecret fuel >>= fun trace => finishResolvedRunIsNone trace.1) =
      nativeTerminalFailureAfterRoot ∅ adversary parameter table ftsSecret fuel := by
  simp only [nativeRetainedParentTrace, nativeTerminalFailureAfterRoot, nativeChainTraceAfterRoot, bind_assoc]
  apply bind_congr
  intro root
  cases root with
  | none => rfl
  | some root => simp only [bind_assoc, pure_bind, finishResolvedRunIsNone_retainedRoot]

def ParentOrRetainedOtsWitness (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  EarlyOtsParentAtQuery parameter
    (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret result ∨
    WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret (result.1.1, result.1.2.1.cache)

theorem probEvent_parentOrRetainedOtsWitness_le_nativeTerminalFailure
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[ParentOrRetainedOtsWitness parameter table ftsSecret | prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot ∅ adversary parameter table ftsSecret fuel] := by
  have hcoupled := relTriple_nativeRetainedParentTrace_prehit adversary parameter table ftsSecret fuel
  have hs := FtsProbeSimulation.relTriple_and_right_support
    (FtsProbeSimulation.relTriple_and_left_support hcoupled
      (fun result => result ∈ support (nativeRetainedParentTrace adversary parameter table ftsSecret fuel))
      (by intro _ hresult; exact hresult))
  have hbound : Pr[ParentOrRetainedOtsWitness parameter table ftsSecret |
      prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun result => result.1 = none | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] := by
    apply probEvent_le_of_relTriple (relTriple_symm hs)
    rintro actual ⟨native, history⟩ hrel (hearly | hwitness)
    · exact hrel.1.1.2 hearly
    · cases native with
      | none => rfl
      | some result =>
          have hcanonical := hrel.1.1.1.1.1
          have hreachable : ReachableResolvedRunRel parameter table (some result) (actual.1.1, actual.1.2.1.cache) :=
            Or.inl ⟨hcanonical.1, hcanonical.2.1, hcanonical.2.2.1, hcanonical.2.2.2.1, hcanonical.2.2.2.2.1⟩
          have hactual : (actual.1.1, actual.1.2.1.cache) ∈ support
              (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
            rw [← prehitRetainedQueryTrace_cache_projection, support_map]
            exact ⟨actual, hrel.2, rfl⟩
          exact False.elim ((not_deferredCompletable_of_winningRetainedVerifyProbe adversary parameter table ftsSecret
            fuel result actual.1.1 actual.1.2.1.cache
            (mem_support_raw_of_nativeRetainedParentTrace adversary parameter table ftsSecret fuel result history hrel.1.2)
            hactual hreachable hwitness) hcanonical.2.2.1.2.2.2.1)
  apply hbound.trans
  rw [← nativeRetainedParentTrace_finish, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro trace
  by_cases hnone : trace.1 = none
  · rw [if_pos hnone, hnone]
    simp [finishResolvedRunIsNone, finishResolvedRun]
  · simp [hnone]

end SphincsSecurity.Concrete.OtsProbeSimulation
