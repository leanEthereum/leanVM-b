import SphincsSecurity.Proof.OtsProbeCanonicalFuel

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

def CanonicalQueryRejects
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (entry : CanonicalQuerySelection) : Prop :=
  ∃ result ∈ support (canonicalChronologicalAdversaryImpl parameter root entry.table ftsSecret
      entry.input entry.context entry.fuel entry.table entry.cache),
    match result with
    | none => True
    | some result => ¬DeferredCompletable result.table result.context

set_option maxRecDepth 100000 in
theorem last_query_rejects_of_canonicalTrace_none
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (history : List CanonicalQuerySelection)
    (hcomplete : DeferredCompletable table context)
    (hrun : (none, history) ∈ support
      (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    ∃ before entry, history = before ++ [entry] ∧ DeferredCompletable entry.table entry.context ∧
      CanonicalQueryRejects parameter root ftsSecret entry := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache history with
  | pure value =>
      simp [runCanonicalQueryTrace, hcomplete] at hrun
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind, if_pos hcomplete, mem_support_bind_iff] at hrun
      obtain ⟨stepOption, hstep, hrun⟩ := hrun
      cases stepOption with
      | none =>
          simp only [pure_bind, mem_support_pure_iff, Prod.mk.injEq, true_and] at hrun
          subst history
          exact ⟨[], ⟨input, context, fuel, table, cache⟩, rfl, hcomplete, none, hstep, trivial⟩
      | some step =>
          dsimp only at hrun
          by_cases hnext : DeferredCompletable step.table step.context
          · rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff, Prod.mk.injEq] at hpure
            have htailNone : tail.1 = none := hpure.1.symm
            have htailRun : (none, tail.2) ∈ support
                (runCanonicalQueryTrace parameter root ftsSecret (next step.value.1)
                  step.context step.remaining step.table step.value.2) := by
              simpa only [← htailNone] using htail
            obtain ⟨before, entry, hlast, hentry, hreject⟩ := ih step.value.1 step.context step.remaining
              step.table step.value.2 tail.2 hnext htailRun
            refine ⟨⟨input, context, fuel, table, cache⟩ :: before, entry, ?_, hentry, hreject⟩
            rw [hpure.2, hlast]
            rfl
          · rw [runCanonicalQueryTrace_of_not_completable parameter root ftsSecret _
              step.context step.remaining step.table step.value.2 hnext] at hrun
            simp only [pure_bind, mem_support_pure_iff, Prod.mk.injEq, true_and] at hrun
            subst history
            exact ⟨[], ⟨input, context, fuel, table, cache⟩, rfl, hcomplete, some step, hstep, hnext⟩

theorem none_not_mem_resolveDeferredReveal_of_no_pending
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (hvalid : context.Valid) (hcovered : PendingCovered [] context) :
    none ∉ support (resolveDeferredReveal table position context) := by
  intro hnone
  have heq := evalDist_map_resolveDeferredReveal_then_finalize table position [] context hvalid hcovered
  have hleft : none ∈ support (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => (pure none : ProbComp (Option (LazyRevealProbe.State Coordinate)))
      | some resolved => projectDeferredState <$>
          finalizeResolvedCoordinates [] resolved.toDeferredContext table) := by
    rw [mem_support_bind_iff]
    exact ⟨none, hnone, by simp⟩
  have hright := (mem_support_iff_of_evalDist_eq heq none).mp hleft
  simp [finalizeResolvedCoordinates, projectDeferredState] at hright

theorem none_not_mem_resolved_revealPublishedPosition_of_no_pending
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) (hvalid : context.Valid) (hcovered : PendingCovered [] context) :
    none ∉ support (runResolvedFromTable context fuel table
      ((revealPublishedCoordinate (.position position)).run cache)) := by
  intro hnone
  unfold revealPublishedCoordinate at hnone
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hnone
  obtain ⟨resolvedOption, hresolved, htail⟩ := hnone
  cases resolvedOption with
  | none =>
      rw [runResolvedFromTable_revealCoordinate, mem_support_bind_iff] at hresolved
      obtain ⟨option, hoption, hpure⟩ := hresolved
      cases option with
      | none => exact none_not_mem_resolveDeferredReveal_of_no_pending table position context hvalid hcovered hoption
      | some result => simp at hpure
  | some result =>
      dsimp only at htail
      rw [StateT.run_bind, runResolvedFromTable_bind] at htail
      obtain ⟨finalContext, hpublish, _⟩ := (resolvedAdministrative_publishCoordinate (.position position)).run
        result.context result.value.2 result.remaining result.table
      rw [hpublish] at htail
      simp [runResolvedFromTable] at htail

theorem none_not_mem_resolved_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat) :
    none ∉ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
  intro hnone
  obtain ⟨reserved, hreserve, hpending, hvalues, hdeferred⟩ :=
    (resolvedAdministrative_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0).run
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } emptySplitHashCache fuel table
  unfold maskedPublishedTreeRoot at hnone
  rw [StateT.run_bind, runResolvedFromTable_bind, hreserve] at hnone
  simp only [pure_bind] at hnone
  have hvalid : reserved.Valid := by
    constructor
    · intro position output hvalue
      rw [hvalues] at hvalue
      simp [LazyRevealProbe.State.empty] at hvalue
    · intro coordinate output _hvalue
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending, LazyRevealProbe.State.empty]
  have hcovered : PendingCovered [] reserved := by
    intro entry hentry
    rw [hpending] at hentry
    simp [LazyRevealProbe.State.empty] at hentry
  exact none_not_mem_resolved_revealPublishedPosition_of_no_pending table _ reserved fuel emptySplitHashCache
    hvalid hcovered hnone

theorem deferredCompletable_of_no_pending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered [] context) : DeferredCompletable table context := by
  let completion : Coordinate → HashOutput
    | .chainStart lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩
    | .position position => (context.values position).getD 0
  refine ⟨completion, ?_, ?_, ?_, ?_⟩
  · intro coordinate output hvalue
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx => exact (hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue).symm
    | position position => simp [completion, hconsistent position output hvalue]
  · intro position output hvalue
    simp [completion, hvalue]
  · intro coordinate candidate hmember
    exact False.elim (List.not_mem_nil (hcovered _ hmember))
  · intro index
    cases index
    rfl

theorem deferredCompletable_of_mem_resolved_maskedPublishedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    DeferredCompletable result.table result.context := by
  have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hresult
  have hcovered := valid_pendingCovered_of_mem_runResolvedFromTable_of_probeFree _ _ fuel table result []
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) DeferredContext.valid_empty
    (by intro entry hentry; simp [LazyRevealProbe.State.empty] at hentry) hresult
  rw [hcore.1]
  exact deferredCompletable_of_no_pending table result.context hcore.2.1 hcore.2.2 hcovered.2

open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem relTriple_canonicalRetainedQueryTrace_prehit_last_reject
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => CanonicalQueryTraceRel parameter table left right ∧
        (left.1 = none → ∃ before entry, left.2 = before ++ [entry] ∧
          DeferredCompletable entry.table entry.context ∧
          CanonicalQueryRejects parameter right.1.1.1 ftsSecret entry)) := by
  classical
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => left ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) (fun _ hsupport => hsupport)
  have hprojection := TightEncoding.runEncodingPrehitMonitor_project accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  rw [simulateQ_romImpl_liftM] at hprojection
  have hmonitor := relTriple_of_evalDist_map_eq_general
    ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
    (TightEncoding.runEncodingPrehitMonitor accountingKey
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest) ∅ false)
    id Prod.fst (by simpa only [id_map] using congrArg evalDist hprojection.symm)
  unfold canonicalRetainedQueryTrace prehitRetainedQueryTrace
  apply relTriple_bind (relTriple_trans_exists hsupported hmonitor)
  rintro leftRoot rightRoot ⟨actualRoot, hrelation, heq⟩
  have hbase : ReachableResolvedRunRel parameter table leftRoot rightRoot.1 := heq ▸ hrelation.1
  cases leftRoot with
  | none => exact False.elim (none_not_mem_resolved_maskedPublishedTreeRoot table fuel hrelation.2)
  | some root =>
      have hcomplete := deferredCompletable_of_mem_resolved_maskedPublishedTreeRoot parameter table fuel root hrelation.2
      have hcomputed := deferredComputationsClosed_empty.of_mem_runResolved _ _ fuel table root hrelation.2
      dsimp only
      rcases hbase with hclean | hdoomed
      · have hcomplete' : DeferredCompletable table root.context := hclean.1 ▸ hcomplete
        rw [hclean.1, ← hclean.2.1]
        have htrace := relTriple_canonicalQueryTrace_prehitQueryTrace parameter root.value.1 table ftsSecret accountingKey
          (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩) root.context root.remaining root.value.2
          (⟨rightRoot.1.2, ⟨[], [], []⟩, [], none⟩, rightRoot.2)
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
        have htraceSupported := FtsProbeSimulation.relTriple_and_left_support htrace
          (fun left => left ∈ support (runCanonicalQueryTrace parameter root.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
            root.context root.remaining table root.value.2)) (fun _ hsupport => hsupport)
        have hmap := relTriple_map
          (R := fun left right => CanonicalQueryTraceRel parameter table left right ∧
            (left.1 = none → ∃ before entry, left.2 = before ++ [entry] ∧
              DeferredCompletable entry.table entry.context ∧
              CanonicalQueryRejects parameter right.1.1.1 ftsSecret entry))
          (f := fun rest : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection =>
            (rest.1.map (retainedResultWithRoot root.value.1), rest.2))
          (g := fun rest : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
            (((root.value.1, rest.1.1), rest.1.2), rest.2))
          (relTriple_post_mono htraceSupported (by
            intro left right hrel
            refine ⟨hrel.1.retainedRoot root.value.1, ?_⟩
            intro hnone
            have hleftNone : left.1 = none := Option.map_eq_none_iff.mp hnone
            exact last_query_rejects_of_canonicalTrace_none parameter root.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
              root.context root.remaining table root.value.2 left.2 hcomplete' (by
                simpa only [← hleftNone] using hrel.2)))
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap
      · exact False.elim (hdoomed.2.2.2 (hdoomed.1 ▸ hcomplete))

set_option maxRecDepth 100000 in
theorem relTriple_retainedVerifyProbe_last_reject_positive_fuel
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    RelTriple (canonicalRetainedQueryTrace adversary parameter table ftsSecret (q + 1))
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => CanonicalQueryTraceRel parameter table left right ∧
        (∀ entry ∈ left.2, 0 < entry.fuel) ∧
        (WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret
          (right.1.1, right.1.2.1.cache) →
          left.1 = none ∧ ∃ before entry, left.2 = before ++ [entry] ∧ 0 < entry.fuel ∧
            DeferredCompletable entry.table entry.context ∧
            CanonicalQueryRejects parameter right.1.1.1 ftsSecret entry)) := by
  have hbase := relTriple_canonicalRetainedQueryTrace_prehit_last_reject adversary parameter table ftsSecret (q + 1)
  have hleft := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret (q + 1)))
    (fun _ hsupport => hsupport)
  have hboth := FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation
  have hpositive := positive_fuel_of_coupled_canonicalRetainedTrace adversary q hq parameter hparameter table
    ftsSecret hfts left right hrelation.1.2 hrelation.2 hrelation.1.1.1
  refine ⟨hrelation.1.1.1, hpositive, ?_⟩
  intro hwitness
  have hnone : left.1 = none := by
    have hactual : (right.1.1, right.1.2.1.cache) ∈ support
        (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
      rw [← prehitRetainedQueryTrace_cache_projection, support_map]
      exact ⟨right, hrelation.2, rfl⟩
    rcases left with ⟨option, history⟩
    cases option with
    | none => rfl
    | some result =>
        have hterminal := hrelation.1.1.1.1
        have hreachable : ReachableResolvedRunRel parameter table (some result) (right.1.1, right.1.2.1.cache) :=
          Or.inl ⟨hterminal.1, hterminal.2.1, hterminal.2.2.1, hterminal.2.2.2.1, hterminal.2.2.2.2.1⟩
        exact False.elim (not_winningRetainedVerifyProbe_of_canonicalRetainedTrace_relation adversary parameter table
          ftsSecret (q + 1) result history right.1.1 right.1.2.1.cache hrelation.1.2 hactual hreachable hwitness)
  obtain ⟨before, entry, hlast, hcomplete, hreject⟩ := hrelation.1.1.2 hnone
  exact ⟨hnone, before, entry, hlast, hpositive entry (by rw [hlast]; simp), hcomplete, hreject⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
