import SphincsSecurity.Proof.OtsProbeEarlyParentRetained

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeRetainedParentTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) := do
  let root ← runResolvedFromTable (ensuredInitialContext ∅) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match root with
  | none => pure (none, [])
  | some root =>
      let rest ← runNativeQueryTrace parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining root.table root.value.2
      pure (rest.1.map (retainedResultWithRoot root.value.1), rest.2)

theorem FullCanonicalQueryTraceRel.retainedRoot
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput} (root : Digest)
    {left : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (h : FullCanonicalQueryTraceRel parameter table left right) :
    FullCanonicalQueryTraceRel parameter table (left.1.map (retainedResultWithRoot root), left.2)
      (((root, right.1.1), right.1.2), right.2) :=
  ⟨h.1.retainedRoot root, fun hsome => h.2 (fun hnone => hsome (by simp [hnone]))⟩

def NativeParentTraceRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  FullCanonicalQueryTraceRel parameter table left right ∧
    (EarlyOtsParentAtQuery parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret right → left.1 = none)

private theorem relTriple_empty_nativeParentTrace
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (right : ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)) :
    RelTriple (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
      right (NativeParentTraceRel parameter table ftsSecret) := by
  have h := relTriple_empty_fullCanonicalTrace_any parameter table right
  have hs := FtsProbeSimulation.relTriple_and_left_support h (fun left => left.1 = none) (by
    intro left hleft
    exact congrArg Prod.fst (show left = (none, []) by simpa using hleft))
  exact relTriple_post_mono hs (fun _ _ hrel => ⟨hrel.1, fun _ => hrel.2⟩)

theorem relTriple_nativeQueryTrace_full_earlyParent
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)
      (runPrehitQueryTrace accountingKey secretKey computation state) (NativeParentTraceRel parameter table ftsSecret) := by
  dsimp only
  have h := relTriple_nativeQueryTrace_full_prehitQueryTrace parameter root table ftsSecret accountingKey
    computation context fuel cache state hinvariant hvisible hpublished hcomputed
  have hs := FtsProbeSimulation.relTriple_and_left_support h
    (fun result => result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (by intro _ hresult; exact hresult)
  apply relTriple_post_mono hs
  rintro ⟨native, history⟩ actual hrel
  refine ⟨hrel.1, ?_⟩
  intro hearly
  cases native with
  | none => rfl
  | some result =>
      exact False.elim (not_earlyOtsParentAtQuery_of_full_native_trace parameter root ftsSecret computation
        context fuel table cache result history actual hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hrel.2 hrel.1 hearly)

theorem relTriple_nativeRetainedParentTrace_prehit
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple (nativeRetainedParentTrace adversary parameter table ftsSecret fuel)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (NativeParentTraceRel parameter table ftsSecret) := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext ∅)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant ∅ parameter table)
    (ensuredInitialContext_visible ∅ parameter table) (ensuredInitialContext_published ∅)
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact (ensuredInitialContext_computed ∅).of_mem_runResolved _ _ fuel table result hleft)
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
  unfold nativeRetainedParentTrace prehitRetainedQueryTrace
  apply relTriple_bind (relTriple_trans_exists hsupported hmonitor)
  rintro leftRoot rightRoot ⟨actualRoot, hrelation, heq⟩
  have hbase : ReachableResolvedRunRel parameter table leftRoot rightRoot.1 := heq ▸ hrelation.1
  cases leftRoot with
  | none => exact relTriple_empty_nativeParentTrace parameter table ftsSecret _
  | some result =>
      have hcomputed := hrelation.2 result rfl
      dsimp only
      rcases hbase with hclean | hdoomed
      · rw [hclean.1, ← hclean.2.1]
        have htrace := relTriple_nativeQueryTrace_full_earlyParent parameter result.value.1 table ftsSecret accountingKey
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining result.value.2
          (⟨rightRoot.1.2, ⟨[], [], []⟩, [], none⟩, rightRoot.2)
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
        have hmap := relTriple_map
          (f := fun left : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection =>
            (left.1.map (retainedResultWithRoot result.value.1), left.2))
          (g := fun rest : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
            (((result.value.1, rest.1.1), rest.1.2), rest.2))
          (R := NativeParentTraceRel parameter table ftsSecret)
          (relTriple_post_mono htrace (fun left right hrel =>
            ⟨hrel.1.retainedRoot result.value.1, fun hearly => by
              rw [hrel.2 hearly]; rfl⟩))
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap
      · rw [runNativeQueryTrace_of_not_completable parameter result.value.1 ftsSecret _
          result.context result.remaining result.table result.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)]
        simp only [pure_bind, Option.map_none]
        exact relTriple_empty_nativeParentTrace parameter table ftsSecret _


end SphincsSecurity.Concrete.OtsProbeSimulation
