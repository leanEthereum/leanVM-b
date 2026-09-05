import SphincsSecurity.Proof.OtsProbeCanonicalTraceSupport
import SphincsSecurity.Proof.OtsProbeQueryTraceReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem runPrehitQueryTrace_cache_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => (result.1.1, result.1.2.1.cache)) <$> runPrehitQueryTrace accountingKey secretKey computation state =
      (simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run state.1.cache := by
  rw [← encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey computation state,
    ← runPrehitQueryTrace_projection, Functor.map_map]

noncomputable def prehitRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) := do
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let root ← TightEncoding.runEncodingPrehitMonitor accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  let rest ← runPrehitQueryTrace accountingKey ⟨parameter, root.1.1, otsSecret, ftsSecret⟩
    (retainedGameRestComputation adversary ⟨root.1.1, parameter⟩)
    (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2)
  pure (((root.1.1, rest.1.1), rest.1.2), rest.2)

theorem prehitRetainedQueryTrace_cache_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.1, result.1.2.1.cache)) <$> prehitRetainedQueryTrace adversary parameter table ftsSecret =
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table) := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := TightEncoding.runEncodingPrehitMonitor_project accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  rw [simulateQ_romImpl_liftM] at hroot
  unfold prehitRetainedQueryTrace actualRetainedGameAfterTable
  change _ = ((simulateQ (randomOracle : QueryImpl HashSpec _)
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅ >>= fun root => do
      let result ← (simulateQ (unloggedMappedAdversaryImpl ⟨parameter, root.1, otsSecret, ftsSecret⟩)
        (retainedGameRestComputation adversary ⟨root.1, parameter⟩)).run root.2
      pure ((root.1, result.1), result.2))
  rw [← hroot, bind_map_left, map_bind]
  apply bind_congr
  intro root
  simp only [map_bind, map_pure]
  have hrest := runPrehitQueryTrace_cache_projection accountingKey ⟨parameter, root.1.1, otsSecret, ftsSecret⟩
    (retainedGameRestComputation adversary ⟨root.1.1, parameter⟩) (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2)
  rw [← hrest, bind_map_left]

theorem CanonicalQueryTraceRel.retainedRoot
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput} (root : Digest)
    {left : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel parameter table left right) :
    CanonicalQueryTraceRel parameter table (left.1.map (retainedResultWithRoot root), left.2)
      (((root, right.1.1), right.1.2), right.2) := by
  refine ⟨?_, hrelation.2⟩
  rcases left with ⟨result, history⟩
  cases result with
  | none => trivial
  | some result =>
      exact ⟨hrelation.1.1, congrArg (root, ·) hrelation.1.2.1, hrelation.1.2.2⟩

set_option maxRecDepth 100000 in
theorem relTriple_canonicalRetainedQueryTrace_prehit
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret) (CanonicalQueryTraceRel parameter table) := by
  classical
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact deferredComputationsClosed_empty.of_mem_runResolved _ _ fuel table result hleft)
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
  | none => exact relTriple_empty_canonicalTrace_any parameter table _
  | some result =>
      have hcomputed := hrelation.2 result rfl
      dsimp only
      rcases hbase with hclean | hdoomed
      · rw [hclean.1, ← hclean.2.1]
        have htrace := relTriple_canonicalQueryTrace_prehitQueryTrace parameter result.value.1 table ftsSecret accountingKey
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining result.value.2
          (⟨rightRoot.1.2, ⟨[], [], []⟩, [], none⟩, rightRoot.2)
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
        have hmap := relTriple_map
          (f := fun rest : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection =>
            (rest.1.map (retainedResultWithRoot result.value.1), rest.2))
          (g := fun rest : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
            (((result.value.1, rest.1.1), rest.1.2), rest.2))
          (relTriple_post_mono htrace fun left right hrel => hrel.retainedRoot result.value.1)
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap
      · rw [runCanonicalQueryTrace_of_not_completable parameter result.value.1 ftsSecret _
          result.context result.remaining result.table result.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)]
        simp only [pure_bind, Option.map_none]
        exact relTriple_empty_canonicalTrace_any parameter table _

theorem relTriple_canonicalRetainedQueryTrace_prehit_witness
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => CanonicalQueryTraceRel parameter table left right ∧
        (WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret
          (right.1.1, right.1.2.1.cache) → left.1 = none)) := by
  have hbase := relTriple_canonicalRetainedQueryTrace_prehit adversary parameter table ftsSecret fuel
  have hleft := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (fun _ hsupport => hsupport)
  have hboth := FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation
  refine ⟨hrelation.1.1, ?_⟩
  intro hwitness
  have hactual : (right.1.1, right.1.2.1.cache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
    rw [← prehitRetainedQueryTrace_cache_projection, support_map]
    exact ⟨right, hrelation.2, rfl⟩
  rcases left with ⟨result, history⟩
  cases result with
  | none => rfl
  | some result =>
      have hterminal := hrelation.1.1.1
      have hreachable : ReachableResolvedRunRel parameter table (some result) (right.1.1, right.1.2.1.cache) :=
        Or.inl ⟨hterminal.1, hterminal.2.1, hterminal.2.2.1, hterminal.2.2.2.1, hterminal.2.2.2.2.1⟩
      exact False.elim (not_winningRetainedVerifyProbe_of_canonicalRetainedTrace_relation adversary parameter table ftsSecret fuel
        result history right.1.1 right.1.2.1.cache hrelation.1.2 hactual hreachable hwitness)

end SphincsSecurity.Concrete.OtsProbeSimulation
