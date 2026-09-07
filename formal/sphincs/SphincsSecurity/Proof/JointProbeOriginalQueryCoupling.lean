import SphincsSecurity.Proof.JointProbeOriginalMonitorCoupling

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem jointResolvedCoupledAt_outerQuery
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hhash : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceOuterQuery parameter root input)
      (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root (fun index tree leaf => table (index, tree, leaf)) input)
      context fuel otsTable cache := by
  cases input with
  | inl world =>
      cases world with
      | inl n =>
          exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel (OtsProbeSimulation.splitUniformImpl n)
            (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n)) context fuel otsTable cache hclean
      | inr input =>
          have hpositive := hhash trivial
          obtain ⟨remaining, rfl⟩ : ∃ remaining, ftsFuel = remaining + 1 := ⟨ftsFuel - 1, by omega⟩
          exact jointResolvedCoupledAt_hashQuery parameter table input state remaining context fuel otsTable cache hclean hsynced
  | inr message => exact jointResolvedCoupledAt_sign parameter root table message state ftsFuel context fuel otsTable cache hclean hsynced

theorem revealedSynced_jointSourceOuterQuery
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState entry.value.2.2 := by
  cases input with
  | inl world =>
      cases world with
      | inl n =>
          exact (invariants_jointSourceNativeBlock parameter table state finalState ftsFuel (OtsProbeSimulation.splitUniformImpl n)
            (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
            context fuel otsTable cache entry hsynced hresult).2.1
      | inr input =>
          exact revealedSynced_jointSourceHashQuery parameter table input state finalState ftsFuel
            context fuel otsTable cache entry hclean hsynced hresult
  | inr message =>
      exact revealedSynced_jointSourceSign parameter root table message state finalState ftsFuel
        context fuel otsTable cache entry hclean hsynced hresult

theorem relTriple_jointResolvedQuery_originalMonitor
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (cache : JointSourceCache)
    (actualCache : QueryCache HashSpec) (hit : Bool)
    (hhash : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state ftsTable = false) (hsynced : RevealedSynced parameter ftsTable state cache.2)
    (hinvariant : OtsProbeSimulation.ResolvedContextInvariant parameter otsTable context
      (mergedCache parameter ftsTable cache.2) actualCache)
    (hvisible : OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable context actualCache)
    (hpublished : OtsProbeSimulation.PublishedValues context.state) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
      fun index tree leaf => ftsTable (index, tree, leaf)⟩
    let joint := AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run cache) context fuel otsTable)
    let original := runExceptionMonitor exception (expandedAdversaryImpl secretKey input) actualCache hit
    RelTriple joint original (fun left right =>
      JointOriginalRunRel parameter otsTable ftsTable left right.1 ∧ left ∈ support joint ∧ right ∈ support original) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
    fun index tree leaf => ftsTable (index, tree, leaf)⟩
  have hjoint := jointResolvedCoupledAt_outerQuery parameter root ftsTable input state ftsFuel context fuel otsTable cache hhash hclean hsynced
  have hnative := OtsProbeSimulation.reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter root otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) input context fuel
    (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter ftsTable cache.2)) actualCache hinvariant hvisible hpublished
  rw [unloggedMappedAdversaryImpl_eq_simulateQ_expanded] at hnative
  have hprojection := runExceptionMonitor_project exception (expandedAdversaryImpl secretKey input) actualCache hit
  have hmonitor := relTriple_of_evalDist_map_eq_general
    ((simulateQ romImpl (expandedAdversaryImpl secretKey input)).run actualCache)
    (runExceptionMonitor exception (expandedAdversaryImpl secretKey input) actualCache hit)
    id Prod.fst (by simpa only [id_map] using congrArg evalDist hprojection.symm)
  have hbase := relTriple_trans_exists hjoint (relTriple_trans_exists hnative hmonitor)
  have hrel := relTriple_post_mono hbase (R' := fun left right => JointOriginalRunRel parameter otsTable ftsTable left right.1) (by
    rintro left right ⟨native, hleft, actual, hright, heq⟩
    rcases hleft with hhit | hleft
    · exact Or.inl hhit
    · exact Or.inr (hleft ▸ heq ▸ hright))
  have hsupported := relTriple_and_right_support (relTriple_and_left_support hrel _ (fun _ h => h))
  exact relTriple_post_mono hsupported (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩)

theorem jointOriginalQuery_continuation_invariants
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (cache : JointSourceCache)
    (entry : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × JointSourceCache))
    (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hclean : AdaptiveRevealProbe.tableHits state ftsTable = false) (hsynced : RevealedSynced parameter ftsTable state cache.2)
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run cache) context fuel otsTable)))
    (hrel : JointOriginalRunRel parameter otsTable ftsTable (.done false finalState (some entry)) actual)
    (hcomplete : OtsProbeSimulation.DeferredCompletable otsTable entry.context) :
    entry.table = otsTable ∧ entry.value.1 = actual.1 ∧
      OtsProbeSimulation.ResolvedContextInvariant parameter otsTable entry.context (mergedCache parameter ftsTable entry.value.2.2) actual.2 ∧
      OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable entry.context actual.2 ∧
      OtsProbeSimulation.PublishedValues entry.context.state ∧
      AdaptiveRevealProbe.tableHits finalState ftsTable = false ∧ RevealedSynced parameter ftsTable finalState entry.value.2.2 := by
  let projected : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × OtsProbeSimulation.SplitHashCache) :=
    { entry with value := (entry.value.1,
      OtsProbeSimulation.replaceOrdinaryCache entry.value.2.1 (mergedCache parameter ftsTable entry.value.2.2)) }
  have hnext := hrel.of_completable (entry := projected) rfl (by simp [projectJointResolvedCache, cleanJointResolved, projected]) hcomplete
  exact ⟨hnext.1, hnext.2.1, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2,
    AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done ftsTable state finalState ftsFuel _ false _ hresult,
    revealedSynced_jointSourceOuterQuery parameter root ftsTable input state finalState ftsFuel context fuel otsTable cache entry hclean hsynced hresult⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
