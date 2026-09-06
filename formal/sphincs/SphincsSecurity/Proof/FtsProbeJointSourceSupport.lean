import SphincsSecurity.Proof.FtsProbeStableExecutionCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem support_eraseProbeQueries_subset
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    support (eraseProbeQueries computation) ⊆ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact Set.Subset.rfl
  | query_bind input next ih =>
      intro value hvalue
      rw [mem_support_bind_iff]
      rw [eraseProbeQueries, construct_query_bind] at hvalue
      cases input
      case probe coordinate digest =>
        exact ⟨(), mem_support_query (spec := LazyRevealProbe.World Coordinate) (.probe coordinate digest) (), ih () hvalue⟩
      all_goals
        rw [mem_support_bind_iff] at hvalue
        obtain ⟨reply, hreply, hnext⟩ := hvalue
        exact ⟨reply, hreply, ih reply hnext⟩

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem mem_support_source_of_maskedJointComputation
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root computation context fuel history cache).run ftsCache))) :
    entry.value.1 ∈ support computation := by
  have hnative := (nativeStepRelAt_maskedJointComputation parameter root table computation state ftsFuel
    context fuel history cache ftsCache hbound hclean hsynced).mem_support_native hresult
  have hraw := OtsProbeSimulation.support_eraseProbeQueries_subset _
    (OtsProbeSimulation.mem_support_of_historyPrefix _ context fuel history _ hnative)
  apply support_simulateQ_run'_subset (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root
    (fun index tree leaf => table (index, tree, leaf))) computation
    (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))
  rw [StateT.run'_eq, support_map]
  exact ⟨_, hraw, rfl⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
