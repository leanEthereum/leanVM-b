import SphincsSecurity.Proof.FtsProbeStableExecutionCache
import SphincsSecurity.Proof.FtsProbeTerminal
import SphincsSecurity.Proof.FtsProbeJointQuerySupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probingHashQuery_eq_ordinary_of_stable
    (parameter : PublicParameter) (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    probingHashQuery parameter input = ordinaryHashImpl input := by
  unfold probingHashQuery
  rw [hstable.1]
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | chain | leaf | node => exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots => rfl

theorem historyPrefix_stableQuery_output_cached
    (parameter : PublicParameter) (input : HashInput) (hstable : StableOrdinaryInput parameter input)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (entry : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hresult : some entry ∈ support (runResolvedHistoryPrefix
      (eraseProbeQueries ((probingHashQuery parameter input).run cache)) context fuel history)) :
    entry.value.2 (.ordinary input) = some entry.value.1 := by
  rw [probingHashQuery_eq_ordinary_of_stable parameter input hstable] at hresult
  change some entry ∈ support (runResolvedHistoryPrefix
    (eraseProbeQueries ((splitHashQuery (.ordinary input)).run cache)) context fuel history) at hresult
  rw [eraseProbeQueries_eq_of_probeFree _ (splitHashQuery_probeFree (.ordinary input) cache)] at hresult
  have hraw := mem_support_of_historyPrefix _ context fuel history entry hresult
  change entry.value ∈ support ((splitHashQuery (.ordinary input)).run cache) at hraw
  rw [splitHashQuery_run_eq] at hraw
  cases hlookup : cache (.ordinary input) with
  | some output =>
      simp only [hlookup, mem_support_pure_iff] at hraw
      rw [hraw]
      exact hlookup
  | none =>
      simp only [hlookup, mem_support_bind_iff, mem_support_pure_iff] at hraw
      obtain ⟨output, _, hvalue⟩ := hraw
      rw [hvalue]
      simp

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem maskedJointHashQuery_stable_output_cached
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (HashOutput × OtsProbeSimulation.SplitHashCache))
    (hstable : OtsProbeSimulation.StableOrdinaryInput parameter input)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache))) :
    mergedCache parameter table finalCache input = some entry.value.1 := by
  have hrel : NativeStepRelAt parameter table state (remaining + 1) (maskedJointHashQuery parameter input)
      (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache ftsCache :=
    relTriple_maskedJointHashQuery parameter table input state remaining context fuel history cache ftsCache hclean hsynced
  exact OtsProbeSimulation.historyPrefix_stableQuery_output_cached parameter input hstable context fuel history _ _
    (hrel.mem_support_native hresult)

theorem maskedJointHashQuery_done_false_hit_revealed
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput) (probe : FtsSecretProbe)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (HashOutput × OtsProbeSimulation.SplitHashCache))
    (hdecode : decodeProbe? parameter input = some probe)
    (hhit : probe.Hits (fun index tree leaf => table (index, tree, leaf)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache))) :
    ∃ value, state.revealed (probe.index, probe.tree, probe.leafIdx) = some value := by
  simp only [maskedJointHashQuery, hdecode] at hresult
  obtain ⟨output, _, hquery⟩ := mem_support_liftFtsBlock_done table state finalState ftsFuel
    (probingHashQuery parameter input) context fuel history cache ftsCache finalCache (some entry) hresult
  exact probingHashQuery_done_false_hit_revealed parameter table state finalState ftsFuel ftsCache finalCache input output probe hdecode hhit hquery

end SphincsSecurity.Concrete.FtsProbeSimulation
