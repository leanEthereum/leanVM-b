import SphincsSecurity.Proof.JointProbeResolvedHashQuery

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runJointResolved_hashQuery_decode_some
    (parameter : PublicParameter) (input : HashInput) (probe : FtsSecretProbe)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hdecode : decodeProbe? parameter input = some probe) :
    runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable =
      (AdaptiveRevealProbe.probeQuery (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
        runJointResolved ((jointSourceFtsBlock (splitHashQuery (.ordinary input))).run cache) context fuel otsTable) := by
  unfold jointSourceHashQuery
  simp only [hdecode]
  dsimp only [jointSourceFtsBlock, StateT.run]
  have hquery := probingHashQuery_run_eq parameter input cache.2
  dsimp only [StateT.run] at hquery
  rw [runJointResolved_map, runJointResolved_fts, hquery, hdecode]
  rw [runJointResolved_map, runJointResolved_fts]
  simp only [Functor.map_map, map_bind]

theorem runDetailed_jointResolved_hashQuery_bind
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (next : Option (ResolvedRunResult (HashOutput × JointSourceCache)) → OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    AdaptiveRevealProbe.runDetailed table state (remaining + 1)
      (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable >>= next) =
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable) >>= fun result =>
          match result with
          | .stopped hit => pure (.stopped hit)
          | .done _ finalState value => AdaptiveRevealProbe.runDetailed table finalState (jointHashRemaining parameter input remaining) (next value) := by
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [jointSourceHashQuery, jointHashRemaining, hdecode]
      convert (AdaptiveRevealProbe.runDetailed_bind_probeFree table state (remaining + 1) _ next
        (runJointResolved_nativeBlock_probeFree (OtsProbeSimulation.probingHashQuery parameter input) context fuel otsTable cache)) using 1
      apply bind_congr
      intro result
      cases result <;> rfl
  | some probe =>
      rw [runJointResolved_hashQuery_decode_some parameter input probe context fuel otsTable cache hdecode]
      simp only [jointHashRemaining, hdecode]
      convert (AdaptiveRevealProbe.runDetailed_bind_probePrefix table state remaining (probe.index, probe.tree, probe.leafIdx) probe.candidate
        _ next (runJointResolved_ftsBlock_probeFree _ (splitHashQuery_probeFree (.ordinary input)) context fuel otsTable cache)) using 1
      apply bind_congr
      intro result
      cases result <;> rfl

theorem jointResolvedCoupledAt_hashQuery_bind
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (next : HashOutput → JointSource α)
    (nativeNext : HashOutput → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hnext : ∀ finalState entry,
      .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable)) →
      JointResolvedCoupledAt parameter table finalState (jointHashRemaining parameter input remaining)
        (next entry.value.1) (nativeNext entry.value.1) entry.context entry.remaining entry.table entry.value.2) :
    JointResolvedCoupledAt parameter table state (remaining + 1) (jointSourceHashQuery parameter input >>= next)
      (OtsProbeSimulation.probingHashQuery parameter input >>= nativeNext) context fuel otsTable cache := by
  apply jointResolvedCoupledAt_bind_of_resume parameter table state (remaining + 1) (jointHashRemaining parameter input remaining)
    _ next _ nativeNext context fuel otsTable cache ?_
    (jointResolvedCoupledAt_hashQuery parameter table input state remaining context fuel otsTable cache hclean hsynced) hnext
  rw [StateT.run_bind, runJointResolved_bind, runDetailed_jointResolved_hashQuery_bind]
  apply bind_congr
  intro result
  cases result with
  | stopped hit => rfl
  | done hit finalState entry => cases entry <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
