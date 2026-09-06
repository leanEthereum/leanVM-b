import SphincsSecurity.Proof.FtsProbeNativeOrdinaryQuery
import SphincsSecurity.Proof.FtsProbeFtsQueryStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def maskedJointHashQuery (parameter : PublicParameter) (input : HashInput) : NativeFtsStep HashOutput :=
  match decodeProbe? parameter input with
  | none => liftNativeBlock (OtsProbeSimulation.probingHashQuery parameter input)
  | some _ => liftFtsBlock (probingHashQuery parameter input)

theorem NativeStepCoupledAt.relTriple
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {ftsFuel : Nat}
    {masked : NativeFtsStep α}
    {native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α}
    {context : OtsProbeSimulation.DeferredContext} {fuel : Nat} {history : List OtsProbeSimulation.Probe}
    {cache : OtsProbeSimulation.SplitHashCache} {ftsCache : SplitHashCache}
    (h : NativeStepCoupledAt parameter table state ftsFuel masked native context fuel history cache ftsCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          (native.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history)
      (NativeStepCleanRel parameter table) := by
  rw [← h]
  have hself := relTriple_post_mono (relTriple_refl
    (AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache)))
    (R' := fun left right => NativeStepCleanRel parameter table left (projectNativeStepCache parameter table right))
    (fun left right heq => by subst right; exact Or.inr rfl)
  simpa only [id_map] using relTriple_map (f := id) (g := projectNativeStepCache parameter table) hself

theorem relTriple_maskedJointHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.probingHashQuery parameter input).run
            (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history)
      (NativeStepCleanRel parameter table) := by
  unfold maskedJointHashQuery
  cases hdecode : decodeProbe? parameter input with
  | none =>
      exact (nativeStepCoupledAt_ordinaryQuery parameter table input state (remaining + 1) context fuel history cache ftsCache hclean hdecode).relTriple
  | some probe => exact relTriple_nativeStep_ftsQuery parameter table input probe state remaining context fuel history cache ftsCache hdecode hclean hsynced

theorem maskedJointHashQuery_run_isProbeBound
    (parameter : PublicParameter) (input : HashInput)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold maskedJointHashQuery
  cases hdecode : decodeProbe? parameter input with
  | none => exact (liftNativeBlock_probeFree _ context fuel history cache ftsCache).mono (by omega)
  | some probe =>
      simp only
      rw [liftFtsBlock, StateT.run_map, isQueryBoundP_map_iff]
      exact probingHashQuery_run_isProbeBound parameter input ftsCache

end SphincsSecurity.Concrete.FtsProbeSimulation
