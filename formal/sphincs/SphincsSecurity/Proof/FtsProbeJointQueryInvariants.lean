import SphincsSecurity.Proof.FtsProbeJointQuery

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] probingHashQuery OtsProbeSimulation.probingHashQuery

theorem invariants_maskedJointHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult HashOutput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache))) :
    AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced parameter table finalState finalCache ∧ finalState.revealed = state.revealed := by
  unfold maskedJointHashQuery at hresult
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [hdecode] at hresult
      obtain ⟨hstate, hsynced', _⟩ := invariants_nativeOrdinaryQuery parameter table input state finalState ftsFuel
        context fuel history cache ftsCache finalCache result hdecode hsynced hresult
      exact ⟨by simpa [hstate] using hclean, hsynced', congrArg AdaptiveRevealProbe.State.revealed hstate⟩
  | some probe =>
      simp only [hdecode] at hresult
      obtain ⟨output, _, houtput⟩ := mem_support_liftFtsBlock_done table state finalState ftsFuel (probingHashQuery parameter input)
        context fuel history cache ftsCache finalCache result hresult
      have hinvariants := probingHashQuery_done_false_invariants parameter table state finalState ftsFuel ftsCache finalCache
        input output hclean houtput
      exact ⟨hinvariants.1, probingHashQuery_done_false_revealedSynced parameter table state finalState ftsFuel
        ftsCache finalCache input output hclean hsynced houtput, hinvariants.2⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
