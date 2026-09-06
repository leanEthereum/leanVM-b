import SphincsSecurity.Proof.JointProbeResolvedSignerSynced

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem jointResolvedCoupledAt_ftsHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput) (probe : FtsSecretProbe)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hdecode : decodeProbe? parameter input = some probe)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state (remaining + 1) (jointSourceFtsBlock (probingHashQuery parameter input))
      (OtsProbeSimulation.probingHashQuery parameter input) context fuel otsTable cache := by
  unfold JointResolvedCoupledAt
  rw [runDetailed_jointSourceFtsBlock, nativeProbingHashQuery_eq_ordinary_of_decodeProbe parameter input probe hdecode,
    OtsProbeSimulation.runResolved_ordinaryHash, OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache]
  have h := relTriple_probingHashQuery_step parameter table state remaining cache.2 input hclean hsynced
  have hrel := relTriple_post_mono h (R' := fun left right =>
    JointResolvedCleanRel parameter table (wrapResolvedFtsBlock context fuel otsTable cache.1 left)
      (OtsProbeSimulation.ordinaryResolvedResult context fuel otsTable
        (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter table cache.2)) right)) (by
      intro left right hstep
      rcases hstep with hhit | hstep
      · left
        cases left <;> exact hhit
      · right
        cases left with
        | stopped hit => exact False.elim hstep
        | done hit finalState value =>
            obtain ⟨rfl, rfl, _, _⟩ := hstep
            simp [projectJointResolvedCache, cleanJointResolved, wrapResolvedFtsBlock, AdaptiveRevealProbe.DetailedResult.mapValue,
              OtsProbeSimulation.ordinaryResolvedResult, OtsProbeSimulation.replaceOrdinaryCache_replace])
  exact relTriple_map (f := wrapResolvedFtsBlock context fuel otsTable cache.1)
    (g := OtsProbeSimulation.ordinaryResolvedResult context fuel otsTable
      (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter table cache.2))) hrel

theorem jointResolvedCoupledAt_hashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state (remaining + 1) (jointSourceHashQuery parameter input)
      (OtsProbeSimulation.probingHashQuery parameter input) context fuel otsTable cache := by
  unfold jointSourceHashQuery
  cases hdecode : decodeProbe? parameter input with
  | none =>
      exact jointResolvedCoupledAt_nativeBlock parameter table state (remaining + 1) _
        (fun cache => cacheMapCommutes_native_probingHashQuery parameter table cache input
          (isOrdinaryInput_of_decode_none parameter table input hdecode)) context fuel otsTable cache hclean
  | some probe => exact jointResolvedCoupledAt_ftsHashQuery parameter table input probe state remaining context fuel otsTable cache hdecode hclean hsynced

theorem revealedSynced_jointSourceHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (HashOutput × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some result) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceHashQuery at hresult
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [hdecode] at hresult
      exact (invariants_jointSourceNativeBlock parameter table state finalState ftsFuel _
        (fun cache => cacheMapCommutes_native_probingHashQuery parameter table cache input
          (isOrdinaryInput_of_decode_none parameter table input hdecode)) context fuel otsTable cache result hsynced hresult).2.1
  | some probe =>
      simp only [hdecode] at hresult
      obtain ⟨value, finalCache, rfl, hvalue⟩ := mem_support_jointSourceFtsBlock_done table state finalState ftsFuel _
        context fuel otsTable cache result hresult
      exact probingHashQuery_done_false_revealedSynced parameter table state finalState ftsFuel cache.2 finalCache
        input value hclean hsynced hvalue

end SphincsSecurity.Concrete.FtsProbeSimulation
