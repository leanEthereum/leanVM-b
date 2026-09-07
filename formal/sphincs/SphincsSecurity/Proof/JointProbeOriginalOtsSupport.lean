import SphincsSecurity.Proof.OtsProbeOuterCapSupport
import SphincsSecurity.Proof.JointProbeOriginalRetainedExecution
import SphincsSecurity.Proof.JointProbeResolvedGameCoupling

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem mem_support_nativeRetained_of_outerCap_some
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (hresult : some (⟨result.context, result.remaining, (some result.value.1, result.value.2), result.table⟩ :
        ResolvedRunResult (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache)) ∈ support
      (OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((outerCappedNativeRetained adversary parameter ftsSecret q).run OtsProbeSimulation.emptySplitHashCache))) :
    some result ∈ support (OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
      ((OtsProbeSimulation.maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
        OtsProbeSimulation.emptySplitHashCache)) := by
  rw [outerCappedNativeRetained, StateT.run_bind, OtsProbeSimulation.runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨root, hroot, hrest⟩ := hresult
  rw [OtsProbeSimulation.maskedChronologicalRetainedGame_eq_root_rest,
    OtsProbeSimulation.runResolvedFromTable_bind, mem_support_bind_iff]
  refine ⟨root, hroot, ?_⟩
  cases root with
  | none => simp at hrest
  | some root =>
      dsimp only at hrest ⊢
      rw [← OtsProbeSimulation.capOuterHashQueries_map] at hrest
      have h := OtsProbeSimulation.mem_support_runResolved_of_outerCap_some
        (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root.value.1 ftsSecret) _ q
        root.context root.remaining root.table root.value.2 result hrest
      rw [show retainedGameRestComputation adversary ⟨root.value.1, parameter⟩ =
        OtsProbeSimulation.retainedGameRestComputation adversary ⟨root.value.1, parameter⟩ from rfl] at h
      simpa only [simulateQ_map, StateT.run_map, bind_pure_comp] using h

namespace JointOriginal

theorem run_retained_native_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame)
    (value : RetainedGameResult) (hvalue : pair.2.1.1 = some value) :
    some (⟨finalFrame.context, finalFrame.fuel,
      (value, OtsProbeSimulation.replaceOrdinaryCache finalFrame.cache.1 (mergedCache parameter ftsTable finalFrame.cache.2)), otsTable⟩ :
        ResolvedRunResult (RetainedGameResult × OtsProbeSimulation.SplitHashCache)) ∈ support
      (OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((OtsProbeSimulation.maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter
          (fun index tree leaf => ftsTable (index, tree, leaf))).run OtsProbeSimulation.emptySplitHashCache)) := by
  have hs := run_retained_shared_support exception adversary parameter root otsTable ftsTable q fuel frame cache hit
    hroot hvalid pair hpair finalFrame hframe
  obtain ⟨native, hn, hrel⟩ := OtsProbeSimulation.exists_right_of_relTriple_of_mem_support
    (relTriple_jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel) hs
  rcases hrel with hhit | heq
  · simp [AdaptiveRevealProbe.DetailedResult.hit] at hhit
  · apply mem_support_nativeRetained_of_outerCap_some adversary parameter _ q fuel otsTable
    rw [← heq] at hn
    simpa only [projectJointResolvedCache, cleanJointResolved, Option.map_some, finalCache, prepareNativeCache,
      OtsProbeSimulation.replaceOrdinaryCache_replace, hvalue] using hn

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
