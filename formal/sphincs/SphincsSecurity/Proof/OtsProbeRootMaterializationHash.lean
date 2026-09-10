import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeComputedRootMaterialization
import SphincsSecurity.Proof.OtsProbeNativeRootHashAction
import SphincsSecurity.Proof.OtsProbeRootMaterializationExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem LayerRootsMaterialized.of_mem_revealCoordinateOutput_peek
    (parameter : PublicParameter) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (hpeek : purePeekTableInput parameter context.state coordinate ≠ none)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((revealCoordinateOutput coordinate).run cache))) :
    LayerRootsMaterialized result.context := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => exact False.elim (hpeek rfl)
  | position position =>
      rw [runResolvedFromTable_revealCoordinateOutput, mem_support_bind_iff] at hresult
      obtain ⟨resolved, hresolved, hreturn⟩ := hresult
      cases resolved with
      | none => simp at hreturn
      | some resolved =>
          simp only [mem_support_pure_iff, Option.some.injEq] at hreturn
          subst result
          exact hmat.of_resolveReveal_peek parameter table position context resolved hclosed hpeek hresolved

theorem rootMaterializationPreserving_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    RootMaterializationPreserving (resolveKnownInput parameter coordinate input) := by
  intro context fuel table cache result hmat hclosed hresult
  rw [runResolvedFromTable_resolveKnownInput_eq_public] at hresult
  unfold resolvePublicKnownInput at hresult
  cases hpeek : purePeekTableInput parameter context.state coordinate with
  | none =>
      simp only [hpeek] at hresult
      exact rootMaterializationPreserving_splitHashQuery (.ordinary input) context fuel table cache result hmat hclosed hresult
  | some knownInput =>
      simp only [hpeek] at hresult
      split_ifs at hresult with hmatch
      · rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, hrest⟩ := hresult
        cases middle with
        | none => simp at hrest
        | some middle =>
            have hmiddleMat := hmat.of_mem_revealCoordinateOutput_peek parameter coordinate context fuel table cache middle hclosed
              (by rw [hpeek]; simp) hmiddle
            have htail := (rootMaterializationPreserving_publishCoordinate coordinate).bind (fun _ =>
              (rootMaterializationPreserving_modify (fun cache => Function.update cache (.ordinary input) (some middle.value.1))).bind
                (fun _ => RootMaterializationPreserving.pure middle.value.1))
            exact htail middle.context middle.remaining middle.table middle.value.2 result hmiddleMat
              (hclosed.of_mem_runResolved _ context fuel table middle hmiddle) hrest
      · exact rootMaterializationPreserving_splitHashQuery (.ordinary input) context fuel table cache result hmat hclosed hresult

theorem rootMaterializationPreserving_probeFirstMissingInputCoordinate
    (input : HashInput) (slot : Nat) (coordinates : List Coordinate) :
    RootMaterializationPreserving (probeFirstMissingInputCoordinate input slot coordinates) := by
  induction coordinates generalizing slot with
  | nil => exact .pure _
  | cons coordinate remaining ih =>
      unfold probeFirstMissingInputCoordinate
      apply (rootMaterializationPreserving_peekCoordinate coordinate).bind
      intro output
      cases output with
      | none => exact rootMaterializationPreserving_probe _
      | some output => exact ih (slot + 1)

theorem rootMaterializationPreserving_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootMaterializationPreserving (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (rootMaterializationPreserving_peekCoordinate candidate.coordinate).bind
  intro output
  cases output with
  | none => exact rootMaterializationPreserving_probe candidate
  | some output => exact rootMaterializationPreserving_probeFirstMissingInputCoordinate input 0 _

theorem rootMaterializationPreserving_probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    RootMaterializationPreserving (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | none =>
          exact (rootMaterializationPreserving_probe candidate).bind
            (fun _ => rootMaterializationPreserving_resolveKnownInput parameter candidate.outputCoordinate input)
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (rootMaterializationPreserving_prepareLeafInputProbe input candidate lay tree leafIdx).bind
                (fun _ => rootMaterializationPreserving_resolveKnownInput parameter candidate.outputCoordinate input)
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (rootMaterializationPreserving_probe candidate).bind
                (fun _ => rootMaterializationPreserving_resolveKnownInput parameter candidate.outputCoordinate input)
  | none =>
      cases decodePosition? parameter input with
      | none => exact rootMaterializationPreserving_splitHashQuery _
      | some position =>
          cases position with
          | chain | leaf => exact rootMaterializationPreserving_resolveKnownInput parameter _ input
          | node lay tree level nodeIdx =>
              exact (rootMaterializationPreserving_probeFirstMissingInputCoordinate input 0 _).bind
                (fun _ => rootMaterializationPreserving_resolveKnownInput parameter _ input)
          | ftsLeaf | ftsNode | ftsRoots => exact rootMaterializationPreserving_splitHashQuery _

end SphincsSecurity.Concrete.OtsProbeSimulation
