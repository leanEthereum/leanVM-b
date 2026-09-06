import SphincsSecurity.Proof.JointProbeEncodingCacheSigner
import SphincsSecurity.Proof.OtsProbeLayerEncodingFailure
import SphincsSecurity.Proof.EncodingSigningFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem traverseOption_none_of_mem_failed_jointPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourcePublication parameter randomness index leaves ftsPath layers).run cache) context fuel otsTable)))
    (hfailed : entry.value.1 = none) : traverseOption layers = none := by
  rw [jointSourcePublication_eq_unmerged] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceUnmergedNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  dsimp only at hrest
  cases hbody : native.value.1 with
  | none =>
      cases hparts : traverseOption layers with
      | none => rfl
      | some parts =>
          simp only [OtsProbeSimulation.publishSignatureBody, hparts, StateT.run_bind,
            OtsProbeSimulation.runResolvedFromTable_bind, mem_support_bind_iff] at hnative
          obtain ⟨publishedOption, hpublished, hreturn⟩ := hnative
          cases publishedOption with
          | none => simp at hreturn
          | some published =>
              simp [OtsProbeSimulation.runResolvedFromTable] at hreturn
              subst native
              simp at hbody
  | some body =>
      simp only [hbody] at hrest
      rw [StateT.run_map, runJointResolved_map, AdaptiveRevealProbe.runRaw_mapValue, support_map] at hrest
      obtain ⟨result, _, heq⟩ := hrest
      cases result with
      | stopped hit => simp [AdaptiveRevealProbe.RawResult.mapValue] at heq
      | done resultState resultFuel result =>
          cases result with
          | none => simp [AdaptiveRevealProbe.RawResult.mapValue] at heq
          | some result =>
              simp only [AdaptiveRevealProbe.RawResult.mapValue, Option.map_some,
                AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at heq
              obtain ⟨_, _, heq⟩ := heq
              subst entry
              simp at hfailed

theorem failed_layer_of_mem_failed_jointPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourcePublication parameter randomness index leaves ftsPath layers).run cache) context fuel otsTable)))
    (hfailed : entry.value.1 = none) : ∃ lay, layers lay = none :=
  exists_none_of_traverseOption_none layers
    (traverseOption_none_of_mem_failed_jointPublication parameter randomness index leaves ftsPath layers
      table state finalState ftsFuel remaining context fuel otsTable cache entry hresult hfailed)

end SphincsSecurity.Concrete.FtsProbeSimulation
