import SphincsSecurity.Proof.JointProbePublicationFailureSupport
import SphincsSecurity.Proof.OtsProbePublicationChainCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex ChainsPublishedOutside ChainOutsideLayerPart MaterializedChainsPublished)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem materializedChainsPublished_of_successful_jointPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hpublic : ChainsPublishedOutside (fun coordinate => ∀ lay, ChainOutsideLayerPart coordinate index lay (layers lay)) context)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourcePublication parameter randomness index leaves ftsPath layers).run cache) context fuel otsTable)))
    (hsuccess : entry.value.1 ≠ none) : MaterializedChainsPublished entry.context := by
  rw [jointSourcePublication_eq_unmerged] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceUnmergedNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  dsimp only at hrest
  cases hbody : native.value.1 with
  | none =>
      simp only [hbody, StateT.run_pure, runJointResolved_pure, AdaptiveRevealProbe.runRaw, construct_pure,
        mem_support_pure_iff, AdaptiveRevealProbe.RawResult.done.injEq, Option.some.injEq] at hrest
      obtain ⟨_, _, heq⟩ := hrest
      subst entry
      exact False.elim (hsuccess rfl)
  | some body =>
      have hpublished := OtsProbeSimulation.materializedChainsPublished_of_successful_publishSignatureBody
        randomness index ftsPath layers context fuel otsTable cache.1 native hpublic hnative (by simp [hbody])
      simp only [hbody] at hrest
      rw [StateT.run_map, runJointResolved_map, AdaptiveRevealProbe.runRaw_mapValue, support_map] at hrest
      obtain ⟨result, hftsResult, heq⟩ := hrest
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
              obtain ⟨value, finalCache, rfl, _⟩ := mem_support_jointSourceFtsBlock_raw_done
                table middleState resultState middleFuel resultFuel _ native.context native.remaining native.table
                (native.value.2, cache.2) result hftsResult
              exact hpublished

end SphincsSecurity.Concrete.FtsProbeSimulation
