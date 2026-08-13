import XmssSecurity.ChainTablePresampling

open OracleComp OracleSpec

namespace XmssSecurity

attribute [local instance] presamplingSampleableChainEdges

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

theorem evalDist_sampleHashOutputsWithDigests_high
    (targets : List Digest) :
    𝒟[(List.map hashOutputHigh) <$>
      sampleHashOutputsWithDigests targets] =
    𝒟[OracleComp.drawList ($ᵗ Digest) targets.length] := by
  induction targets with
  | nil => simp [sampleHashOutputsWithDigests, OracleComp.drawList]
  | cons target targets ih =>
      rw [sampleHashOutputsWithDigests_cons, OracleComp.drawList.eq_def]
      unfold Rom.sampleHashOutputWithDigest
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, List.length_cons]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro high
      simp only [hashOutputHigh, Rom.hashOutputEquivDigestPair.apply_symm_apply,
        List.map_cons]
      calc
        𝒟[(fun outputs => high :: List.map hashOutputHigh outputs) <$>
            sampleHashOutputsWithDigests targets] =
          𝒟[(fun outputs => high :: outputs) <$>
            ((List.map hashOutputHigh) <$>
              sampleHashOutputsWithDigests targets)] := by
            simp [Functor.map_map]
        _ = 𝒟[(fun outputs => high :: outputs) <$>
            OracleComp.drawList ($ᵗ Digest) targets.length] := by
          rw [evalDist_map, ih, ← evalDist_map]

noncomputable def chainEdgeHighTableOfTape
    (outputs : List HashOutput) : ChainEdgeIndex → Digest :=
  chainEdgeTableOfTape (outputs.map hashOutputHigh)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_sampleChainEdgeOutputs_highTable_eq_uniform
    (table : ChainValueIndex → Digest) :
    𝒟[chainEdgeHighTableOfTape <$>
      sampleHashOutputsWithDigests (chainTableEdgeTargets table)] =
    𝒟[$ᵗ (ChainEdgeIndex → Digest)] := by
  calc
    𝒟[chainEdgeHighTableOfTape <$>
        sampleHashOutputsWithDigests (chainTableEdgeTargets table)] =
      𝒟[chainEdgeTableOfTape <$>
        ((List.map hashOutputHigh) <$>
          sampleHashOutputsWithDigests (chainTableEdgeTargets table))] := by
        have hfun : chainEdgeHighTableOfTape =
            fun outputs => chainEdgeTableOfTape
              (List.map hashOutputHigh outputs) := by
          rfl
        rw [hfun, ← Functor.map_map]
    _ = 𝒟[chainEdgeTableOfTape <$>
        OracleComp.drawList ($ᵗ Digest) allChainEdges.length] := by
      rw [evalDist_map, evalDist_sampleHashOutputsWithDigests_high,
        chainTableEdgeTargets_length, allChainEdges_length, ← evalDist_map]
    _ = 𝒟[chainEdgeTableOfTape <$>
        ((fun edgeTable : ChainEdgeIndex → Digest =>
          allChainEdges.map edgeTable) <$>
          ($ᵗ (ChainEdgeIndex → Digest)))] := by
      have htape :
          (fun table : ChainEdgeIndex → Digest => allChainEdges.map table) =
          (fun edgeTable : ChainEdgeIndex → Digest =>
            allChainEdges.map edgeTable) := rfl
      rw [← htape]
      rw [evalDist_map, evalDist_map,
        evalDist_uniformChainEdgeTableTape_eq_drawList]
    _ = 𝒟[$ᵗ (ChainEdgeIndex → Digest)] := by
      simp [Functor.map_map]

end XmssSecurity
