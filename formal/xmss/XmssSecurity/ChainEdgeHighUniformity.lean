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

set_option maxRecDepth 1000000 in
theorem evalDist_batchProgrammedHashTape_halves_independent
    (count : Nat) :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (tape.1, tape.2.map hashOutputHigh)) <$>
        batchProgrammedHashTape count) =
    evalDist (do
      let lows ← OracleComp.drawList ($ᵗ Digest) count
      let highs ← OracleComp.drawList ($ᵗ Digest) count
      pure (lows, highs)) := by
  unfold batchProgrammedHashTape
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro targets htargets
  have hlength : targets.length = count :=
    drawList_support_length ($ᵗ Digest) count targets htargets
  calc
    evalDist ((fun outputs : List HashOutput =>
          (targets, outputs.map hashOutputHigh)) <$>
        sampleHashOutputsWithDigests targets) =
      evalDist ((fun highs : List Digest => (targets, highs)) <$>
        ((List.map hashOutputHigh) <$>
          sampleHashOutputsWithDigests targets)) := by
        simp [Functor.map_map]
    _ = evalDist ((fun highs : List Digest => (targets, highs)) <$>
        OracleComp.drawList ($ᵗ Digest) targets.length) := by
      rw [evalDist_map,
        evalDist_sampleHashOutputsWithDigests_high targets, ← evalDist_map]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest) count >>= fun highs =>
        pure (targets, highs)) := by
      rw [hlength]
      simp [map_eq_bind_pure_comp]

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashTape_halves_independent
    (count : Nat) :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (tape.1, tape.2.map hashOutputHigh)) <$>
        Rom.uniformHashTape count) =
    evalDist (do
      let lows ← OracleComp.drawList ($ᵗ Digest) count
      let highs ← OracleComp.drawList ($ᵗ Digest) count
      pure (lows, highs)) := by
  calc
    _ = evalDist ((fun tape : List Digest × List HashOutput =>
          (tape.1, tape.2.map hashOutputHigh)) <$>
        batchProgrammedHashTape count) := by
      rw [evalDist_map, evalDist_map]
      exact congrArg
        (Functor.map (fun tape : List Digest × List HashOutput =>
          (tape.1, tape.2.map hashOutputHigh)))
        ((evalDist_batchProgrammedHashTape_eq_programmedHashTape count).trans
          (Rom.evalDist_programmedHashTape_eq_uniformHashTape count)).symm
    _ = _ := evalDist_batchProgrammedHashTape_halves_independent count

noncomputable def chainEdgeHighTableOfTape
    (outputs : List HashOutput) : ChainEdgeIndex → Digest :=
  chainEdgeTableOfTape (outputs.map hashOutputHigh)

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashTape_chainEdgeHalves_independent :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (chainEdgeTableOfTape tape.1, chainEdgeHighTableOfTape tape.2)) <$>
        Rom.uniformHashTape allChainEdges.length) =
    evalDist (do
      let lows ← $ᵗ (ChainEdgeIndex → Digest)
      let highs ← $ᵗ (ChainEdgeIndex → Digest)
      pure (lows, highs)) := by
  let splitTape := fun tape : List Digest × List HashOutput =>
    (tape.1, tape.2.map hashOutputHigh)
  let toTables := fun halves : List Digest × List Digest =>
    (chainEdgeTableOfTape halves.1, chainEdgeTableOfTape halves.2)
  calc
    _ = evalDist (toTables <$> (splitTape <$>
        Rom.uniformHashTape allChainEdges.length)) := by
      simp [splitTape, toTables, chainEdgeHighTableOfTape, Functor.map_map]
    _ = evalDist (toTables <$> (do
        let lows ← OracleComp.drawList ($ᵗ Digest) allChainEdges.length
        let highs ← OracleComp.drawList ($ᵗ Digest) allChainEdges.length
        pure (lows, highs))) := by
      rw [evalDist_map,
        evalDist_uniformHashTape_halves_independent allChainEdges.length,
        ← evalDist_map]
    _ = evalDist ((chainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allChainEdges.length) >>= fun lows =>
        (chainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allChainEdges.length) >>= fun highs =>
        pure (lows, highs)) := by
      simp [toTables, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (ChainEdgeIndex → Digest)) >>= fun lows =>
        (chainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allChainEdges.length) >>= fun highs =>
        pure (lows, highs)) := by
      rw [evalDist_bind,
        evalDist_chainEdgeTableOfTape_drawList_eq_uniform, ← evalDist_bind]
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro lows
      rw [evalDist_bind,
        evalDist_chainEdgeTableOfTape_drawList_eq_uniform, ← evalDist_bind]

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashTape_fixedSeeds_table_high_independent
    (seeds : Epoch → Digest) :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (chainTableMaterialEquiv.symm
          (seeds, chainEdgeTableOfTape tape.1),
        chainEdgeHighTableOfTape tape.2)) <$>
      Rom.uniformHashTape allChainEdges.length) =
    evalDist (do
      let edges ← $ᵗ (ChainEdgeIndex → Digest)
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (chainTableMaterialEquiv.symm (seeds, edges), high)) := by
  let finish := fun halves :
      (ChainEdgeIndex → Digest) × (ChainEdgeIndex → Digest) =>
    (chainTableMaterialEquiv.symm (seeds, halves.1), halves.2)
  calc
    _ = evalDist (finish <$>
        ((fun tape : List Digest × List HashOutput =>
          (chainEdgeTableOfTape tape.1,
            chainEdgeHighTableOfTape tape.2)) <$>
          Rom.uniformHashTape allChainEdges.length)) := by
      simp [finish, Functor.map_map]
    _ = evalDist (finish <$> (do
        let edges ← $ᵗ (ChainEdgeIndex → Digest)
        let high ← $ᵗ (ChainEdgeIndex → Digest)
        pure (edges, high))) := by
      rw [evalDist_map,
        evalDist_uniformHashTape_chainEdgeHalves_independent, ← evalDist_map]
    _ = _ := by
      simp [finish, map_eq_bind_pure_comp, bind_assoc]

noncomputable def fixedChainMaterialHighTable
    (material : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec))) :
    ChainEdgeIndex → Digest :=
  chainEdgeHighTableOfTape material.2.2.1

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
