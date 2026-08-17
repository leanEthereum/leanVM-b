import XmssSecurity.CappedGlobalChainPresampling
import XmssSecurity.ChainEdgeHighUniformity

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable local instance globalHighSampleableEdges :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

noncomputable def globalChainEdgeHighTableOfTape
    (outputs : List HashOutput) : GlobalChainEdgeIndex → Digest :=
  globalChainEdgeTableOfTape (outputs.map XmssSecurity.hashOutputHigh)

theorem evalDist_cappedSampleHashOutputsWithDigests_high
    (targets : List Digest) :
    evalDist ((List.map XmssSecurity.hashOutputHigh) <$>
      sampleHashOutputsWithDigests targets) =
    evalDist (OracleComp.drawList ($ᵗ Digest) targets.length) := by
  induction targets with
  | nil => simp [sampleHashOutputsWithDigests, OracleComp.drawList]
  | cons target targets ih =>
      rw [sampleHashOutputsWithDigests_cons, OracleComp.drawList.eq_def]
      unfold Rom.sampleHashOutputWithDigest
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, List.length_cons]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro high
      simp only [XmssSecurity.hashOutputHigh,
        Rom.hashOutputEquivDigestPair.apply_symm_apply, List.map_cons]
      calc
        evalDist ((fun outputs =>
            high :: List.map XmssSecurity.hashOutputHigh outputs) <$>
          sampleHashOutputsWithDigests targets) =
          evalDist ((fun outputs => high :: outputs) <$>
            ((List.map XmssSecurity.hashOutputHigh) <$>
              sampleHashOutputsWithDigests targets)) := by
            simp [Functor.map_map]
        _ = evalDist ((fun outputs => high :: outputs) <$>
            OracleComp.drawList ($ᵗ Digest) targets.length) := by
          rw [evalDist_map, ih, ← evalDist_map]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 5000000 in
theorem evalDist_uniformHashTape_globalChainEdgeHalves_independent :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (globalChainEdgeTableOfTape tape.1,
        globalChainEdgeHighTableOfTape tape.2)) <$>
      Rom.uniformHashTape allGlobalChainEdges.length) =
    evalDist (do
      let lows ← $ᵗ (GlobalChainEdgeIndex → Digest)
      let highs ← $ᵗ (GlobalChainEdgeIndex → Digest)
      pure (lows, highs)) := by
  let splitTape := fun tape : List Digest × List HashOutput =>
    (tape.1, tape.2.map XmssSecurity.hashOutputHigh)
  let toTables := fun halves : List Digest × List Digest =>
    (globalChainEdgeTableOfTape halves.1,
      globalChainEdgeTableOfTape halves.2)
  calc
    _ = evalDist (toTables <$> (splitTape <$>
        Rom.uniformHashTape allGlobalChainEdges.length)) := by
      simp [splitTape, toTables, globalChainEdgeHighTableOfTape,
        Functor.map_map]
    _ = evalDist (toTables <$> (do
        let lows ← OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length
        let highs ← OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length
        pure (lows, highs))) := by
      rw [evalDist_map,
        XmssSecurity.evalDist_uniformHashTape_halves_independent
          allGlobalChainEdges.length,
        ← evalDist_map]
    _ = evalDist ((globalChainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length) >>=
        fun lows =>
        (globalChainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length) >>=
        fun highs => pure (lows, highs)) := by
      simp [toTables, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun lows =>
        (globalChainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length) >>=
        fun highs => pure (lows, highs)) := by
      rw [evalDist_bind, evalDist_bind,
        evalDist_globalChainEdgeTableOfTape_drawList_eq_uniform]
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro lows
      change evalDist ((fun highs => (lows, highs)) <$>
          (globalChainEdgeTableOfTape <$>
            OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length)) =
        evalDist ((fun highs => (lows, highs)) <$>
          ($ᵗ (GlobalChainEdgeIndex → Digest)))
      rw [evalDist_map,
        evalDist_globalChainEdgeTableOfTape_drawList_eq_uniform,
        ← evalDist_map]

set_option maxRecDepth 1000000 in
theorem evalDist_uniformHashTape_globalFixedSeeds_table_high_independent
    (seeds : Epoch → ChainIndex → Digest) :
    evalDist ((fun tape : List Digest × List HashOutput =>
      (globalChainTableMaterialEquiv.symm
          (seeds, globalChainEdgeTableOfTape tape.1),
        globalChainEdgeHighTableOfTape tape.2)) <$>
      Rom.uniformHashTape allGlobalChainEdges.length) =
    evalDist (do
      let edges ← $ᵗ (GlobalChainEdgeIndex → Digest)
      let high ← $ᵗ (GlobalChainEdgeIndex → Digest)
      pure (globalChainTableMaterialEquiv.symm (seeds, edges), high)) := by
  let finish := fun halves :
      (GlobalChainEdgeIndex → Digest) ×
        (GlobalChainEdgeIndex → Digest) =>
    (globalChainTableMaterialEquiv.symm (seeds, halves.1), halves.2)
  calc
    _ = evalDist (finish <$>
        ((fun tape : List Digest × List HashOutput =>
          (globalChainEdgeTableOfTape tape.1,
            globalChainEdgeHighTableOfTape tape.2)) <$>
          Rom.uniformHashTape allGlobalChainEdges.length)) := by
      simp [finish, Functor.map_map]
    _ = evalDist (finish <$> (do
        let edges ← $ᵗ (GlobalChainEdgeIndex → Digest)
        let high ← $ᵗ (GlobalChainEdgeIndex → Digest)
        pure (edges, high))) := by
      rw [evalDist_map,
        evalDist_uniformHashTape_globalChainEdgeHalves_independent,
        ← evalDist_map]
    _ = _ := by
      simp [finish, map_eq_bind_pure_comp, bind_assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000000 in
theorem evalDist_sampleGlobalChainEdgeOutputs_highTable_eq_uniform
    (table : GlobalChainValueIndex → Digest) :
    evalDist (globalChainEdgeHighTableOfTape <$>
      sampleHashOutputsWithDigests (globalChainTableEdgeTargets table)) =
    evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    evalDist (globalChainEdgeHighTableOfTape <$>
        sampleHashOutputsWithDigests (globalChainTableEdgeTargets table)) =
      evalDist (globalChainEdgeTableOfTape <$>
        ((List.map XmssSecurity.hashOutputHigh) <$>
          sampleHashOutputsWithDigests
            (globalChainTableEdgeTargets table))) := by
        have hfun : globalChainEdgeHighTableOfTape =
            fun outputs => globalChainEdgeTableOfTape
              (List.map XmssSecurity.hashOutputHigh outputs) := by
          rfl
        rw [hfun, ← Functor.map_map]
    _ = evalDist (globalChainEdgeTableOfTape <$>
        OracleComp.drawList ($ᵗ Digest)
          (globalChainTableEdgeTargets table).length) := by
      rw [evalDist_map,
        evalDist_cappedSampleHashOutputsWithDigests_high,
        ← evalDist_map]
    _ = evalDist (globalChainEdgeTableOfTape <$>
        OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length) := by
      have hlength : (globalChainTableEdgeTargets table).length =
          allGlobalChainEdges.length := by
        simp [globalChainTableEdgeTargets]
      rw [hlength]
    _ = evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
      exact evalDist_globalChainEdgeTableOfTape_drawList_eq_uniform

end XmssSecurity.CappedChain
