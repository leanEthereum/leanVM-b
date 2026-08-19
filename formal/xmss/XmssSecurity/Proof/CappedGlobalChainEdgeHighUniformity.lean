import XmssSecurity.Proof.CappedGlobalChainPresampling
import XmssSecurity.Proof.ChainEdgeHighUniformity

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable local instance globalHighSampleableEdges :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

noncomputable def globalChainEdgeHighTableOfTape
    (outputs : List HashOutput) : GlobalChainEdgeIndex → Digest :=
  globalChainEdgeTableOfTape (outputs.map XmssSecurity.hashOutputHigh)

noncomputable def globalChainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  match cache (globalChainTableEdgeInput parameter table edge) with
  | none => 0
  | some output => XmssSecurity.hashOutputHigh output

def globalChainEdgeOutputFromHigh
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashOutput :=
  Rom.hashOutputEquivDigestPair.symm
    (high edge, globalChainTableEdgeTarget table edge)

theorem globalChainEdgeOutputFromHigh_eq_cached
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (output : HashOutput)
    (hcache : cache (globalChainTableEdgeInput parameter table edge) =
      some output)
    (htarget : truncateHash output = globalChainTableEdgeTarget table edge) :
    globalChainEdgeOutputFromHigh
        (globalChainEdgeHighTableOfCache cache parameter table) table edge =
      output := by
  simp [globalChainEdgeOutputFromHigh, globalChainEdgeHighTableOfCache,
    hcache, XmssSecurity.hashOutputHigh, ← htarget]
  exact Rom.hashOutputEquivDigestPair.symm_apply_apply output

theorem globalChainEdgeHighTableOfCache_mono
    (cache larger : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    globalChainEdgeHighTableOfCache cache parameter table =
      globalChainEdgeHighTableOfCache larger parameter table := by
  funext edge
  obtain ⟨output, hcache, _htarget⟩ := hmatches edge
  have hlarger := hle hcache
  simp [globalChainEdgeHighTableOfCache, hcache, hlarger]

theorem truncateHash_globalChainEdgeOutputFromHigh
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    truncateHash (globalChainEdgeOutputFromHigh high table edge) =
      globalChainTableEdgeTarget table edge := by
  simp [globalChainEdgeOutputFromHigh]

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

theorem map_globalChainEdgeTableOfTape
    (targets : List Digest)
    (hlength : targets.length = allGlobalChainEdges.length) :
    allGlobalChainEdges.map (globalChainEdgeTableOfTape targets) = targets := by
  unfold globalChainEdgeTableOfTape
  rw [dif_pos hlength]
  calc
    allGlobalChainEdges.map
        (globalChainEdgeTableTapeEquiv.symm fun index =>
          targets.get (Fin.cast hlength.symm index)) =
        List.ofFn (globalChainEdgeTableTapeEquiv
          (globalChainEdgeTableTapeEquiv.symm fun index =>
            targets.get (Fin.cast hlength.symm index))) :=
      (listOfFn_globalChainEdgeTableTapeEquiv _).symm
    _ = List.ofFn (fun index =>
          targets.get (Fin.cast hlength.symm index)) := by
      rw [globalChainEdgeTableTapeEquiv.apply_symm_apply]
    _ = List.ofFn targets.get := by
      exact (List.ofFn_congr hlength targets.get).symm
    _ = targets := List.ofFn_get targets

theorem cappedSampleHashOutputsWithDigests_support_info :
    ∀ (targets : List Digest) (outputs : List HashOutput),
      outputs ∈ support (sampleHashOutputsWithDigests targets) →
      outputs.length = targets.length ∧ outputs.map truncateHash = targets := by
  intro targets
  induction targets with
  | nil =>
      intro outputs houtputs
      simp only [sampleHashOutputsWithDigests_nil, support_pure,
        Set.mem_singleton_iff] at houtputs
      subst outputs
      simp
  | cons target targets ih =>
      intro outputs houtputs
      rw [sampleHashOutputsWithDigests_cons, mem_support_bind_iff] at houtputs
      obtain ⟨output, houtput, hrest⟩ := houtputs
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst outputs
      obtain ⟨hlength, htargets⟩ := ih rest hrest
      exact ⟨by simp [hlength], by
        simp [Rom.sampleHashOutputWithDigest_support_truncate
          target output houtput, htargets]⟩

theorem globalEqOnListOfMapEq
    {α β : Type} (left right : α → β) (values : List α)
    (heq : values.map left = values.map right) :
    ∀ value ∈ values, left value = right value := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at heq
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact heq.1
      · exact ih heq.2 value htail

set_option linter.constructorNameAsVariable false in
theorem installGlobalChainTableEdgeOutputs_info
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    ∀ (edges : List GlobalChainEdgeIndex) (outputs : List HashOutput)
      (cache : QueryCache HashSpec),
      edges.Nodup →
      (∀ edge ∈ edges,
        cache (globalChainTableEdgeInput parameter table edge) = none) →
      outputs.length = edges.length →
      outputs.map truncateHash =
        edges.map (globalChainTableEdgeTarget table) →
      cache ≤ installGlobalChainTableEdgeOutputs cache parameter table
          edges outputs ∧
        List.Forall₂
          (fun edge output =>
            (installGlobalChainTableEdgeOutputs cache parameter table
                edges outputs)
                (globalChainTableEdgeInput parameter table edge) =
                  some output ∧
              truncateHash output = globalChainTableEdgeTarget table edge)
          edges outputs := by
  intro edges
  induction edges with
  | nil =>
      intro outputs cache _hnodup _habsent hlength _htargets
      cases outputs with
      | nil => simp
      | cons output outputs => simp at hlength
  | cons edge edges ih =>
      intro outputList cache hnodup habsent hlength htargets
      cases outputList with
      | nil => simp at hlength
      | cons output outputs =>
          obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [List.map_cons, List.cons.injEq] at htargets
          have htailAbsent : ∀ target ∈ edges,
              (cache.cacheQuery
                (globalChainTableEdgeInput parameter table edge) output)
                (globalChainTableEdgeInput parameter table target) = none := by
            intro target htarget
            rw [QueryCache.cacheQuery_of_ne]
            · exact habsent target (by simp [htarget])
            · intro heq
              exact hnotMem
                ((globalChainTableEdgeInput_injective parameter table)
                  heq.symm ▸ htarget)
          obtain ⟨hcacheLe, hpairs⟩ := ih outputs
            (cache.cacheQuery
              (globalChainTableEdgeInput parameter table edge) output)
            htailNodup htailAbsent hlength htargets.2
          constructor
          · exact (QueryCache.le_cacheQuery cache
              (habsent edge (by simp))).trans hcacheLe
          · apply List.Forall₂.cons
            · exact ⟨hcacheLe (QueryCache.cacheQuery_self cache
                (globalChainTableEdgeInput parameter table edge) output),
                htargets.1⟩
            · exact hpairs

theorem globalChainEdgeHighTableOfCache_installOutputs
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) (outputs : List HashOutput)
    (hlength : outputs.length = allGlobalChainEdges.length)
    (htargets : outputs.map truncateHash =
      globalChainTableEdgeTargets table) :
    globalChainEdgeHighTableOfCache
        (installGlobalChainTableEdgeOutputs ∅ parameter table
          allGlobalChainEdges outputs)
        parameter table = globalChainEdgeHighTableOfTape outputs := by
  let installed := installGlobalChainTableEdgeOutputs ∅ parameter table
    allGlobalChainEdges outputs
  have hpairs : List.Forall₂
      (fun edge output =>
        installed (globalChainTableEdgeInput parameter table edge) =
            some output ∧
          truncateHash output = globalChainTableEdgeTarget table edge)
      allGlobalChainEdges outputs := by
    have hinstalled := installGlobalChainTableEdgeOutputs_info parameter table
      allGlobalChainEdges outputs ∅ allGlobalChainEdges_nodup (by simp)
        hlength htargets
    simpa [installed] using hinstalled.2
  have hpairsHigh : List.Forall₂
      (fun edge high =>
        globalChainEdgeHighTableOfCache installed parameter table edge = high)
      allGlobalChainEdges
        (outputs.map XmssSecurity.hashOutputHigh) := by
    rw [List.forall₂_map_right_iff]
    apply hpairs.imp
    intro edge output houtput
    simp [globalChainEdgeHighTableOfCache, installed, houtput.1,
      XmssSecurity.hashOutputHigh]
  have hmaps : allGlobalChainEdges.map
      (globalChainEdgeHighTableOfCache installed parameter table) =
      outputs.map XmssSecurity.hashOutputHigh := by
    rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff]
    exact hpairsHigh
  funext edge
  apply globalEqOnListOfMapEq
    (globalChainEdgeHighTableOfCache installed parameter table)
    (globalChainEdgeHighTableOfTape outputs) allGlobalChainEdges
  · rw [hmaps]
    unfold globalChainEdgeHighTableOfTape
    exact (map_globalChainEdgeTableOfTape
      (outputs.map XmssSecurity.hashOutputHigh) (by simpa using hlength)).symm
  · exact mem_allGlobalChainEdges edge

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000000 in
theorem evalDist_programGlobalChainTableEdgesTrace_highTable_eq_uniform
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    evalDist ((fun result : List HashOutput × QueryCache HashSpec =>
      globalChainEdgeHighTableOfCache result.2 parameter table) <$>
        programGlobalChainTableEdgesTrace ∅ parameter table
          allGlobalChainEdges) =
    evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist ((fun result : List HashOutput × QueryCache HashSpec =>
          globalChainEdgeHighTableOfCache result.2 parameter table) <$>
        ((fun outputs =>
          (outputs, installGlobalChainTableEdgeOutputs ∅ parameter table
            allGlobalChainEdges outputs)) <$>
          sampleHashOutputsWithDigests (globalChainTableEdgeTargets table))) := by
      unfold globalChainTableEdgeTargets
      rw [evalDist_map,
        evalDist_programGlobalChainTableEdgesTrace_eq_install,
        ← evalDist_map]
    _ = evalDist (globalChainEdgeHighTableOfTape <$>
        sampleHashOutputsWithDigests
          (globalChainTableEdgeTargets table)) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply evalDist_bind_congr
      intro outputs houtputs
      obtain ⟨hlength, htargets⟩ :=
        cappedSampleHashOutputsWithDigests_support_info
          (globalChainTableEdgeTargets table) outputs houtputs
      have hlength' : outputs.length = allGlobalChainEdges.length := by
        simpa [globalChainTableEdgeTargets] using hlength
      rw [globalChainEdgeHighTableOfCache_installOutputs
        parameter table outputs hlength' htargets]
      simp only [Function.comp_apply]
    _ = evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) :=
      evalDist_sampleGlobalChainEdgeOutputs_highTable_eq_uniform table

end XmssSecurity.CappedChain
