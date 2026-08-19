import XmssSecurity.Proof.CausalObservedMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

attribute [local instance] presamplingSampleableChainEdges

noncomputable def fixedChainOutsideTableHighView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) :=
  (fun material =>
    ((outsideChainSecret chain material.1.2,
      fixedChainMaterialTable chain material),
      fixedChainMaterialHighTable material)) <$>
        fixedChainMaterialRepresentation parameter chain

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainOutsideTableHighView_eq_appendUniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (fixedChainOutsideTableHighView parameter chain) =
    evalDist (do
      let outsideTable ← fixedChainOutsideTableView parameter chain
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (outsideTable, high)) := by
  unfold fixedChainOutsideTableHighView fixedChainOutsideTableView
    fixedChainMaterialRepresentation uniformInstalledChainEdgeCache
    installedChainEdgeTapeResult fixedChainMaterialTable
    fixedChainMaterialHighTable
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let finish := fun result :
      (ChainValueIndex → Digest) × (ChainEdgeIndex → Digest) =>
    ((outsideChainSecret chain secretView.2, result.1), result.2)
  calc
    _ = evalDist (finish <$>
        ((fun tape : List Digest × List HashOutput =>
          (chainTableMaterialEquiv.symm
              ((fun epoch => secretView.2 (epoch, chain)),
                chainEdgeTableOfTape tape.1),
            chainEdgeHighTableOfTape tape.2)) <$>
          Rom.uniformHashTape allChainEdges.length)) := by
      simp [finish, Functor.map_map]
    _ = evalDist (finish <$> (do
        let edges ← $ᵗ (ChainEdgeIndex → Digest)
        let high ← $ᵗ (ChainEdgeIndex → Digest)
        pure (chainTableMaterialEquiv.symm
          ((fun epoch => secretView.2 (epoch, chain)), edges), high))) := by
      rw [evalDist_map,
        evalDist_uniformHashTape_fixedSeeds_table_high_independent,
        ← evalDist_map]
    _ = evalDist (do
        let edges ← $ᵗ (ChainEdgeIndex → Digest)
        let high ← $ᵗ (ChainEdgeIndex → Digest)
        pure ((outsideChainSecret chain secretView.2,
          chainTableMaterialEquiv.symm
            ((fun epoch => secretView.2 (epoch, chain)), edges)), high)) := by
      simp [finish, map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by
      have hlow := evalDist_uniformInstalledChainEdgeTable_eq_uniform
        parameter chain (fun epoch => secretView.2 (epoch, chain))
      unfold uniformInstalledChainEdgeCache installedChainEdgeTapeResult at hlow
      simp only [Functor.map_map] at hlow
      symm
      calc
        _ = evalDist (((fun tape : List Digest × List HashOutput =>
              chainEdgeTableOfTape tape.1) <$>
            Rom.uniformHashTape allChainEdges.length) >>= fun edges =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
          pure ((outsideChainSecret chain secretView.2,
            chainTableMaterialEquiv.symm
              ((fun epoch => secretView.2 (epoch, chain)), edges)), high)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = _ := by
          rw [evalDist_bind, hlow, ← evalDist_bind]

noncomputable def fixedChainMaterialWithBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) := do
  let materialBase ← fixedChainMaterialWithBase parameter chain
  let high ← $ᵗ (ChainEdgeIndex → Digest)
  pure (materialBase, high)

def fixedChainMaterialBaseHighView (chain : ChainIndex)
    (result : (FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) :
    (OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest) :=
  ((outsideChainSecret chain result.1.1.1.2, result.1.2), result.2)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainOutsideTableHighView_eq_baseHighView
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (fixedChainOutsideTableHighView parameter chain) =
    evalDist (fixedChainMaterialBaseHighView chain <$>
      fixedChainMaterialWithBaseHigh parameter chain) := by
  calc
    _ = evalDist (fixedChainOutsideTableView parameter chain >>= fun view =>
        ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
        pure (view, high)) :=
      evalDist_fixedChainOutsideTableHighView_eq_appendUniform parameter chain
    _ = evalDist ((fixedChainMaterialBaseView chain <$>
          fixedChainMaterialWithBase parameter chain) >>= fun view =>
        ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
        pure (view, high)) := by
      rw [evalDist_bind,
        evalDist_fixedChainMaterialOutsideTable_eq_baseView parameter chain,
        ← evalDist_bind]
    _ = _ := by
      simp [fixedChainMaterialWithBaseHigh, fixedChainMaterialBaseView,
        fixedChainMaterialBaseHighView, map_eq_bind_pure_comp, bind_assoc]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem fixedChainMaterialWithBaseHigh_support_material
    (parameter : PublicParameter) (chain : ChainIndex)
    (result : (FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest))
    (hresult : result ∈ support
      (fixedChainMaterialWithBaseHigh parameter chain)) :
    result.1.1 ∈ support
      (fixedChainMaterialRepresentation parameter chain) := by
  unfold fixedChainMaterialWithBaseHigh at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨materialBase, hmaterialBase, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨high, _hhigh, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact fixedChainMaterialWithBase_support_material
    parameter chain materialBase hmaterialBase

def CoupledFixedChainMaterialBaseHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : FixedChainMaterial)
    (right : (FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) : Prop :=
  fixedChainMaterialTable chain left = right.1.2 ∧
    fixedChainMaterialHighTable left = right.2 ∧
    outsideChainSecret chain left.1.2 =
      outsideChainSecret chain right.1.1.1.2 ∧
    left ∈ support (fixedChainMaterialRepresentation parameter chain) ∧
    right.1.1 ∈ support
      (fixedChainMaterialRepresentation parameter chain)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_fixedChainMaterialRepresentation_withBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (fixedChainMaterialRepresentation parameter chain)
      (fixedChainMaterialWithBaseHigh parameter chain)
      (CoupledFixedChainMaterialBaseHighRelation parameter chain) := by
  classical
  letI : DecidableEq
      ((OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
        (ChainEdgeIndex → Digest)) := Classical.decEq _
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_with_support_general
      (fixedChainMaterialRepresentation parameter chain)
      (fixedChainMaterialWithBaseHigh parameter chain)
      (fun material =>
        ((outsideChainSecret chain material.1.2,
          fixedChainMaterialTable chain material),
          fixedChainMaterialHighTable material))
      (fixedChainMaterialBaseHighView chain)
      (evalDist_fixedChainOutsideTableHighView_eq_baseHighView
        parameter chain))
  intro left right hrelation
  have htable : fixedChainMaterialTable chain left = right.1.2 :=
    congrArg (fun view => view.1.2) hrelation.1
  have hhigh : fixedChainMaterialHighTable left = right.2 :=
    congrArg Prod.snd hrelation.1
  have houtside : outsideChainSecret chain left.1.2 =
      outsideChainSecret chain right.1.1.1.2 :=
    congrArg (fun view => view.1.1) hrelation.1
  exact ⟨htable, hhigh, houtside, hrelation.2.1,
    fixedChainMaterialWithBaseHigh_support_material
      parameter chain right hrelation.2.2⟩

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem fixedChainMaterialHighTable_eq_cacheHigh
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : FixedChainMaterial)
    (hmaterial : material ∈ support
      (fixedChainMaterialRepresentation parameter chain)) :
    fixedChainMaterialHighTable material =
      chainEdgeHighTableOfCache material.2.2.2 parameter chain
        (fixedChainMaterialTable chain material) := by
  unfold fixedChainMaterialRepresentation at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨secretView, _hsecretView, hedgeView⟩ := hmaterial
  rw [mem_support_bind_iff] at hedgeView
  obtain ⟨edgeView, hedgeView, hpure⟩ := hedgeView
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  unfold uniformInstalledChainEdgeCache at hedgeView
  rw [support_map] at hedgeView
  obtain ⟨tape, htape, htapeEq⟩ := hedgeView
  subst edgeView
  unfold fixedChainMaterialHighTable fixedChainMaterialTable
    installedChainEdgeTapeResult
  symm
  apply chainEdgeHighTableOfCache_installChainTableEdgeOutputs
  · exact (uniformHashTape_support_info
      allChainEdges.length tape htape).2.1
  · have hinfo := uniformHashTape_support_info
      allChainEdges.length tape htape
    calc
      tape.2.map truncateHash = tape.1 := hinfo.2.2
      _ = allChainEdges.map (chainEdgeTableOfTape tape.1) :=
        (map_chainEdgeTableOfTape tape.1 hinfo.1).symm
      _ = chainTableEdgeTargets
          (chainTableMaterialEquiv.symm
            ((fun epoch => secretView.2 (epoch, chain)),
              chainEdgeTableOfTape tape.1)) := by
        unfold chainTableEdgeTargets
        rw [chainTableEdgeTarget_materialEquiv_symm]

theorem chainEdgeHighTableOfCache_mono
    (cache larger : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (hmatches : ChainTableEdgesMatch cache parameter chain table)
    (hle : cache ≤ larger) :
    chainEdgeHighTableOfCache cache parameter chain table =
      chainEdgeHighTableOfCache larger parameter chain table := by
  funext edge
  obtain ⟨output, hcache, _htarget⟩ := hmatches edge
  have hlarger := hle hcache
  simp [chainEdgeHighTableOfCache, hcache, hlarger]

structure CoupledFixedChainMaterialHighInvariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : (FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) : Prop where
  base : CoupledFixedChainMaterialInvariant parameter selected left right.1
  highEq : chainEdgeHighTableOfCache left.2.2.2 parameter selected
      (fixedChainMaterialTable selected left) = right.2

theorem coupledFixedChainMaterialBaseHighRelation_to_invariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : (FixedChainMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseHighRelation
      parameter selected left right) :
    CoupledFixedChainMaterialHighInvariant
      parameter selected left right := by
  refine ⟨coupledFixedChainMaterialBaseRelation_to_invariant
    parameter selected left right.1 ?_, ?_⟩
  · exact ⟨hrel.1, hrel.2.2.1, hrel.2.2.2.1, hrel.2.2.2.2⟩
  · exact (fixedChainMaterialHighTable_eq_cacheHigh
      parameter selected left hrel.2.2.2.1).symm.trans hrel.2.1

theorem relTriple_fixedChainMaterialRepresentation_withBaseHigh_invariant
    (parameter : PublicParameter) (selected : ChainIndex) :
    RelTriple
      (fixedChainMaterialRepresentation parameter selected)
      (fixedChainMaterialWithBaseHigh parameter selected)
      (CoupledFixedChainMaterialHighInvariant parameter selected) := by
  apply relTriple_post_mono
    (relTriple_fixedChainMaterialRepresentation_withBaseHigh
      parameter selected)
  exact coupledFixedChainMaterialBaseHighRelation_to_invariant
    parameter selected

noncomputable def fixedChainTreeKeygenWithBaseHigh
    (chain : ChainIndex) :
    ProbComp ((ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let materialBaseHigh ← fixedChainMaterialWithBaseHigh parameter chain
  let material := materialBaseHigh.1.1
  let tree ← treeValues parameter (unflattenSecret material.1.2)
    allTreeValueIndices material.2.2.2
  pure ((fixedChainTreeKeygenView parameter chain material tree,
    materialBaseHigh.1.2), materialBaseHigh.2)

structure ProgrammedActualKeygenCacheHighRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) : Prop where
  base : ProgrammedActualKeygenCacheRelation chain left right.1
  highEq : chainEdgeHighTableOfCache left.cache left.secretKey.parameter
      chain left.table = right.2

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_fixedChainTreeKeygen_withBaseHigh
    (chain : ChainIndex) :
    RelTriple
      (fixedChainTreeKeygen chain)
      (fixedChainTreeKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  unfold fixedChainTreeKeygen fixedChainTreeKeygenWithBaseHigh
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_fixedChainMaterialRepresentation_withBaseHigh_invariant
      leftParameter chain)
  intro leftMaterial rightMaterial hmaterial
  apply relTriple_bind
    (relTriple_fixedChainMaterial_allTreeValues_root_and_paths
      leftParameter chain leftMaterial rightMaterial.1 hmaterial.base)
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  refine ⟨⟨⟨hmaterial.base.tableEq, ?_, ?_, htree.2.2.2.2.1⟩,
    htree.2.2.2.2.2.1⟩, ?_⟩
  · exact congrArg (fun root => PublicKey.mk root leftParameter)
      htree.2.2.2.1
  · exact secretOutsideChain_eq_of_outsideChainSecret_eq chain
      leftMaterial.1.2 rightMaterial.1.1.1.2 hmaterial.base.outsideEq
  · calc
      chainEdgeHighTableOfCache leftTree.2 leftParameter chain
          (fixedChainMaterialTable chain leftMaterial) =
        chainEdgeHighTableOfCache leftMaterial.2.2.2 leftParameter chain
          (fixedChainMaterialTable chain leftMaterial) :=
            (chainEdgeHighTableOfCache_mono leftMaterial.2.2.2 leftTree.2
              leftParameter chain (fixedChainMaterialTable chain leftMaterial)
              hmaterial.base.leftMatches.2 htree.2.2.2.2.2.2.1).symm
      _ = rightMaterial.2 := hmaterial.highEq

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainTreeKeygenWithBaseHigh_eq_appendHigh
    (chain : ChainIndex) :
    evalDist (fixedChainTreeKeygenWithBaseHigh chain) =
    evalDist (do
      let keyViewBase ← fixedChainTreeKeygenWithBase chain
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (keyViewBase, high)) := by
  unfold fixedChainTreeKeygenWithBaseHigh fixedChainTreeKeygenWithBase
    fixedChainMaterialWithBaseHigh
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro materialBase
  let finish : (ChainEdgeIndex → Digest) →
      (List Digest × QueryCache HashSpec) →
      ProbComp ((ProgrammedFixedChainKeygenView ×
        (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) :=
    fun high tree => pure
      ((fixedChainTreeKeygenView parameter chain materialBase.1 tree,
        materialBase.2), high)
  simpa [finish, bind_assoc] using
    (OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ (ChainEdgeIndex → Digest))
      (treeValues parameter (unflattenSecret materialBase.1.1.2)
        allTreeValueIndices materialBase.1.2.2.2) finish)

noncomputable def programmedFixedChainKeygenWithBaseHigh
    (chain : ChainIndex) :
    ProbComp ((ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) := do
  let keyView ← programmedFixedChainKeygen chain
  let base ← uniformChainValueTable chain
  let high ← $ᵗ (ChainEdgeIndex → Digest)
  pure ((keyView, base), high)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_programmedFixedChainKeygen_withBaseHigh_cache
    (chain : ChainIndex) :
    RelTriple
      (programmedFixedChainKeygen chain)
      (programmedFixedChainKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_fixedChainTreeKeygen_eq_programmedFixed chain).symm
  let appendHigh := fun keyViewBase :
      ProgrammedFixedChainKeygenView × (ChainValueIndex → Digest) => do
    let high ← $ᵗ (ChainEdgeIndex → Digest)
    pure (keyViewBase, high)
  have hbaseProgrammed :
      evalDist (fixedChainTreeKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base)) =
      evalDist (programmedFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base)) := by
    rw [evalDist_bind, evalDist_fixedChainTreeKeygen_eq_programmedFixed,
      ← evalDist_bind]
  have hright : evalDist (fixedChainTreeKeygenWithBaseHigh chain) =
      evalDist (programmedFixedChainKeygenWithBaseHigh chain) := by
    calc
      _ = evalDist (fixedChainTreeKeygenWithBase chain >>= appendHigh) :=
        evalDist_fixedChainTreeKeygenWithBaseHigh_eq_appendHigh chain
      _ = evalDist ((fixedChainTreeKeygen chain >>= fun keyView =>
          uniformChainValueTable chain >>= fun base =>
          pure (keyView, base)) >>= appendHigh) := by
        rw [evalDist_bind,
          evalDist_fixedChainTreeKeygenWithBase_eq_independentBase,
          ← evalDist_bind]
      _ = evalDist ((programmedFixedChainKeygen chain >>= fun keyView =>
          uniformChainValueTable chain >>= fun base =>
          pure (keyView, base)) >>= appendHigh) := by
        rw [evalDist_bind, hbaseProgrammed, ← evalDist_bind]
      _ = _ := by
        simp [programmedFixedChainKeygenWithBaseHigh, appendHigh, bind_assoc]
  exact relTriple_of_evalDist_eq_right hright
    (relTriple_fixedChainTreeKeygen_withBaseHigh chain)

set_option maxRecDepth 100000 in
theorem relTriple_programmed_monitoredHashQueryWithHigh_until_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      (((randomOracle input).run leftCache) :
        ProbComp (HashOutput × QueryCache HashSpec))
      ((monitorCausalTrace right.1.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (filteredProbingAttackerHashQueryAtFromHigh
            (chainValueHighTableOfEdges right.2)
            right.1.1.secretKey selected input causalState
              (some (index, target)))).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  simpa only [hrel.highEq] using
    (relTriple_programmed_monitoredHashQueryFromHigh_until_hit
      selected left right.1 hrel.base hleftSupport hrightSupport
        leftCache rightState hstate input index target hprobe)

end XmssSecurity
