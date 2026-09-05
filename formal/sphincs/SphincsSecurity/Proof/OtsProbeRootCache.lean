import SphincsSecurity.Proof.OtsProbeEncodingPrehitViewed

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def RootValuesCached (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (cache : QueryCache HashSpec) : Prop :=
  ∀ lay tree output, context.positionValue (layerRootPosition lay tree) = some output →
    CachedRun cache (fromCache cache)
      (treeRoot parameter lay tree (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) ∧
    evalWithAnswerFn (fromCache cache)
      (treeRoot parameter lay tree (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) =
        truncateHash output

theorem resolvedPositionComputation_layerRootPosition (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    resolvedPositionComputation parameter table (layerRootPosition lay tree) =
      treeRoot parameter lay tree (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) := by
  have hheight : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  simp [resolvedPositionComputation, layerRootPosition, treeRoot, Nat.sub_add_cancel hheight]

theorem resolvableOtsPosition_layerRootPosition (lay : Layer) (tree : TreeIndex) :
    ResolvableOtsPosition (layerRootPosition lay tree) := by
  have hheight : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  simp only [layerRootPosition, ResolvableOtsPosition, Fin.val_zero, zero_add, mul_one,
    Nat.sub_add_cancel hheight]
  exact Nat.pow_le_pow_right (by omega) (layerHeight_le lay)

theorem VisibleResolvedComputationsCached.root_value_cached
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : context.state.values (.position (layerRootPosition lay tree)) = some output) :
    CachedRun cache (fromCache cache)
      (treeRoot parameter lay tree (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) ∧
    evalWithAnswerFn (fromCache cache)
      (treeRoot parameter lay tree (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) =
        truncateHash output := by
  simpa only [resolvedPositionComputation_layerRootPosition] using
    hclosed (layerRootPosition lay tree) output (resolvableOtsPosition_layerRootPosition lay tree) hvalue

theorem RootValuesCached.mono
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {initialCache finalCache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context initialCache) (hle : initialCache ≤ finalCache) :
    RootValuesCached parameter table context finalCache := by
  intro lay tree output hvalue
  obtain ⟨hcached, houtput⟩ := hclosed lay tree output hvalue
  refine ⟨(hcached.changeAnswerFn (agreesWithFn_fromCache initialCache)
    (agreesWithFn_fromCache_of_le hle)).mono hle, ?_⟩
  exact (hcached.eval_eq (agreesWithFn_fromCache initialCache)
    (agreesWithFn_fromCache_of_le hle)).symm.trans houtput

theorem RootValuesCached.canonicalize
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context cache) (hconsistent : context.ValuesConsistent) :
    RootValuesCached parameter table (canonicalizeMaterializedValues table context) cache := by
  intro lay tree output hvalue
  rw [canonicalizeMaterializedValues_positionValue table context hconsistent] at hvalue
  exact hclosed lay tree output hvalue

theorem RootValuesCached.of_materialized_or_previous
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {before after : DeferredContext} {initialCache finalCache : QueryCache HashSpec}
    (hbefore : RootValuesCached parameter table before initialCache) (hle : initialCache ≤ finalCache)
    (hvisible : VisibleResolvedComputationsCached parameter table after finalCache)
    (hvalues : ∀ lay tree output, after.positionValue (layerRootPosition lay tree) = some output →
      before.positionValue (layerRootPosition lay tree) = some output ∨
        after.state.values (.position (layerRootPosition lay tree)) = some output) :
    RootValuesCached parameter table after finalCache := by
  intro lay tree output hvalue
  rcases hvalues lay tree output hvalue with hold | hnew
  · exact hbefore.mono hle lay tree output hold
  · exact hvisible.root_value_cached lay tree output hnew

theorem RootValuesCached.settled_value
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table context cache)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (position : Position)
    (hroot : IsLayerRoot position) (output : HashOutput)
    (hvalue : context.positionValue position = some output) :
    Settled parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      ftsSecret cache position ∧
    honestValue (fromCache cache) parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret position =
        truncateHash output := by
  obtain ⟨lay, tree, rfl⟩ := hroot
  obtain ⟨hcached, houtput⟩ := hclosed lay tree output hvalue
  constructor
  · exact settled_treeRoot_of_cachedRun (ftsSecret := ftsSecret) (agreesWithFn_fromCache cache) lay tree hcached
  · have hheight : 0 < layerHeight lay := by
      unfold layerHeight
      split <;> norm_num [maxLayerHeight]
    simpa only [layerRootPosition, honestValue_node, honestNode, treeRoot,
      Fin.val_zero, Nat.sub_add_cancel hheight] using houtput

set_option maxRecDepth 100000 in
theorem RootValuesCached.refinedReserve_of_encoding_candidate
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached secretKey.parameter table context cache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hvalue : context.positionValue target = some output) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  obtain ⟨rootPosition, hcoordinate, hroot⟩ := encodingLayerRootCandidateAt_isLayerRoot hcandidate
  have heq : rootPosition = target := Coordinate.position.inj (hcoordinate.symm.trans hposition)
  subst rootPosition
  have hsettled := (hclosed.settled_value secretKey.ftsSecret target hroot output hvalue).1
  rw [← hsecrets] at hsettled
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  exact otsOpeningRefinedQueryReserve_ge_four_thirds_of_encodingMessageSettled secretKey cache input position hat
    ⟨index, htree, hleaf, hsettled⟩

set_option maxRecDepth 100000 in
theorem RootValuesCached.encoding_weightedCharge_le_refinedReserve
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {actualCache : QueryCache HashSpec}
    (hclosed : RootValuesCached secretKey.parameter table context actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hvalue : context.positionValue target = some output)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan secretKey.parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? secretKey.parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input :=
  (probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds
    secretKey.parameter input publicState plan cache context fuel).trans
      (hclosed.refinedReserve_of_encoding_candidate hsecrets hcandidate hposition hvalue)

end SphincsSecurity.Concrete.OtsProbeSimulation
