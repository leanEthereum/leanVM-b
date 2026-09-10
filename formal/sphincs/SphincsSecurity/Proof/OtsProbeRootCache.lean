import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsOpeningRefinedReserve
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate
import SphincsSecurity.Proof.OtsProbeResolvedSampling

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

theorem resolvableOtsPosition_layerRootPosition (lay : Layer) (tree : TreeIndex) :
    ResolvableOtsPosition (layerRootPosition lay tree) := by
  have hheight : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  simp only [layerRootPosition, ResolvableOtsPosition, Fin.val_zero, zero_add, mul_one,
    Nat.sub_add_cancel hheight]
  exact Nat.pow_le_pow_right (by omega) (layerHeight_le lay)

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

end SphincsSecurity.Concrete.OtsProbeSimulation
