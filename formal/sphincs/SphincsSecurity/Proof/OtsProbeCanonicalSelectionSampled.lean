import SphincsSecurity.Proof.OtsProbeCanonicalSelectionCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def canonicalQuerySelectionAfterTable
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    ProbComp (Option CanonicalQuerySelection) := do
  let result ← runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match result with
  | none => pure none
  | some result =>
      canonicalQuerySelection parameter result.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        ordinal result.context result.remaining table result.value.2

theorem tsum_canonicalQuerySelectionAfterTable_charge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' ordinal, ∑' selection,
      Pr[= selection | canonicalQuerySelectionAfterTable adversary parameter table ftsSecret fuel ordinal] *
        CanonicalQuerySelection.charge (canonicalJointOuterCharge parameter) selection) =
      canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel := by
  unfold canonicalQuerySelectionAfterTable canonicalJointChargeAfterTable
  simp only [tsum_probOutput_bind_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro result
  rw [ENNReal.tsum_mul_left]
  congr 1
  cases result with
  | none => simp only [tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]
  | some result =>
      exact tsum_canonicalQuerySelection_charge parameter result.value.1 ftsSecret
        (canonicalJointOuterCharge parameter) _ result.context result.remaining table result.value.2


noncomputable def actualQuerySelectionAfterSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (ordinal : Nat) :
    ProbComp (Option ActualQuerySelection) := do
  let result ← (simulateQ (randomOracle : QueryImpl HashSpec _)
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅
  actualQuerySelection (⟨parameter, result.1, otsSecret, ftsSecret⟩ : SecretKey)
    (retainedGameRestComputation adversary ⟨result.1, parameter⟩) ordinal result.2

set_option maxRecDepth 100000 in
theorem relTriple_canonicalQuerySelectionAfterTable_actual
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    RelTriple (canonicalQuerySelectionAfterTable adversary parameter table ftsSecret fuel ordinal)
      (actualQuerySelectionAfterSecrets adversary parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret ordinal)
      (CanonicalQuerySelectionRel parameter table) := by
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact deferredComputationsClosed_empty.of_mem_runResolved _ _ fuel table result hleft)
  unfold canonicalQuerySelectionAfterTable actualQuerySelectionAfterSecrets
  apply relTriple_bind (by simpa only [treeRoot] using hsupported)
  intro left right hrelation
  cases left with
  | none => exact relTriple_none_actualQuerySelection parameter table _
  | some result =>
      dsimp only
      rcases hrelation.1 with hclean | hdoomed
      · rw [← hclean.2.1]
        exact relTriple_canonicalQuerySelection_actualQuerySelection parameter result.value.1 table ftsSecret
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
          ordinal result.context result.remaining result.value.2 right.2
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 (hrelation.2 result rfl)
      · rw [canonicalQuerySelection_eq_none_of_not_completable parameter result.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
          ordinal result.context result.remaining table result.value.2 hdoomed.2.2.2]
        exact relTriple_none_actualQuerySelection parameter table _

noncomputable def sampledCanonicalQuerySelection (adversary : Adversary) (fuel ordinal : Nat) :
    ProbComp (PublicParameter × Option CanonicalQuerySelection) := do
  let parameter ← sampleParameter
  let table ← sampleOtsHashTable
  let ftsSecret ← sampleFtsSecrets
  (fun selection => (parameter, selection)) <$>
    canonicalQuerySelectionAfterTable adversary parameter table ftsSecret fuel ordinal

theorem tsum_sampledCanonicalQuerySelection_charge
    (adversary : Adversary) (fuel : Nat) :
    (∑' ordinal, ∑' result, Pr[= result | sampledCanonicalQuerySelection adversary fuel ordinal] *
      CanonicalQuerySelection.charge (canonicalJointOuterCharge result.1) result.2) =
      sampledCanonicalJointCharge adversary fuel := by
  unfold sampledCanonicalQuerySelection sampledCanonicalJointCharge
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro parameter
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro table
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro ftsSecret
  rw [ENNReal.tsum_mul_left, tsum_canonicalQuerySelectionAfterTable_charge]

theorem tsum_sampledCanonicalQuerySelection_charge_le_refinedReserve
    (adversary : Adversary) (fuel : Nat) :
    (∑' ordinal, ∑' result, Pr[= result | sampledCanonicalQuerySelection adversary fuel ordinal] *
      CanonicalQuerySelection.charge (canonicalJointOuterCharge result.1) result.2) ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  rw [tsum_sampledCanonicalQuerySelection_charge]
  exact sampledCanonicalJointCharge_le_refinedReserve adversary fuel


noncomputable def sampledActualQuerySelection (adversary : Adversary) (ordinal : Nat) :
    ProbComp (SampledSecrets × Option ActualQuerySelection) := do
  let secrets ← sampleSecrets
  (fun selection => (secrets, selection)) <$>
    actualQuerySelectionAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret ordinal

def SampledCanonicalQuerySelectionRel
    (left : PublicParameter × Option CanonicalQuerySelection)
    (right : SampledSecrets × Option ActualQuerySelection) : Prop :=
  left.1 = right.1.parameter ∧ ∃ table : OtsSecretIndex → HashOutput,
    right.1.otsSecret = (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ∧
      CanonicalQuerySelectionRel left.1 table left.2 right.2

set_option maxRecDepth 100000 in
theorem relTriple_sampledCanonicalQuerySelection_actual
    (adversary : Adversary) (fuel ordinal : Nat) :
    RelTriple (sampledCanonicalQuerySelection adversary fuel ordinal)
      (sampledActualQuerySelection adversary ordinal) SampledCanonicalQuerySelectionRel := by
  unfold sampledCanonicalQuerySelection sampledActualQuerySelection
  simp only [sampleSecrets, bind_assoc, pure_bind]
  apply relTriple_bind (relTriple_refl sampleParameter)
  intro parameter other hparameter
  subst other
  apply relTriple_bind (by
    simpa only [sampleOtsHashTable] using relTriple_uniformOtsHashTable_sampleOtsSecrets)
  intro table otsSecret hsecrets
  have hots : otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) :=
    hsecrets.symm
  rw [hots]
  apply relTriple_bind (relTriple_refl sampleFtsSecrets)
  intro ftsSecret other hfts
  subst other
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_canonicalQuerySelectionAfterTable_actual adversary parameter table ftsSecret fuel ordinal)
  intro left right hrelation
  exact ⟨rfl, table, rfl, hrelation⟩


set_option maxRecDepth 100000 in
theorem SampledCanonicalQuerySelectionRel.root_settled_value
    {parameter : PublicParameter} {selection : CanonicalQuerySelection}
    {secrets : SampledSecrets} {actual : ActualQuerySelection}
    (hrelation : SampledCanonicalQuerySelectionRel (parameter, some selection) (secrets, some actual))
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : selection.context.positionValue (layerRootPosition lay tree) = some output) :
    Settled secrets.parameter secrets.otsSecret secrets.ftsSecret actual.cache (layerRootPosition lay tree) ∧
      honestValue (fromCache actual.cache) secrets.parameter secrets.otsSecret secrets.ftsSecret
        (layerRootPosition lay tree) = truncateHash output := by
  obtain ⟨hparameter, table, hsecrets, hselected⟩ := hrelation
  obtain ⟨_hinput, _htable, hinvariant, _hvisible, _hpublished, hcomputed⟩ := hselected
  have hroot := hcomputed.root_settled_value hinvariant secrets.ftsSecret lay tree output hvalue
  dsimp only at hparameter hsecrets
  rw [← hparameter, hsecrets]
  exact hroot

end SphincsSecurity.Concrete.OtsProbeSimulation
