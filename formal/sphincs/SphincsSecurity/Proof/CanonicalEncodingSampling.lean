import SphincsSecurity.Proof.ReferenceEncodingTable

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalGraphMessage (labels : CanonicalGraphLabels) (position : EncodingPosition) : Digest :=
  truncateHash (labels (layerMessagePosition
    (referenceIndex position.lay position.tree position.leafIdx) position.lay))

theorem layerMessagePosition_treeBound (index : Index) (lay : Layer) :
    (layerMessagePosition index lay).TreeBound := by
  unfold layerMessagePosition
  split_ifs <;> norm_num [Position.TreeBound, layerHeight, middleLayer, bottomLayer, topLayer, numLayers,
    maxLayerHeight]

theorem canonicalGraphMessage_eq (key : SecretKey) (f : QueryImpl HashSpec Id) (position : EncodingPosition) :
    canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position =
      evalWithAnswerFn f (layerMessage key (referenceIndex position.lay position.tree position.leafIdx) position.lay) := by
  rw [canonicalGraphMessage, canonicalGraphLabels_eq_honest _ _ _ _ _ (layerMessagePosition_treeBound _ _),
    eval_layerMessage_eq_honestValue]
  rfl

theorem canonicalEncodingSearch_eq_graph_table (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    canonicalEncodingSearch key f position.lay position.tree position.leafIdx =
      encodingTableResult (referenceEncodingTable key.parameter f position
        (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position)
        encodingAttemptLimit 0) 0 := by
  rw [canonicalEncodingSearch, canonicalGraphMessage_eq, referenceEncodingSearch_eq_table]

abbrev EncodingRow := EncodingPosition × Fin encodingAttemptLimit
abbrev CanonicalEncodingRows := EncodingRow → HashOutput

noncomputable def canonicalEncodingRowInput (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : HashInput :=
  encodingRetryInput parameter row.1 (canonicalGraphMessage labels row.1) row.2.val

theorem canonicalEncodingRowInput_injective (parameter : PublicParameter) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingRowInput parameter labels) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) right from
      ⟨_, heq⟩)
  subst right
  have hcounter := encodingRetryInput_injective_of_lt first.isLt second.isLt heq
  exact Prod.ext rfl (Fin.ext hcounter)

attribute [local irreducible] canonicalEncodingInputs

theorem canonicalEncodingRowInput_mem (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : canonicalEncodingRowInput parameter labels row ∈ canonicalEncodingInputs parameter := by
  rw [canonicalEncodingInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨row.1, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(canonicalGraphMessage labels row.1, row.2), rfl⟩

noncomputable def canonicalEncodingCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) (row : EncodingRow) : inputs :=
  ⟨canonicalEncodingRowInput parameter labels row, hinputs (canonicalEncodingRowInput_mem parameter labels row)⟩

theorem canonicalEncodingCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingCell parameter inputs hinputs labels) := by
  intro left right heq
  exact canonicalEncodingRowInput_injective parameter labels (congrArg Subtype.val heq)

theorem canonicalEncodingCell_ne_graphCell (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (before after : CanonicalGraphLabels) (row : EncodingRow) (position : Position) :
    canonicalEncodingCell parameter inputs hencoding after row ≠
      canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position before := by
  intro heq
  have hbytes := congrArg Subtype.val heq
  have hencoding : AtEncodingPosition parameter (canonicalEncodingRowInput parameter after row) row.1 := ⟨_, rfl⟩
  exact hencoding.not_atPosition position ⟨_, hbytes⟩

noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable local instance : SampleableType CanonicalGraphLabels := SampleableType.ofFintype CanonicalGraphLabels
noncomputable local instance : SampleableType CanonicalEncodingRows := SampleableType.ofFintype CanonicalEncodingRows
noncomputable local instance : SampleableType (Fin encodingAttemptLimit → HashOutput) :=
  SampleableType.ofFintype (Fin encodingAttemptLimit → HashOutput)

noncomputable def readCanonicalEncodingRows (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) : CanonicalEncodingRows := fun row => f (canonicalEncodingRowInput parameter labels row)

theorem readCanonicalEncodingRows_finite (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (table : inputs → HashOutput) :
    readCanonicalEncodingRows parameter labels (finiteHashAnswer ∅ inputs table) =
      table ∘ canonicalEncodingCell parameter inputs hinputs labels := by
  funext row
  exact finiteHashAnswer_none ∅ inputs table _ (hinputs (canonicalEncodingRowInput_mem parameter labels row)) (by simp)

theorem evalDist_canonicalEncodingRows_uniform (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    𝒟[do
      let table ← sampleHashTable inputs
      pure (readCanonicalEncodingRows parameter labels (finiteHashAnswer ∅ inputs table))] =
        𝒟[($ᵗ CanonicalEncodingRows : ProbComp _)] := by
  simp only [readCanonicalEncodingRows_finite parameter inputs hinputs]
  exact evalDist_uniformSample_map_comp_injective (canonicalEncodingCell_injective parameter inputs hinputs labels)

theorem evalDist_canonicalGraph_encodingRows_uniform (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs parameter ⊆ inputs) (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :
    𝒟[do
      let table ← sampleHashTable inputs
      let f := finiteHashAnswer ∅ inputs table
      let labels := canonicalGraphLabels parameter otsSecret ftsSecret f
      pure (labels, readCanonicalEncodingRows parameter labels f)] =
        𝒟[do
          let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
          let rows ← ($ᵗ CanonicalEncodingRows : ProbComp _)
          pure (labels, rows)] := by
  rw [evalDist_canonicalGraph_bind_eq_plant parameter otsSecret ftsSecret inputs hgraph
    (fun labels table => pure (labels, readCanonicalEncodingRows parameter labels (finiteHashAnswer ∅ inputs table)))]
  simp only [readCanonicalEncodingRows_finite parameter inputs hencoding]
  rw [plantCanonicalGraph]
  rw [FiniteGraphSampling.evalDist_plant_read
    (canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph)
    (fun position output values => Function.update values position output) canonicalGraphOrder (fun _ => 0)
    (fun labels table => table ∘ canonicalEncodingCell parameter inputs hencoding labels) (by
      intro position before after table answer
      funext row
      exact Function.update_of_ne
        (canonicalEncodingCell_ne_graphCell parameter otsSecret ftsSecret inputs hencoding hgraph before after row position)
        answer table) (fun labels rows => pure (labels, rows))]
  rw [evalDist_bind, FiniteGraphSampling.evalDist_draw_coordinates canonicalGraphOrder canonicalGraphOrder_nodup
    mem_canonicalGraphOrder (fun _ => 0), ← evalDist_bind]
  apply evalDist_bind_congr_left
  intro labels
  have h := evalDist_uniformSample_map_comp_injective (R := HashOutput)
    (canonicalEncodingCell_injective parameter inputs hencoding labels)
  have hnext := congrArg (fun distribution : SPMF CanonicalEncodingRows =>
    distribution >>= fun rows => pure (labels, rows)) h
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using hnext

def canonicalEncodingResults (rows : CanonicalEncodingRows) : EncodingPosition → Option (Counter × Encoding) × Nat :=
  fun position => encodingTableResult (fun counter => rows (position, counter)) 0

theorem canonicalEncodingResults_eq (key : SecretKey) (f : QueryImpl HashSpec Id) :
    canonicalEncodingResults (readCanonicalEncodingRows key.parameter
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) f) =
        fun position => canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  funext position
  rw [canonicalEncodingSearch_eq_graph_table]
  apply congrArg (fun table => encodingTableResult table 0)
  funext counter
  simp only [readCanonicalEncodingRows, canonicalEncodingRowInput, referenceEncodingTable]
  rw [Nat.zero_add]

theorem evalDist_canonicalEncodingSearches_independent (key : SecretKey) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) :
    𝒟[do
      let table ← sampleHashTable inputs
      let f := finiteHashAnswer ∅ inputs table
      pure (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f,
        fun position : EncodingPosition => canonicalEncodingSearch key f position.lay position.tree position.leafIdx)] =
        𝒟[do
          let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
          let rows ← ($ᵗ CanonicalEncodingRows : ProbComp _)
          pure (labels, canonicalEncodingResults rows)] := by
  have h := congrArg (fun distribution : SPMF (CanonicalGraphLabels × CanonicalEncodingRows) =>
    distribution >>= fun result => pure (result.1, canonicalEncodingResults result.2))
    (evalDist_canonicalGraph_encodingRows_uniform key.parameter key.otsSecret key.ftsSecret inputs hgraph hencoding)
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind, canonicalEncodingResults_eq] using h

theorem evalDist_canonicalEncodingSearch_uniform (key : SecretKey) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    𝒟[do
      let table ← sampleHashTable inputs
      pure (canonicalEncodingSearch key (finiteHashAnswer ∅ inputs table) position.lay position.tree position.leafIdx)] =
        𝒟[do
          let table ← ($ᵗ (Fin encodingAttemptLimit → HashOutput) : ProbComp _)
          pure (encodingTableResult table 0)] := by
  have h := congrArg (fun distribution : SPMF
      (CanonicalGraphLabels × (EncodingPosition → Option (Counter × Encoding) × Nat)) =>
    distribution >>= fun result => pure (result.2 position))
    (evalDist_canonicalEncodingSearches_independent key inputs hgraph hencoding)
  have hfirst :
      𝒟[do
        let table ← sampleHashTable inputs
        pure (canonicalEncodingSearch key (finiteHashAnswer ∅ inputs table) position.lay position.tree position.leafIdx)] =
          𝒟[do
            let _labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
            let rows ← ($ᵗ CanonicalEncodingRows : ProbComp _)
            pure (canonicalEncodingResults rows position)] := by
    simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h
  rw [hfirst, evalDist_bind_const_neverFails _ (by simp)]
  have hrows := evalDist_uniformSample_map_comp_injective (R := HashOutput)
    (e := fun index : Fin encodingAttemptLimit => (position, index)) (by
      intro left right heq
      exact congrArg Prod.snd heq)
  have hnext := congrArg (fun distribution : SPMF (Fin encodingAttemptLimit → HashOutput) =>
    distribution >>= fun table => pure (encodingTableResult table 0)) hrows
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind, canonicalEncodingResults,
    Function.comp_def] using hnext

theorem evalDist_canonicalEncodingSearch_pmf (key : SecretKey) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    𝒟[do
      let table ← sampleHashTable inputs
      pure (canonicalEncodingSearch key (finiteHashAnswer ∅ inputs table) position.lay position.tree position.leafIdx)] =
        𝒟[(FirstSuccessTable.full (Answer := HashOutput) encodingAttemptLimit).map
          (fun table => encodingTableResult table 0)] := by
  rw [evalDist_canonicalEncodingSearch_uniform key inputs hgraph hencoding position,
    bind_pure_comp, evalDist_map, evalDist_uniformSample, FirstSuccessTable.full_eq_uniform]
  rw [← PMF.monad_map_eq_map, evalDist_map]

theorem probOutput_canonicalEncodingSearch_success (key : SecretKey) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) (index : Fin encodingAttemptLimit) (digest : Digest) (word : Encoding)
    (hdecode : TargetSum.decodeDigest digest = some word) :
    Pr[= (some (BitVec.ofNat counterBits index.val, word), index.val + 1) | do
      let table ← sampleHashTable inputs
      pure (canonicalEncodingSearch key (finiteHashAnswer ∅ inputs table) position.lay position.tree position.leafIdx)] =
        encodingInvalidRate ^ index.val * (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := _root_.evalDist_ext_iff.mp (evalDist_canonicalEncodingSearch_pmf key inputs hgraph hencoding position)
    (some (BitVec.ofNat counterBits index.val, word), index.val + 1)
  rw [← PMF.monad_map_eq_map, probOutput_map] at h
  exact h.trans (by simpa only [Nat.zero_add] using probEvent_encodingTableResult_success 0 index digest word hdecode)

theorem probOutput_canonicalEncodingSearch_exhaustion (key : SecretKey) (inputs : Finset HashInput)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    Pr[= (none, encodingAttemptLimit) | do
      let table ← sampleHashTable inputs
      pure (canonicalEncodingSearch key (finiteHashAnswer ∅ inputs table) position.lay position.tree position.leafIdx)] =
        encodingInvalidRate ^ encodingAttemptLimit := by
  have h := _root_.evalDist_ext_iff.mp (evalDist_canonicalEncodingSearch_pmf key inputs hgraph hencoding position)
    (none, encodingAttemptLimit)
  rw [← PMF.monad_map_eq_map, probOutput_map] at h
  exact h.trans (probEvent_encodingTableResult_exhaustion encodingAttemptLimit 0)

end SphincsSecurity.Concrete
