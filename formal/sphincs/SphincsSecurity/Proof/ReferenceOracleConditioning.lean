import SphincsSecurity.Proof.EncodingOracleSplit

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

abbrev ReferenceSelection := Option (Fin encodingAttemptLimit × Encoding)

noncomputable def referenceTableSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) : ReferenceSelection :=
  FirstSuccessTable.select decodeEncodingOutput (fun counter =>
    readCanonicalEncodingRows key.parameter (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      f (position, counter))

def referenceSelectionResult (selection : ReferenceSelection) : Option (Counter × Encoding) × Nat :=
  (selection.map (fun result => (BitVec.ofNat counterBits result.1.val, result.2)),
    selection.elim encodingAttemptLimit (fun result => result.1.val + 1))

theorem referenceSelectionResult_eq_search (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    referenceSelectionResult (referenceTableSelection key f position) =
      canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  rw [← congrFun (canonicalEncodingResults_eq key f) position]
  simp only [canonicalEncodingResults, referenceSelectionResult, referenceTableSelection, encodingTableResult, Nat.zero_add]

theorem referenceTableSelection_joinEncodingTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      position = FirstSuccessTable.select decodeEncodingOutput
        (encoding ∘ referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) := by
  rw [referenceTableSelection, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  change finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    (encodingRetryInput key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter.val) = _
  rw [finiteHashAnswer_none ∅ inputs _ _
    (hencoding (encodingRetryInput_mem_canonicalEncodingInputs _ _ _ counter)) (by simp)]
  exact UniformTableSplit.join_embed _ _ encoding outside
    (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter)

theorem referenceTableSelection_referenceOracleTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (position : EncodingPosition)
    (rows : Fin encodingAttemptLimit → HashOutput)
    (remaining : UniformTableSplit.Outside
      (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) → HashOutput) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (referenceOracleTable key inputs hencoding outside position rows remaining))
      position = FirstSuccessTable.select decodeEncodingOutput rows := by
  rw [referenceOracleTable, referenceTableSelection_joinEncodingTable key inputs hencoding hgraph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  exact UniformTableSplit.join_embed _ _ rows remaining counter

theorem uniform_bind_reference {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) (next : ReferenceSelection → (inputs → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (inputs → HashOutput)).bind
        (fun table => next (referenceTableSelection key (finiteHashAnswer ∅ inputs table) position) table) =
      (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
        (FirstSuccessTable.selected decodeEncodingOutput encodingAttemptLimit).bind (fun result =>
          (FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty result).bind
            (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
              (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) → HashOutput)).bind
                (fun remaining => next result (referenceOracleTable key inputs hencoding outside position rows remaining))))) := by
  rw [UniformTableSplit.uniform_bind_split (encodingInputCell key.parameter inputs hencoding)
    (encodingInputCell_injective key.parameter inputs hencoding), PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext outside
  change ((PMF.uniformOfFintype (canonicalEncodingInputs key.parameter → HashOutput)).bind
    (fun encoding => next (referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) position)
      (joinEncodingTable key.parameter inputs hencoding encoding outside))) = _
  simp only [referenceTableSelection_joinEncodingTable key inputs hencoding hgraph]
  have h := UniformTableSplit.uniform_bind_firstSuccess
    (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position))
    (referenceCounterCell_injective key.parameter position (outsideGraphMessage key inputs hencoding outside position))
    decodeEncodingOutput decodeEncodingOutput_invalid_nonempty
    (fun result encoding => next result (joinEncodingTable key.parameter inputs hencoding encoding outside))
  exact h

noncomputable def referenceOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (position : EncodingPosition) :
    PMF (ReferenceSelection × (inputs → HashOutput)) :=
  (FirstSuccessTable.selected decodeEncodingOutput encodingAttemptLimit).bind (fun result =>
    (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
      (FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty result).bind
        (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
          (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) → HashOutput)).map
            (fun remaining => (result, referenceOracleTable key inputs hencoding outside position rows remaining)))))

theorem referenceOracleSample_nonencoding (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (position : EncodingPosition) :
    (referenceOracleSample key inputs hencoding position).map (fun result =>
      (result.1, fun cell : UniformTableSplit.Outside (encodingInputCell key.parameter inputs hencoding) =>
        result.2 cell.val)) =
      (FirstSuccessTable.selected decodeEncodingOutput encodingAttemptLimit).bind (fun result =>
        (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).map (fun outside => (result, outside))) := by
  rw [referenceOracleSample, PMF.map_bind]
  apply congrArg (FirstSuccessTable.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext result
  rw [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext outside
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, referenceOracleTable_nonencoding,
    PMF.bind_const]
  exact PMF.map_const _ _

theorem uniform_joint_eq_referenceOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun table => (referenceTableSelection key (finiteHashAnswer ∅ inputs table) position, table)) =
      referenceOracleSample key inputs hencoding position := by
  have h := uniform_bind_reference key inputs hencoding hgraph position (fun result table => PMF.pure (result, table))
  rw [PMF.bind_comm] at h
  exact h

theorem referenceOracleSample_table (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    (referenceOracleSample key inputs hencoding position).map Prod.snd = PMF.uniformOfFintype (inputs → HashOutput) := by
  rw [← uniform_joint_eq_referenceOracleSample key inputs hencoding hgraph position, PMF.map_comp]
  exact PMF.map_id _

theorem referenceOracleSample_selection (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) (result : ReferenceSelection × (inputs → HashOutput))
    (hresult : result ∈ (referenceOracleSample key inputs hencoding position).support) :
    result.1 = referenceTableSelection key (finiteHashAnswer ∅ inputs result.2) position := by
  rw [← uniform_joint_eq_referenceOracleSample key inputs hencoding hgraph position, PMF.mem_support_map_iff] at hresult
  obtain ⟨table, _, rfl⟩ := hresult
  rfl

theorem referenceOracleSample_search (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) (result : ReferenceSelection × (inputs → HashOutput))
    (hresult : result ∈ (referenceOracleSample key inputs hencoding position).support) :
    referenceSelectionResult result.1 =
      canonicalEncodingSearch key (finiteHashAnswer ∅ inputs result.2) position.lay position.tree position.leafIdx := by
  rw [referenceOracleSample_selection key inputs hencoding hgraph position result hresult,
    referenceSelectionResult_eq_search]

noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

theorem evalDist_referenceOracleSample_table (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) :
    𝒟[(referenceOracleSample key inputs hencoding position).map Prod.snd] = 𝒟[sampleHashTable inputs] := by
  rw [referenceOracleSample_table key inputs hencoding hgraph position, sampleHashTable, evalDist_uniformSample]

theorem referenceOracleSample_bind {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (position : EncodingPosition) (next : (inputs → HashOutput) → ProbComp Result) :
    (𝒟[referenceOracleSample key inputs hencoding position] >>= fun result => 𝒟[next result.2]) =
      𝒟[do let table ← sampleHashTable inputs; next table] := by
  have h := congrArg (fun distribution : SPMF (inputs → HashOutput) => distribution >>= fun table => 𝒟[next table])
    (evalDist_referenceOracleSample_table key inputs hencoding hgraph position)
  simpa only [← PMF.monad_map_eq_map, evalDist_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    evalDist_bind, Function.comp_apply, evalDist_pure] using h

end SphincsSecurity.Concrete
