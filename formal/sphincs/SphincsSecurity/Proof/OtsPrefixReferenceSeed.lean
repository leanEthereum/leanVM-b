import SphincsSecurity.Proof.OtsPrefixRawSampling

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

namespace OtsPrefix

structure ReferenceAuxSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) where
  high : segment.Query → High
  remaining : segment.RemainingRows inputs hencoding hgraph
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs segment.parameter → HashOutput

noncomputable def referenceAuxSeedLaw (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (segment.ReferenceAuxSeed inputs hencoding hgraph) :=
  (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
    (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).bind (fun remaining =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
        (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs segment.parameter → HashOutput)).map
          (fun encoding => ⟨high, remaining, selectedRows, encoding⟩))))

noncomputable def referenceSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily)
    (tables : Fin segment.digit.val → Digest → Digest) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) :
    ReferenceFamilySeed segment.parameter inputs hencoding :=
  ⟨selections, segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining,
    auxiliary.selectedRows, auxiliary.encoding⟩

theorem referenceFamilySeedLawAt_eq_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    referenceFamilySeedLawAt segment.parameter inputs hencoding selections =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map
          (segment.referenceSeed inputs hencoding hgraph selections tables)) := by
  rw [referenceFamilySeedLawAt, segment.uniform_nonencoding inputs hencoding hgraph]
  simp only [PMF.bind_bind, PMF.bind_map, referenceAuxSeedLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

end OtsPrefix

theorem referenceFamilyOracleSample_eq_prefixSeed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : ReferenceFamily → Digit) :
    referenceFamilyOracleSample key inputs hencoding =
      (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
        let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩
        (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
          (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map (fun auxiliary =>
            (selections, referenceFamilySeedTable key inputs hencoding
              (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))))) := by
  rw [referenceFamilyOracleSample_eq_seed, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [OtsPrefix.referenceFamilySeedLawAt_eq_prefix
    ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩ inputs hencoding hgraph selections]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, OtsPrefix.referenceSeed]

theorem referenceFamilyPrefixSeed_rows (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit)
    (selections : ReferenceFamily) (tables : Fin digit.val → Digest → Digest)
    (auxiliary : (⟨key.parameter, lay, tree, leaf, chainIdx, digit⟩ : OtsPrefix).ReferenceAuxSeed inputs hencoding hgraph) :
    let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, digit⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    (segment.lows oracle, segment.highs oracle) = (tables, auxiliary.high) := by
  let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, digit⟩
  let seed := segment.referenceSeed inputs hencoding hgraph selections tables auxiliary
  let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding seed)
  have hquery (query : segment.Query) : oracle (segment.input query) =
      OtsPrefix.combine (tables query.1 query.2) (auxiliary.high query) := by
    exact (referenceFamilySeedTable_answer_nonencoding key inputs hencoding seed
      (segment.nonencodingCell inputs hencoding hgraph query)).trans
      (segment.joinNonencoding_prefix inputs hencoding hgraph tables auxiliary.high auxiliary.remaining query)
  change (segment.lows oracle, segment.highs oracle) = (tables, auxiliary.high)
  apply Prod.ext
  · funext level input
    exact congrArg truncateHash (hquery (level, input)) |>.trans (OtsPrefix.truncate_combine _ _)
  · funext query
    exact congrArg (fun output => (splitHashOutput digestBits output).2) (hquery query) |>.trans
      (congrArg Prod.snd (OtsPrefix.split_combine _ _))

end SphincsSecurity.Concrete
