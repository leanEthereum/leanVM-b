import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsOpeningRefinedReserve
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

inductive DeferredPositionComputed (context : DeferredContext) : Position → Prop where
  | intro (position : Position) (hots : IsOtsPosition position) (hvalid : position.Valid)
      (hknown : ∃ output, context.positionValue position = some output)
      (hchildren : ∀ child ∈ position.children, DeferredPositionComputed context child) :
      DeferredPositionComputed context position

theorem DeferredPositionComputed.mono
    {before after : DeferredContext} {position : Position}
    (hcomputed : DeferredPositionComputed before position)
    (hvalues : ∀ position output, before.positionValue position = some output →
      after.positionValue position = some output) :
    DeferredPositionComputed after position := by
  induction hcomputed with
  | intro position hots hvalid hknown hchildren ih =>
      obtain ⟨output, houtput⟩ := hknown
      exact .intro position hots hvalid ⟨output, hvalues position output houtput⟩ ih

theorem DeferredPositionComputed.of_positionValue_eq
    {before after : DeferredContext} {position : Position}
    (hcomputed : DeferredPositionComputed before position)
    (hvalues : ∀ position, after.positionValue position = before.positionValue position) :
    DeferredPositionComputed after position :=
  hcomputed.mono (fun position _ hvalue => (hvalues position).trans hvalue)

theorem honestInput_eq_tableInput_of_children
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (completion : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (position : Position) (hots : IsOtsPosition position) (hvalid : position.Valid)
    (hchildren : ∀ child ∈ position.children,
      honestValue f parameter (tableOtsSecret completion) ftsSecret child = tableValue completion child) :
    honestInput f parameter (tableOtsSecret completion) ftsSecret position =
      tableInput parameter completion (.position position) := by
  have hmap : childValues f parameter (tableOtsSecret completion) ftsSecret position =
      position.children.map (tableValue completion) := List.map_congr_left hchildren
  unfold honestInput
  rw [honestPayload_eq_slots f parameter (tableOtsSecret completion) ftsSecret hvalid]
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simp only [tableInput, slots, tablePayload]
      split_ifs <;> simp_all [tableOtsSecret]
  | leaf lay tree leafIdx =>
      simpa only [slots, tableInput, tablePayload] using congrArg
        (fun values : List Digest => tweakableHashInput parameter
          (Position.leaf lay tree leafIdx).domain (values.flatMap digestBytes)) hmap
  | node lay tree level nodeIdx =>
      simpa only [slots, tableInput, tablePayload] using congrArg
        (fun values : List Digest => tweakableHashInput parameter
          (Position.node lay tree level nodeIdx).domain (values.flatMap digestBytes)) hmap
  | ftsLeaf | ftsNode | ftsRoots => contradiction

set_option maxRecDepth 100000 in
theorem DeferredPositionComputed.settled_value
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hcache : ChronologicalCacheAgrees parameter table context cache)
    (completion : Coordinate → HashOutput) (hcompletion : DeferredCompletion table context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {position : Position} (hcomputed : DeferredPositionComputed context position) :
    Settled parameter (tableOtsSecret completion) ftsSecret cache position ∧
      honestValue (fromCache cache) parameter (tableOtsSecret completion) ftsSecret position =
        tableValue completion position := by
  induction hcomputed with
  | intro position hots hvalid hknown hchildren ih =>
      obtain ⟨output, houtput⟩ := hknown
      have hinput := honestInput_eq_tableInput_of_children (fromCache cache) parameter completion
        ftsSecret position hots hvalid (fun child hchild => (ih child hchild).2)
      have hquery := hcache completion hcompletion position hots
      simp only [ResolveInputAgrees, houtput] at hquery
      have hanswer : fromCache cache (tableInput parameter completion (.position position)) = output := by
        simp [fromCache, hquery]
      constructor
      · rw [settled_iff]
        refine ⟨hvalid, ?_, fun child hchild => (ih child hchild).1⟩
        change cache (honestInput (fromCache cache) parameter (tableOtsSecret completion) ftsSecret position) ≠ none
        rw [hinput, hquery]
        simp
      · rw [honestValue, hinput, hanswer, tableValue, hcompletion.eq_positionValue position output houtput]

set_option maxRecDepth 100000 in
theorem DeferredPositionComputed.refinedReserve_of_encoding_candidate
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hcache : ChronologicalCacheAgrees secretKey.parameter table context cache)
    (completion : Coordinate → HashOutput) (hcompletion : DeferredCompletion table context completion)
    (hsecrets : secretKey.otsSecret = tableOtsSecret completion)
    {input : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hcomputed : DeferredPositionComputed context target) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  have hsettled := (hcomputed.settled_value hcache completion hcompletion secretKey.ftsSecret).1
  rw [← hsecrets] at hsettled
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  exact otsOpeningRefinedQueryReserve_ge_four_thirds_of_encodingMessageSettled secretKey cache input position hat
    ⟨index, htree, hleaf, hsettled⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
