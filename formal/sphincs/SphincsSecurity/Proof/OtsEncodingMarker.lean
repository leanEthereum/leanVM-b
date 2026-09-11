import SphincsSecurity.Proof.EncodingFreshRow
import SphincsSecurity.Proof.EncodingInputs
import SphincsSecurity.Proof.EncodingBackwardWitness
import SphincsSecurity.Proof.OtsContactTrace
import SphincsSecurity.Proof.QueryClassAllocation

namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ OtsContactTrace.contacts canonicalEncodingInputs

def EntryMarker (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (entry : HashInput × HashOutput) : Prop :=
  AtEncodingPosition parameter entry.1 ⟨address.1, address.2.1, address.2.2.1⟩ ∧
    entry.1 ∈ canonicalEncodingInputs parameter ∧
    ∃ candidate, decodeEncodingOutput entry.2 = some candidate ∧
      TargetSum.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2

theorem entryMarker_encoding_iff (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (message : Digest) (counter : Counter) (output : HashOutput) :
    EntryMarker parameter words address
      (tweakableHashInput parameter (.encoding address.1 address.2.1 address.2.2.1)
        (digestBytes message ++ counterBytes counter), output) ↔
      ∃ candidate, decodeEncodingOutput output = some candidate ∧
        TargetSum.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2 := by
  have hcounter : counter.toNat < encodingAttemptLimit := by
    simpa only [encodingAttemptLimit, counterBits] using counter.isLt
  have hin := encodingRetryInput_mem_canonicalEncodingInputs parameter
    ⟨address.1, address.2.1, address.2.2.1⟩ message ⟨counter.toNat, hcounter⟩
  simp only [encodingRetryInput, BitVec.ofNat_toNat] at hin
  exact and_iff_right ⟨_, rfl⟩ |>.trans (and_iff_right hin)

def Seen (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (trace : OtsContactTrace.Trace) : Prop := ∃ entry ∈ trace.toList, EntryMarker parameter words address entry

theorem entryMarker_unique (parameter : PublicParameter) (words : OtsReferenceWords) (entry : HashInput × HashOutput)
    (left right : OtsPrefix.ChainAddress) (hleft : EntryMarker parameter words left entry) (hright : EntryMarker parameter words right entry) :
    left = right := by
  rcases left with ⟨leftLay, leftTree, leftLeaf, leftChain⟩
  rcases right with ⟨rightLay, rightTree, rightLeaf, rightChain⟩
  obtain ⟨hl, _, leftWord, hdecodeLeft, hneighborLeft⟩ := hleft
  obtain ⟨hr, _, rightWord, hdecodeRight, hneighborRight⟩ := hright
  have hp := atEncodingPosition_unique hl hr
  simp only [EncodingPosition.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  have hw : leftWord = rightWord := Option.some.inj (hdecodeLeft.symm.trans hdecodeRight)
  subst rightWord
  have hc := hneighborLeft.lowered_unique hneighborRight
  cases hc
  rfl

theorem entryMarker_not_contact (parameter : PublicParameter) (words : OtsReferenceWords) (address other : OtsPrefix.ChainAddress)
    (endpoint : Digest) (entry : HashInput × HashOutput) (hm : EntryMarker parameter words address entry) :
    ¬OtsContactTrace.EntryContact (OtsPrefix.atAddress parameter words other) endpoint entry := by
  intro hc
  exact QueryClass.prefix_not_encoding (OtsPrefix.atAddress parameter words other) (.inr entry.1)
    (OtsContactTrace.entryContact_selects _ endpoint entry hc) ⟨_, hm.1⟩

theorem seen_one (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) :
    ¬Seen parameter words address 1 := by simp [Seen]

theorem seen_of (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) :
    Seen parameter words address (FreeMonoid.of entry) ↔ EntryMarker parameter words address entry := by simp [Seen]

theorem seen_mul (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (before after : OtsContactTrace.Trace) :
    Seen parameter words address (before * after) ↔ Seen parameter words address before ∨ Seen parameter words address after := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]

noncomputable def markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) :
    Finset OtsPrefix.ChainAddress := Finset.univ.filter fun address => Seen parameter words address trace

theorem mem_markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ markers parameter words trace ↔ Seen parameter words address trace := by
  simp only [markers, Finset.mem_filter, Finset.mem_univ, true_and]

theorem markers_one (parameter : PublicParameter) (words : OtsReferenceWords) : markers parameter words 1 = ∅ := by
  ext address
  simp only [mem_markers, seen_one, Finset.notMem_empty]

theorem markers_mul (parameter : PublicParameter) (words : OtsReferenceWords) (before after : OtsContactTrace.Trace) :
    markers parameter words (before * after) = markers parameter words before ∪ markers parameter words after := by
  ext address
  simp only [mem_markers, seen_mul, Finset.mem_union]

attribute [local irreducible] markers

theorem markers_of_card_le_one (parameter : PublicParameter) (words : OtsReferenceWords) (entry : HashInput × HashOutput) :
    (markers parameter words (FreeMonoid.of entry)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro left hl right hr
  rw [mem_markers, seen_of] at hl hr
  exact entryMarker_unique parameter words entry left right hl hr

theorem entryMarker_uniform_le (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (input : HashInput) :
    Pr[fun output : HashOutput => EntryMarker parameter words address (input, output) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      41 / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (mx := ($ᵗ HashOutput : ProbComp HashOutput)) ?_).trans
    (TargetSum.unitNeighbors_uniform_le (words address.1 address.2.1 address.2.2.1) address.2.2.2)
  intro output _ hm
  obtain ⟨_, _, candidate, hd, hn⟩ := hm
  exact TargetSum.mem_decodingDigests.mpr ⟨candidate, TargetSum.mem_unitNeighbors.mpr hn, hd⟩

theorem entryMarker_subset_uniform_le (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (input : HashInput) :
    Pr[fun output : HashOutput => ∃ address ∈ addresses, EntryMarker parameter words address (input, output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (41 * (addresses.card : ENNReal)) / Fintype.card Digest := by
  have h := (probEvent_exists_finset_le_sum addresses ($ᵗ HashOutput : ProbComp HashOutput)
    (fun address output => EntryMarker parameter words address (input, output))).trans
    (Finset.sum_le_sum fun address _ => entryMarker_uniform_le parameter words address input)
  simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem entryMarker_any_uniform_le (parameter : PublicParameter) (words : OtsReferenceWords) (input : HashInput) :
    Pr[fun output : HashOutput => ∃ address, EntryMarker parameter words address (input, output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1722 / (Fintype.card Digest : ENNReal) := by
  by_cases hp : ∃ position, AtEncodingPosition parameter input position
  · obtain ⟨position, hp⟩ := hp
    refine (_root_.probEvent_mono (mx := ($ᵗ HashOutput : ProbComp HashOutput)) ?_).trans
      (TargetSum.allUnitNeighbors_uniform_le (words position.lay position.tree position.leafIdx))
    intro output _ hm
    obtain ⟨⟨lay, tree, leaf, chain⟩, hposition, _, candidate, hd, hn⟩ := hm
    have he := atEncodingPosition_unique hposition hp
    subst position
    exact TargetSum.mem_decodingDigests.mpr ⟨candidate, TargetSum.mem_allUnitNeighbors.mpr ⟨chain, hn⟩, hd⟩
  · have he : (fun output : HashOutput => ∃ address, EntryMarker parameter words address (input, output)) = fun _ => False := by
      funext output
      apply propext
      constructor
      · rintro ⟨address, hm⟩
        exact hp ⟨_, hm.1⟩
      · exact False.elim
    rw [he]
    simp only [probEvent_eq_tsum_ite, if_false, tsum_zero, zero_le]

end SphincsSecurity.Concrete.OtsEncodingMarker
