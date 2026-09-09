import SphincsSecurity.Proof.FirstSuccessTable
import SphincsSecurity.Proof.CanonicalGraphGame
import SphincsSecurity.Proof.EncodingSelectionCache

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def decodeEncodingOutput (output : HashOutput) : Option Encoding := TargetSum.decodeDigest (truncateHash output)

theorem decodeEncodingOutput_invalid_nonempty : (FirstSuccessTable.invalid decodeEncodingOutput).Nonempty := by
  refine ⟨0, (FirstSuccessTable.mem_invalid _ _).mpr ?_⟩
  decide

theorem decodeEncodingOutput_fiber_nonempty (digest : Digest) (word : Encoding)
    (hdecode : TargetSum.decodeDigest digest = some word) :
    (FirstSuccessTable.fiber decodeEncodingOutput word).Nonempty := by
  obtain ⟨output, houtput⟩ := (splitHashOutput_bijective (width := digestBits) (by decide)).2 (digest, 0)
  have hlow : truncateHash output = digest := congrArg Prod.fst houtput
  refine ⟨output, (FirstSuccessTable.mem_fiber _ _ _).mpr ?_⟩
  rw [decodeEncodingOutput, hlow, hdecode]

noncomputable def encodingInvalidRate : ENNReal :=
  1 - (TargetSum.validDigests.card : ENNReal) / (Fintype.card Digest : ENNReal)

theorem decodeEncodingOutput_invalid_ratio :
    (FirstSuccessTable.invalid decodeEncodingOutput).card / (Fintype.card HashOutput : ENNReal) =
      encodingInvalidRate := by
  have h := probEvent_uniform_encoding_invalid
  rw [probEvent_uniformSample] at h
  have hset : (Finset.univ.filter fun output : HashOutput => ¬ TargetSum.ValidDigest (truncateHash output)) =
      FirstSuccessTable.invalid decodeEncodingOutput := by
    ext output
    simp [FirstSuccessTable.invalid, TargetSum.validDigest_iff_decodeDigest_ne_none, decodeEncodingOutput]
  simpa only [hset, encodingInvalidRate] using h

theorem decodeEncodingOutput_fiber_ratio (digest : Digest) (word : Encoding)
    (hdecode : TargetSum.decodeDigest digest = some word) :
    (FirstSuccessTable.fiber decodeEncodingOutput word).card / (Fintype.card HashOutput : ENNReal) =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := probEvent_uniform_truncateHash_eq digest
  rw [probEvent_uniformSample] at h
  have hset : (Finset.univ.filter fun output : HashOutput => truncateHash output = digest) =
      FirstSuccessTable.fiber decodeEncodingOutput word := by
    ext output
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, FirstSuccessTable.mem_fiber]
    constructor
    · intro heq
      rw [decodeEncodingOutput, heq, hdecode]
    · intro heq
      exact TargetSum.decodeDigest_some_injective heq hdecode
  simpa only [hset] using h

theorem encodingTable_success_mass {n : Nat} (index : Fin n) (digest : Digest) (word : Encoding)
    (hdecode : TargetSum.decodeDigest digest = some word) (table : Fin n → HashOutput) :
    (if FirstSuccessTable.select decodeEncodingOutput table = some (index, word) then
      FirstSuccessTable.full n table else 0) =
        (encodingInvalidRate ^ index.val * (Fintype.card Digest : ENNReal)⁻¹) *
          FirstSuccessTable.conditional decodeEncodingOutput index word decodeEncodingOutput_invalid_nonempty
            (decodeEncodingOutput_fiber_nonempty digest word hdecode) table := by
  have h := FirstSuccessTable.full_success_mass decodeEncodingOutput index word
    decodeEncodingOutput_invalid_nonempty (decodeEncodingOutput_fiber_nonempty digest word hdecode) table
  rw [FirstSuccessTable.successMass_eq, decodeEncodingOutput_invalid_ratio,
    decodeEncodingOutput_fiber_ratio digest word hdecode] at h
  by_cases hselected : FirstSuccessTable.select decodeEncodingOutput table = some (index, word) <;>
    simpa only [hselected, if_true, if_false] using h

theorem probEvent_encodingTable_success {n : Nat} (index : Fin n) (digest : Digest) (word : Encoding)
    (hdecode : TargetSum.decodeDigest digest = some word) :
    Pr[fun table => FirstSuccessTable.select decodeEncodingOutput table = some (index, word) |
      FirstSuccessTable.full (Answer := HashOutput) n] =
        encodingInvalidRate ^ index.val * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [FirstSuccessTable.probEvent_full_success decodeEncodingOutput index word decodeEncodingOutput_invalid_nonempty
    (decodeEncodingOutput_fiber_nonempty digest word hdecode), FirstSuccessTable.successMass_eq,
    decodeEncodingOutput_invalid_ratio, decodeEncodingOutput_fiber_ratio digest word hdecode]

theorem encodingTable_exhaustion_mass (n : Nat) (table : Fin n → HashOutput) :
    (if FirstSuccessTable.select decodeEncodingOutput table = none then FirstSuccessTable.full n table else 0) =
      encodingInvalidRate ^ n *
        FirstSuccessTable.exhausted decodeEncodingOutput n decodeEncodingOutput_invalid_nonempty table := by
  rw [FirstSuccessTable.full_exhaustion_mass decodeEncodingOutput n decodeEncodingOutput_invalid_nonempty,
    decodeEncodingOutput_invalid_ratio]

theorem probEvent_encodingTable_exhaustion (n : Nat) :
    Pr[fun table => FirstSuccessTable.select decodeEncodingOutput table = none |
      FirstSuccessTable.full (Answer := HashOutput) n] = encodingInvalidRate ^ n := by
  rw [FirstSuccessTable.probEvent_full_exhaustion decodeEncodingOutput n decodeEncodingOutput_invalid_nonempty,
    decodeEncodingOutput_invalid_ratio]

def referenceEncodingTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) : Fin attempts → HashOutput :=
  fun index => f (encodingRetryInput parameter position message (start + index.val))

def encodingTableResult {n : Nat} (table : Fin n → HashOutput) (start : Nat) : Option (Counter × Encoding) × Nat :=
  let result := FirstSuccessTable.select decodeEncodingOutput table
  (result.map (fun result => (BitVec.ofNat counterBits (start + result.1.val), result.2)),
    result.elim n (fun result => result.1.val + 1))

theorem encodingTableResult_success_iff {n : Nat} (table : Fin n → HashOutput) (start : Nat)
    (index : Fin n) (word : Encoding) :
    encodingTableResult table start = (some (BitVec.ofNat counterBits (start + index.val), word), index.val + 1) ↔
      FirstSuccessTable.select decodeEncodingOutput table = some (index, word) := by
  cases hselected : FirstSuccessTable.select decodeEncodingOutput table with
  | none => simp [encodingTableResult, hselected]
  | some result =>
      obtain ⟨found, value⟩ := result
      simp only [encodingTableResult, hselected, Option.map_some, Option.elim_some,
        Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro ⟨⟨_, hword⟩, hcount⟩
        exact ⟨Fin.ext (by omega), hword⟩
      · rintro ⟨rfl, rfl⟩
        simp

theorem encodingTableResult_exhaustion_iff {n : Nat} (table : Fin n → HashOutput) (start : Nat) :
    encodingTableResult table start = (none, n) ↔ FirstSuccessTable.select decodeEncodingOutput table = none := by
  cases hselected : FirstSuccessTable.select decodeEncodingOutput table <;> simp [encodingTableResult, hselected]

theorem probEvent_encodingTableResult_success {n : Nat} (start : Nat) (index : Fin n)
    (digest : Digest) (word : Encoding) (hdecode : TargetSum.decodeDigest digest = some word) :
    Pr[fun table => encodingTableResult table start =
      (some (BitVec.ofNat counterBits (start + index.val), word), index.val + 1) |
      FirstSuccessTable.full (Answer := HashOutput) n] =
        encodingInvalidRate ^ index.val * (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [encodingTableResult_success_iff]
  exact probEvent_encodingTable_success index digest word hdecode

theorem probEvent_encodingTableResult_exhaustion (n start : Nat) :
    Pr[fun table => encodingTableResult table start = (none, n) | FirstSuccessTable.full (Answer := HashOutput) n] =
      encodingInvalidRate ^ n := by
  simp only [encodingTableResult_exhaustion_iff]
  exact probEvent_encodingTable_exhaustion n

theorem eval_encode_eq_decodeEncodingOutput (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (counter : Nat) :
    evalWithAnswerFn f (encode parameter position.lay position.tree position.leafIdx message
      (BitVec.ofNat counterBits counter)) =
        decodeEncodingOutput (f (encodingRetryInput parameter position message counter)) := by
  simp only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure]
  rfl

theorem referenceEncodingSearch_eq_table (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) :
    referenceEncodingSearch parameter f position.lay position.tree position.leafIdx message attempts start =
      encodingTableResult (referenceEncodingTable parameter f position message attempts start) start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      have htail :
          (fun i : Fin attempts => referenceEncodingTable parameter f position message (attempts + 1) start i.succ) =
            referenceEncodingTable parameter f position message attempts (start + 1) := by
        funext i
        change f (encodingRetryInput parameter position message (start + (i.val + 1))) =
          f (encodingRetryInput parameter position message (start + 1 + i.val))
        rw [show start + (i.val + 1) = start + 1 + i.val by omega]
      rw [referenceEncodingSearch, eval_encode_eq_decodeEncodingOutput,
        encodingTableResult, FirstSuccessTable.select]
      have hzero : referenceEncodingTable parameter f position message (attempts + 1) start 0 =
          f (encodingRetryInput parameter position message start) := by simp [referenceEncodingTable]
      rw [hzero]
      cases hdecode : decodeEncodingOutput (f (encodingRetryInput parameter position message start)) with
      | some word => simp
      | none =>
          rw [htail, ih]
          unfold encodingTableResult
          cases hselected : FirstSuccessTable.select decodeEncodingOutput
              (referenceEncodingTable parameter f position message attempts (start + 1)) with
          | none => simp [Nat.add_comm]
          | some result =>
              rcases result with ⟨index, word⟩
              simp [Nat.add_comm, Nat.add_left_comm]

end SphincsSecurity.Concrete
