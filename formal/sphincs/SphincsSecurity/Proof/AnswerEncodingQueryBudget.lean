import SphincsSecurity.Proof.AnswerEncodingQueryBound
import SphincsSecurity.Proof.FirstFtsParentGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation (otsHashInputCharge IsOtsPosition)

attribute [local irreducible] instFintypePosition

theorem parentStoppedEncodingQueryCharge_le_two (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    parentStoppedEncodingQueryCharge secretKey cache input ≤ 2 := by
  classical
  unfold parentStoppedEncodingQueryCharge
  split_ifs
  · unfold encodingMessageIncrement
    split_ifs <;> norm_num
  all_goals norm_num

theorem parentStoppedEncodingQueryCharge_le_one_of_not_encoding
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hnotEncoding : ¬ ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position) :
    parentStoppedEncodingQueryCharge secretKey cache input ≤ 1 := by
  classical
  unfold parentStoppedEncodingQueryCharge
  split_ifs <;> simp_all

theorem ots_ftsLeaf_parent_queryCharge_eq_zero_of_atEncoding
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) {position : EncodingPosition}
    (hat : AtEncodingPosition secretKey.parameter input position) :
    otsHashInputCharge secretKey.parameter input + FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input +
      ftsParentQueryCharge secretKey cache input = 0 := by
  classical
  have hnotOts : ¬ ∃ candidate, IsOtsPosition candidate ∧ AtPosition secretKey.parameter input candidate := by
    rintro ⟨candidate, _, hc⟩
    exact hat.not_atPosition candidate hc
  have hnotParent : ¬ ∃ candidate, AtPosition secretKey.parameter input candidate ∧ ¬ IsOtsPosition candidate ∧
      ¬ ∀ child ∈ candidate.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child := by
    rintro ⟨candidate, hc, _⟩
    exact hat.not_atPosition candidate hc
  have hnotProbe : ¬ ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
    rintro ⟨probe, heq⟩
    have hp : AtPosition secretKey.parameter input (.ftsLeaf probe.index probe.tree probe.leafIdx) := by
      rw [← heq]
      exact ⟨digestBytes probe.candidate, rfl⟩
    exact hat.not_atPosition _ hp
  simp only [otsHashInputCharge, if_neg hnotOts, FtsProbeSimulation.ftsHashQueryCharge, if_neg hnotProbe,
    ftsParentQueryCharge, parentReserveCharge, if_neg hnotParent, Nat.cast_zero, zero_add]

theorem answerEncoding_parent_ots_fts_queryCharge_le_two
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input +
      (otsHashInputCharge secretKey.parameter input + FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) ≤ 2 := by
  classical
  rw [add_assoc, add_comm (ftsParentQueryCharge secretKey cache input)]
  by_cases hencoding : ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position
  · obtain ⟨position, hat⟩ := hencoding
    rw [ots_ftsLeaf_parent_queryCharge_eq_zero_of_atEncoding secretKey cache input hat, add_zero]
    exact parentStoppedEncodingQueryCharge_le_two secretKey cache input
  · exact (add_le_add (parentStoppedEncodingQueryCharge_le_one_of_not_encoding secretKey cache input hencoding)
      (ots_ftsLeaf_parent_queryCharge_le_one secretKey cache input)).trans_eq (by norm_num)

theorem sampled_answerEncoding_parent_ots_fts_queryCharge_le_two
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
      ftsParentQueryCharge secretKey cache input) adversary +
      sampledQueryCharge (fun secretKey cache input => otsHashInputCharge secretKey.parameter input +
        FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary ≤ 2 * q := by
  rw [← sampledQueryCharge_add]
  exact sampledQueryCharge_le_const _ 2 answerEncoding_parent_ots_fts_queryCharge_le_two adversary q hq

end SphincsSecurity.Concrete
