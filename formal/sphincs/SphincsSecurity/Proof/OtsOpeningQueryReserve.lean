import SphincsSecurity.Proof.JointSecretOpeningQueryBudget
import SphincsSecurity.Proof.OtsProbeQueryCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem TightEncoding.refinedStructuralEncodingQueryCharge_le_two_of_atPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position) :
    TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input ≤ 2 := by
  classical
  have hnotEncoding : ¬ ∃ candidate : EncodingPosition, AtEncodingPosition secretKey.parameter input candidate :=
    fun ⟨candidate, hencoding⟩ => hencoding.not_atPosition position hat
  have hposition : ∃ position : Position, AtPosition secretKey.parameter input position := ⟨position, hat⟩
  unfold refinedStructuralEncodingQueryCharge
  split_ifs <;> simp_all [structuralEncodingQueryCharge]

theorem ftsOpeningQueryReserve_eq_zero_of_atOtsPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position) (hots : OtsProbeSimulation.IsOtsPosition position) :
    ftsOpeningQueryReserve secretKey cache input = 0 := by
  classical
  have hnone : ¬ ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
    rintro ⟨probe, hinput⟩
    have hprobe : AtPosition secretKey.parameter input (.ftsLeaf probe.index probe.tree probe.leafIdx) := by
      rw [← hinput]
      exact ⟨digestBytes probe.candidate, rfl⟩
    rw [atPosition_unique secretKey.parameter hat hprobe] at hots
    exact hots
  simp only [ftsOpeningQueryReserve, FtsProbeSimulation.ftsHashQueryCharge, if_neg hnone, zero_mul]

theorem otsOpeningQueryReserve_ge_one_of_atOtsPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position) (hots : OtsProbeSimulation.IsOtsPosition position) :
    1 ≤ otsOpeningQueryReserve secretKey cache input := by
  rw [otsOpeningQueryReserve, ftsOpeningQueryReserve_eq_zero_of_atOtsPosition secretKey cache input position hat hots,
    tsub_zero]
  have hbound := tsub_le_tsub_left
    (TightEncoding.refinedStructuralEncodingQueryCharge_le_two_of_atPosition secretKey cache input position hat)
    (3 : ℝ≥0∞)
  have hone : (3 : ℝ≥0∞) - 2 = 1 :=
    (ENNReal.eq_sub_of_add_eq' (by norm_num) (show (1 : ℝ≥0∞) + 2 = 3 by norm_num)).symm
  simpa only [hone, residualPrimitiveQueryCharge] using hbound

theorem otsOpeningQueryReserve_ge_two_of_children_settled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position) (hots : OtsProbeSimulation.IsOtsPosition position)
    (hchildren : ∀ child ∈ position.children,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child) :
    2 ≤ otsOpeningQueryReserve secretKey cache input := by
  rw [otsOpeningQueryReserve, ftsOpeningQueryReserve_eq_zero_of_atOtsPosition secretKey cache input position hat hots,
    tsub_zero]
  exact residualPrimitiveQueryCharge_ge_two_of_children_settled secretKey cache input position hat hchildren

end SphincsSecurity.Concrete
