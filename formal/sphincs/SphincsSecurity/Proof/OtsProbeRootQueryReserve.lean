import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.JointSecretOpeningQueryBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem ftsOpeningQueryReserve_eq_zero_of_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position) :
    ftsOpeningQueryReserve secretKey cache input = 0 := by
  classical
  have hnone : ¬ ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
    rintro ⟨probe, hinput⟩
    apply hat.not_atPosition (.ftsLeaf probe.index probe.tree probe.leafIdx)
    rw [← hinput]
    exact ⟨digestBytes probe.candidate, rfl⟩
  simp only [ftsOpeningQueryReserve, FtsProbeSimulation.ftsHashQueryCharge, if_neg hnone, zero_mul]

theorem otsOpeningQueryReserve_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position) :
    otsOpeningQueryReserve secretKey cache input =
      if cache input = none then
        if HasEncodingTarget cache secretKey position then 2
        else if EncodingMessageSettledAt cache secretKey position then 1 else 0
      else 3 := by
  classical
  rw [otsOpeningQueryReserve,
    ftsOpeningQueryReserve_eq_zero_of_atEncodingPosition secretKey cache input position hat, tsub_zero]
  have hexists : ∃ candidate : EncodingPosition, AtEncodingPosition secretKey.parameter input candidate :=
    ⟨position, hat⟩
  have hselected : Classical.choose hexists = position :=
    atEncodingPosition_unique (Classical.choose_spec hexists) hat
  unfold residualPrimitiveQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge
  by_cases hfresh : cache input = none
  · simp only [hfresh, if_true, hexists, ↓reduceDIte, hselected, TightEncoding.encodingStageIncrement]
    split_ifs <;> norm_num
    · exact (ENNReal.eq_sub_of_add_eq' (by norm_num)
        (show (2 : ℝ≥0∞) + 1 = 3 by norm_num)).symm
    · exact (ENNReal.eq_sub_of_add_eq' (by norm_num)
        (show (1 : ℝ≥0∞) + 2 = 3 by norm_num)).symm
  · simp [hfresh]

end SphincsSecurity.Concrete
