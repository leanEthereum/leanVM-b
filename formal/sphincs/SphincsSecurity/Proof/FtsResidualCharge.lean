import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.JointPrimitiveQueryBudget
import SphincsSecurity.Proof.SecretProbe

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem residualPrimitiveQueryCharge_ge_two_of_children_settled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position)
    (hchildren : ∀ child ∈ position.children,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child) :
    2 ≤ residualPrimitiveQueryCharge secretKey cache input := by
  have h := TightEncoding.refinedStructuralEncodingQueryCharge_le_one_of_children_settled
    secretKey cache input position hat hchildren
  have hsub := tsub_le_tsub_left h (3 : ℝ≥0∞)
  have heq : (3 : ℝ≥0∞) - 1 = 2 := by
    exact (ENNReal.eq_sub_of_add_eq' (by norm_num)
      (show (2 : ℝ≥0∞) + 1 = 3 by norm_num)).symm
  rw [heq] at hsub
  exact hsub

theorem residualPrimitiveQueryCharge_ge_two_ftsProbe
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (probe : FtsSecretProbe) :
    2 ≤ residualPrimitiveQueryCharge secretKey cache (probe.input secretKey.parameter) := by
  apply residualPrimitiveQueryCharge_ge_two_of_children_settled secretKey cache _
    (.ftsLeaf probe.index probe.tree probe.leafIdx) ⟨digestBytes probe.candidate, rfl⟩
  intro child hchild
  simp only [Position.children, List.not_mem_nil] at hchild

end SphincsSecurity.Concrete
