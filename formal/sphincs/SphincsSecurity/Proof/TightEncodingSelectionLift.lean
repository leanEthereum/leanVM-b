import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.TightEncodingSelectionPotential

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

/-- The total encoding potential, extended harmlessly to caches not known to be finite. All caches
reachable from the empty lazy random oracle cache are finite. -/
noncomputable def encodingSelectionAdaptivePotential
    (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  open Classical in
    if hfinite : Finite cache then
      encodingSelectionTotalPotential cache hfinite secretKey
    else 0

theorem encodingSelectionAdaptivePotential_eq
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    encodingSelectionAdaptivePotential cache secretKey =
      encodingSelectionTotalPotential cache hfinite secretKey := by
  rw [encodingSelectionAdaptivePotential, dif_pos hfinite]

@[simp] theorem encodingSelectionAdaptivePotential_empty (secretKey : SecretKey) :
    encodingSelectionAdaptivePotential ∅ secretKey = 0 := by
  rw [encodingSelectionAdaptivePotential_eq finite_empty]
  exact encodingSelectionTotalPotential_empty secretKey

end SphincsSecurity.Concrete.TightEncoding
