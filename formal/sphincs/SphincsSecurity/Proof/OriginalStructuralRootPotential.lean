import SphincsSecurity.Proof.OriginalStructuralPotential
import SphincsSecurity.Proof.RootStructuralCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem structuralRecordPotential_root_irrel
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (left right : Digest)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    structuralRecordPotential ⟨parameter, left, otsSecret, ftsSecret⟩ cache saved =
      structuralRecordPotential ⟨parameter, right, otsSecret, ftsSecret⟩ cache saved := rfl

theorem structuralRecordPotential_empty (key : SecretKey) : structuralRecordPotential key ∅ none = 0 := by
  simp [structuralRecordPotential, answerEncodingMonitorPotential, answerEncodingAdaptivePotential_eq finite_empty,
    ftsParentSelectionPotential, firstExceptionSelectionPotential, parentReserve_empty]

theorem structuralRecordPotential_treeRoot_eq_zero
    (key : SecretKey) (lay : Layer) (tree : TreeIndex) (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl
      (liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)).run ∅)) :
    structuralRecordPotential key result.2 none = 0 := by
  let computation : OracleComp OracleWorld Digest := liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest)
  let exception := CleanParentSettlement key.parameter key.otsSecret key.ftsSecret
  have h := expected_structuralRecordPotential_le_preCharge key computation ∅ finite_empty none
  have hz := expectedPreExceptionCharge_treeRoot_eq_zero key exception lay tree ∅ false
  change expectedPreExceptionCharge exception (signingStructuralCharge key) computation ∅ false = 0 at hz
  rw [structuralRecordPotential_empty, Option.isSome_none, hz, zero_mul, zero_add] at h
  have hzero := le_antisymm h zero_le
  rw [← runFirstException_project exception computation ∅ none, support_map] at hresult
  obtain ⟨recorded, hr, hproject⟩ := hresult
  have hnone := runFirstException_treeRoot_no_record key exception (fun _ _ _ h => h.2) lay tree hr
  have hterm := (ENNReal.tsum_eq_zero.mp hzero) recorded
  have hp := (mul_eq_zero.mp hterm).resolve_left (probOutput_ne_zero_of_mem_support hr)
  rw [← hproject, ← hnone]
  exact hp

end SphincsSecurity.Concrete
