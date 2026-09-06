import SphincsSecurity.Proof.ParentReserve
import SphincsSecurity.Proof.AmortizedExceptionCharge
import SphincsSecurity.Proof.FirstExceptionSelection

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem probEvent_eligibleParentSettlement_le_queryCharge (computation : OracleComp OracleWorld α) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (EligibleParentSettlement parameter otsSecret ftsSecret eligible) computation ∅ false] ≤
      expectedQueryCharge (fun cache input =>
        (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ℝ≥0∞)) computation ∅ *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hbound := probEvent_runExceptionMonitor_le_amortized_queryCharge
    (EligibleParentSettlement parameter otsSecret ftsSecret eligible)
    (parentReserve parameter otsSecret ftsSecret eligible)
    (parentReserveCharge parameter otsSecret ftsSecret eligible)
    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
    (fun target => by rw [← probOutput_map]; exact probOutput_truncateHash_le target)
    (fun _ hfinite input hfresh => parentReserve_step parameter otsSecret ftsSecret eligible hfinite input hfresh)
    computation ∅ finite_empty
  simpa only [parentReserve_empty, Nat.cast_zero, zero_mul, zero_add] using hbound

def EligibleParentRecord (parameter : PublicParameter) (eligible : Position → Prop)
    (record : ExceptionRecord) : Prop :=
  ∃ child parent, AtPosition parameter record.input child ∧ child.parentOf = some parent ∧ eligible parent

theorem probEvent_firstEligibleParentRecord_le_queryCharge (computation : OracleComp OracleWorld α) :
    Pr[fun result => ∃ record ∈ result.2, EligibleParentRecord parameter eligible record |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret) computation ∅ none] ≤
      expectedQueryCharge (fun cache input =>
        (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ℝ≥0∞)) computation ∅ *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  exact (probEvent_firstException_selected_le_monitor
    (CleanParentSettlement parameter otsSecret ftsSecret) (EligibleParentRecord parameter eligible)
    (EligibleParentSettlement parameter otsSecret ftsSecret eligible)
    (fun _ _ _ hparent hselected => ⟨hparent.2, hselected⟩) computation ∅).trans
      (probEvent_eligibleParentSettlement_le_queryCharge parameter otsSecret ftsSecret eligible computation)

end SphincsSecurity
