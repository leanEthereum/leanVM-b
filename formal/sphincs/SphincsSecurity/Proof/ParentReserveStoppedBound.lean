import SphincsSecurity.Proof.FirstExceptionStoppedCharge
import SphincsSecurity.Proof.ParentReserveBound

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem firstParentSelectionPotential_query_le_reserve
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range query × QueryCache HashSpec) (eps : ENNReal) :
    firstExceptionSelectionPotential (EligibleParentRecord parameter eligible)
      (fun cache => (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) * eps)
      result.2 (recordQueryException (CleanParentSettlement parameter otsSecret ftsSecret) cache query result.1) ≤
      exceptionReservePotential (parentReserve parameter otsSecret ftsSecret eligible) eps result.2
        (queryException (EligibleParentSettlement parameter otsSecret ftsSecret eligible) cache query result.1) := by
  cases query with
  | inl sample =>
      simp only [recordQueryException, queryException, firstExceptionSelectionPotential, exceptionReservePotential,
        Bool.false_eq_true, if_false, zero_add, le_refl]
  | inr input =>
      simp only [recordQueryException]
      split_ifs with hparent
      · by_cases hselected : EligibleParentRecord parameter eligible ⟨cache, input, result.1⟩
        · have hx : cache input = none ∧ CleanParentSettlement parameter otsSecret ftsSecret cache input result.1 := by
            simpa only [queryException, decide_eq_true_eq] using hparent
          have heligible : EligibleParentSettlement parameter otsSecret ftsSecret eligible cache input result.1 :=
            ⟨hx.2.2, hselected⟩
          have hflag : queryException (EligibleParentSettlement parameter otsSecret ftsSecret eligible) cache (.inr input) result.1 = true := by
            simp only [queryException, hx.1, heligible, and_self, decide_true]
          simp only [firstExceptionSelectionPotential, if_pos hselected, exceptionReservePotential, hflag, if_true]
          exact le_self_add
        · simp only [firstExceptionSelectionPotential, if_neg hselected, zero_le]
      · simp only [firstExceptionSelectionPotential, exceptionReservePotential]
        exact le_add_self

theorem probEvent_firstEligibleParentRecord_le_preExceptionCharge (computation : OracleComp OracleWorld α) :
    Pr[fun result => ∃ record ∈ result.2, EligibleParentRecord parameter eligible record |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret) computation ∅ none] ≤
      expectedPreExceptionCharge (CleanParentSettlement parameter otsSecret ftsSecret)
        (fun cache input => (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ENNReal))
        computation ∅ false * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let eps : ENNReal := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hstep (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
      (∑' result, Pr[= result | (romImpl query).run cache] *
        firstExceptionSelectionPotential (EligibleParentRecord parameter eligible)
          (fun cache => (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) * eps)
          result.2 (recordQueryException (CleanParentSettlement parameter otsSecret ftsSecret) cache query result.1)) ≤
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) * eps +
        hashQueryCharge (fun cache input => (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ENNReal) * eps) cache query := by
    apply (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
      (firstParentSelectionPotential_query_le_reserve parameter otsSecret ftsSecret eligible query cache result eps)).trans
    simpa only [exceptionReservePotential, Bool.false_eq_true, if_false, zero_add, Bool.false_or] using
      expected_exceptionReserve_query_le
        (EligibleParentSettlement parameter otsSecret ftsSecret eligible)
        (parentReserve parameter otsSecret ftsSecret eligible)
        (parentReserveCharge parameter otsSecret ftsSecret eligible) eps
        (fun target => by rw [← probOutput_map]; exact probOutput_truncateHash_le target)
        (fun _ hfinite input hfresh => parentReserve_step parameter otsSecret ftsSecret eligible hfinite input hfresh)
        query cache hfinite false
  have hbound := probEvent_firstException_selected_le_preExceptionCharge
    (CleanParentSettlement parameter otsSecret ftsSecret) (EligibleParentRecord parameter eligible)
    (fun cache => (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) * eps)
    (fun cache input => (parentReserveCharge parameter otsSecret ftsSecret eligible cache input : ENNReal) * eps)
    hstep computation ∅ finite_empty
  simpa only [parentReserve_empty, Nat.cast_zero, zero_mul, zero_add, expectedPreExceptionCharge_mul] using hbound

end SphincsSecurity
