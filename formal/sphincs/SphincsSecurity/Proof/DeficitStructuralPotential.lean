import SphincsSecurity.Proof.DeficitExceptionRecord
import SphincsSecurity.Proof.FirstExceptionCleanCharge
import SphincsSecurity.Proof.CollisionStructuralPotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
open FtsProbeSimulation.JointOriginal (deficitStoppingException)
attribute [local instance] Classical.propDecidable

theorem collisionStructuralRecordPotential_message_eq_zero
    (key : SecretKey) (cache : QueryCache HashSpec) (record : ExceptionRecord)
    (hmessage : MessageHashInput key.parameter record.input) :
    collisionStructuralRecordPotential key cache (some record) = 0 := by
  have hnot : ¬ EligibleParentRecord key.parameter (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) record := by
    rintro ⟨child, parent, hat, _⟩
    exact atPosition_not_message hat hmessage
  simp only [collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential,
    Option.isSome_some, if_true, ftsParentSelectionPotential, firstExceptionSelectionPotential, if_neg hnot, zero_add]

theorem collisionStructuralRecordPotential_deficit_query_le
    (key : SecretKey) (cache : QueryCache HashSpec) (hclean : ¬ MessageDeficitExceptional key cache)
    (query : OracleWorld.Domain) (answer : OracleWorld.Range query) (after : QueryCache HashSpec) :
    collisionStructuralRecordPotential key after
      (recordQueryException (deficitStoppingException key (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret))
        cache query answer) ≤
    collisionStructuralRecordPotential key after
      (recordQueryException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) cache query answer) := by
  let parent := CleanParentSettlement key.parameter key.otsSecret key.ftsSecret
  change collisionStructuralRecordPotential key after
    (recordQueryException (deficitStoppingException key parent) cache query answer) ≤
    collisionStructuralRecordPotential key after (recordQueryException parent cache query answer)
  cases query with
  | inl sample => exact le_rfl
  | inr input =>
      by_cases hp : queryException parent cache (.inr input) answer = true
      · have hpair : cache input = none ∧ parent cache input answer := by
          simpa only [queryException, decide_eq_true_eq] using hp
        have hs : queryException (deficitStoppingException key parent) cache (.inr input) answer = true := by
          simp only [queryException, decide_eq_true_eq]
          exact ⟨hpair.1, Or.inl hpair.2⟩
        simp only [recordQueryException, hp, hs, if_true, le_refl]
      · by_cases hs : queryException (deficitStoppingException key parent) cache (.inr input) answer = true
        · have hpair : cache input = none ∧ deficitStoppingException key parent cache input answer := by
            simpa only [queryException, decide_eq_true_eq] using hs
          have hbad : MessageDeficitExceptional key (cache.cacheQuery input answer) := by
            rcases hpair.2 with hparent | hbad
            · exact False.elim (hp (by simp only [queryException, decide_eq_true_eq]; exact ⟨hpair.1, hparent⟩))
            · exact hbad
          have hm : MessageHashInput key.parameter input := by
            by_contra hn
            exact hclean ((messageDeficitExceptional_cacheQuery_nonmessage key cache input answer hpair.1 hn).mp hbad)
          rw [recordQueryException, if_pos hs, collisionStructuralRecordPotential_message_eq_zero key after _ hm]
          exact zero_le
        · simp only [recordQueryException, hp, hs, le_refl]

theorem expected_deficitStructuralRecordPotential_le_preCharge
    (key : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) (hclean : saved.isSome = false → ¬ MessageDeficitExceptional key cache) :
    (∑' result, Pr[= result | runFirstException
        (deficitStoppingException key (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret)) computation cache saved] *
      collisionStructuralRecordPotential key result.1.2 result.2) ≤
      collisionStructuralRecordPotential key cache saved +
        expectedPreExceptionCharge (deficitStoppingException key (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret))
          (collisionSigningStructuralCharge key) computation cache saved.isSome * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← expectedPreExceptionCharge_mul]
  apply expected_runFirstException_potential_le_preCharge_of_detects (MessageDeficitExceptional key) _
    (fun _ _ _ h => Or.inr h) _ _ ?_ computation cache hfinite saved hclean
  intro query cache hfinite saved hclean
  cases saved with
  | some record =>
      simp only [retainFirstException, collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential,
        Option.isSome_some, if_true, ftsParentSelectionPotential, firstExceptionSelectionPotential, zero_add, add_zero]
      rw [ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]
  | none =>
      have hbase := expected_collisionStructuralRecordPotential_le_preCharge key
        ((OracleSpec.query query : OracleComp OracleWorld (OracleWorld.Range query)) >>= pure) cache hfinite none
      simp only [runFirstException, OracleComp.construct_query_bind, OracleComp.construct_pure, tsum_probOutput_bind_mul,
        tsum_probOutput_pure_mul, expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_pure,
        mul_zero, tsum_zero, add_zero, Option.isSome_none, Bool.false_eq_true, if_false] at hbase
      change (∑' result : OracleWorld.Range query × QueryCache HashSpec, Pr[= result | (romImpl query).run cache] *
        collisionStructuralRecordPotential key result.2
          (recordQueryException (deficitStoppingException key (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret))
            cache query result.1)) ≤ collisionStructuralRecordPotential key cache none +
        hashQueryCharge (fun cache input => collisionSigningStructuralCharge key cache input * (Fintype.card Digest : ENNReal)⁻¹) cache query
      apply (ENNReal.tsum_le_tsum fun result : OracleWorld.Range query × QueryCache HashSpec => mul_le_mul' le_rfl
        (collisionStructuralRecordPotential_deficit_query_le key cache (hclean rfl) query result.1 result.2)).trans
      have hscale : hashQueryCharge
          (fun cache input => collisionSigningStructuralCharge key cache input * (Fintype.card Digest : ENNReal)⁻¹) cache query =
          hashQueryCharge (collisionSigningStructuralCharge key) cache query * (Fintype.card Digest : ENNReal)⁻¹ := by
        cases query <;> simp only [hashQueryCharge, Sum.elim_inl, Sum.elim_inr, zero_mul]
      rw [hscale]
      exact hbase

end SphincsSecurity.Concrete
