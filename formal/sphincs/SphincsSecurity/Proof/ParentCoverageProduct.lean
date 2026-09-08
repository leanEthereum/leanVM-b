import SphincsSecurity.Proof.ParentReserveSigning
import SphincsSecurity.Proof.FreshParentCollisionCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def parentCoverageProduct (key : SecretKey) (cap budget : Nat) (state : CoverLogState) : ENNReal :=
  boundedRemainingCoveragePotential key cap budget state *
    ((parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) state.1 : ENNReal) *
      (2 * (Fintype.card Digest : ENNReal)⁻¹))

theorem parentCoverageProduct_budget_mono (key : SecretKey) (cap : Nat) (state : CoverLogState)
    {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    parentCoverageProduct key cap smaller state ≤ parentCoverageProduct key cap larger state :=
  mul_le_mul' (boundedRemainingCoveragePotential_budget_mono key cap state hbudget) le_rfl

theorem parentReserve_randomOracle_le_fresh (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (result)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.2 : ENNReal) ≤
      (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal) +
        freshFtsParentReserveCharge key cache input := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simpa only [freshFtsParentReserveCharge, freshParentReserveCharge, if_pos hfresh, ← Nat.cast_add] using
      Nat.cast_le (α := ENNReal).mpr (parentReserve_cacheQuery_le_charge key.parameter key.otsSecret key.ftsSecret
        (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) (answer := answer) hfresh)
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, mem_support_pure_iff] at hr
    subst result
    exact le_self_add

theorem freshFtsParentReserveCharge_message_eq_zero (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hmessage : MessageHashInput key.parameter input) : freshFtsParentReserveCharge key cache input = 0 := by
  unfold freshFtsParentReserveCharge freshParentReserveCharge parentReserveCharge
  simp only [show ¬ ∃ position, AtPosition key.parameter input position ∧ ¬ OtsProbeSimulation.IsOtsPosition position ∧
      ¬ ∀ child ∈ position.children, Settled key.parameter key.otsSecret key.ftsSecret cache child from by
        rintro ⟨position, hat, _⟩; exact hmessage.not_atPosition position hat,
    if_false, Nat.cast_zero, ite_self]

theorem expected_logTraced_boundedRemainingCoverage_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      boundedRemainingCoveragePotential key cap (budget - signingExecutionHashCost input) result.2) ≤
      boundedRemainingCoveragePotential key cap budget state := by
  apply le_min
  · calc
      _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * 1 :=
        ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (boundedRemainingCoveragePotential_le_one _ _ _ _)
      _ ≤ 1 := by simpa only [mul_one] using (tsum_probOutput_le_one (mx := (logTracedMappedAdversaryImpl key input).run state))
  · have h := mul_le_mul' (le_self_add.trans (expected_logTraced_remainingCoverage_add_unused_le key cap budget hcap state hsigned hcache
        input hcost ∅ Finset.univ (by constructor <;> simp))) (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
    rw [← ENNReal.tsum_mul_right] at h
    simp only [mul_assoc] at h
    exact (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (min_le_right _ _)).trans h

private theorem expected_parentCoverageProduct_le_of_parent_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (hparent : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state),
      parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.2.1 ≤
        parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) state.1) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      parentCoverageProduct key cap (budget - signingExecutionHashCost input) result.2) ≤ parentCoverageProduct key cap budget state := by
  unfold parentCoverageProduct
  apply le_trans ?_ (mul_le_mul' (expected_logTraced_boundedRemainingCoverage_le key cap budget hcap state hsigned hcache input hcost) le_rfl)
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc]
  by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
  · exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr (hparent result hr)) le_rfl))
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expected_parentCoverageProduct_sign_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      parentCoverageProduct key cap (budget - signingExecutionHashCost (.inr message)) result.2) ≤ parentCoverageProduct key cap budget state := by
  apply expected_parentCoverageProduct_le_of_parent_le key cap budget hcap state hsigned hcache (.inr message) hcost
  intro result hr
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
  obtain ⟨base, hb, rfl⟩ := hr
  exact parentReserve_sign_le key _ message state.1 base.2 base.1 hb

theorem expected_parentCoverageProduct_message_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : HashInput) (hmessage : MessageHashInput key.parameter input)
    (hcost : 1 ≤ budget) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl (.inr input))).run state] *
      parentCoverageProduct key cap (budget - 1) result.2) ≤ parentCoverageProduct key cap budget state := by
  apply expected_parentCoverageProduct_le_of_parent_le key cap budget hcap state hsigned hcache (.inl (.inr input)) hcost
  intro result hr
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
  obtain ⟨base, hb, rfl⟩ := hr
  have h := parentReserve_randomOracle_le_fresh key state.1 input base hb
  rw [freshFtsParentReserveCharge_message_eq_zero key state.1 input hmessage, add_zero] at h
  exact Nat.cast_le.mp h

theorem expected_parentCoverageProduct_nonmessage_le (key : SecretKey) (cap budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : HashInput) (hmessage : ¬ MessageHashInput key.parameter input) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl (.inr input))).run state] *
      parentCoverageProduct key cap (budget - 1) result.2) ≤ parentCoverageProduct key cap budget state +
        boundedRemainingCoveragePotential key cap (budget - 1) state *
          (collisionSigningStructuralCharge key state.1 input * (Fintype.card Digest : ENNReal)⁻¹) := by
  let before := (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) state.1 : ENNReal)
  let fresh := freshFtsParentReserveCharge key state.1 input
  have hbound : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl (.inr input))).run state] *
      parentCoverageProduct key cap (budget - 1) result.2) ≤
      boundedRemainingCoveragePotential key cap (budget - 1) state * ((before + fresh) * (2 * (Fintype.card Digest : ENNReal)⁻¹)) := by
    apply le_trans ?_ (mul_le_of_le_one_left' (tsum_probOutput_le_one (mx := (logTracedMappedAdversaryImpl key (.inl (.inr input))).run state)))
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl (.inr input))).run state)
    · have hc := remainingCoveragePotential_nonmessage_step key cap (budget - 1) state input hsigned hmessage result hr ∅ Finset.univ
      rw [parentCoverageProduct, boundedRemainingCoveragePotential, hc]
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      apply mul_le_mul' ?_ le_rfl
      rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
      obtain ⟨base, hb, rfl⟩ := hr
      exact parentReserve_randomOracle_le_fresh key state.1 input base hb
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  apply hbound.trans
  rw [add_mul, mul_add]
  apply add_le_add (parentCoverageProduct_budget_mono key cap state (Nat.sub_le _ _))
  apply mul_le_mul' le_rfl
  have h := mul_le_mul' (twice_freshFtsParentReserveCharge_le_collisionCharge key state.1 input) (le_refl (Fintype.card Digest : ENNReal)⁻¹)
  convert h using 1
  ring

end SphincsSecurity.Concrete
