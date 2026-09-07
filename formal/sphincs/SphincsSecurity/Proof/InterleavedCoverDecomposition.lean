import SphincsSecurity.Proof.WorldCoverBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def signingInterleavedCoverStepCharge (key : SecretKey) (cap : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message => validInterleavedCoverStepCharge key cap state (.inr message)

theorem validInterleavedCoverStepCharge_eq_world_add_signing (key : SecretKey) (cap : Nat) (state : CoverLogState)
    (input : (OracleWorld + SigningSpec).Domain) :
    validInterleavedCoverStepCharge key cap state input =
      worldInterleavedCoverStepCharge key cap state input + signingInterleavedCoverStepCharge key cap state input := by
  cases input <;> simp only [worldInterleavedCoverStepCharge, signingInterleavedCoverStepCharge, add_zero, zero_add]

noncomputable def expectedSigningCoverCharge {α : Type} (key : SecretKey) (cap : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => signingInterleavedCoverStepCharge key cap state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedSigningCoverCharge_pure {α : Type} (key : SecretKey) (cap : Nat)
    (value : α) (state : CoverLogState) : expectedSigningCoverCharge key cap (pure value) state = 0 := rfl

theorem expectedSigningCoverCharge_query_bind {α : Type} (key : SecretKey) (cap : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedSigningCoverCharge key cap (OracleSpec.query input >>= next) state =
      signingInterleavedCoverStepCharge key cap state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedSigningCoverCharge key cap (next result.1) result.2 := by
  cases input <;> rfl

theorem expectedValidInterleavedCoverCharge_eq_world_add_signing {α : Type} (key : SecretKey) (cap : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedValidInterleavedCoverCharge key cap computation state =
      expectedWorldCoverCharge key cap computation state + expectedSigningCoverCharge key cap computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedValidInterleavedCoverCharge_pure, expectedWorldCoverCharge_pure, expectedSigningCoverCharge_pure, add_zero]
  | query_bind input next ih =>
      rw [expectedValidInterleavedCoverCharge_query_bind, expectedWorldCoverCharge_query_bind, expectedSigningCoverCharge_query_bind,
        validInterleavedCoverStepCharge_eq_world_add_signing]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      ac_rfl

theorem expectedValidInterleavedCoverCharge_le_expanded_queryBound {α : Type} (key : SecretKey) (cap : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    expectedValidInterleavedCoverCharge key cap computation state ≤
      (q : ENNReal) * (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
        frozenCoverWeight key result.2) + expectedSigningCoverCharge key cap computation state := by
  rw [expectedValidInterleavedCoverCharge_eq_world_add_signing]
  exact add_le_add (expectedWorldCoverCharge_le_expanded_queryBound key cap computation q hbound state hsigned) le_rfl

end SphincsSecurity.Concrete
