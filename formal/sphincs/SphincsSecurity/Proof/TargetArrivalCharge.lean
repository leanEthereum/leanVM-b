import SphincsSecurity.Proof.TargetArrivalStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedWeightedIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (cost : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => (cost state.1 input : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedWeightedIndexCharge_pure {α : Type} (key : SecretKey) (cap : Nat)
    (cost : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (value : α) (state : CoverLogState) :
    expectedWeightedIndexCharge key cap cost groups remaining (pure value) state = 0 := rfl

theorem expectedWeightedIndexCharge_query_bind {α : Type} (key : SecretKey) (cap : Nat)
    (cost : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedWeightedIndexCharge key cap cost groups remaining (OracleSpec.query input >>= next) state =
      (cost state.1 input : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        expectedWeightedIndexCharge key cap cost groups remaining (next result.1) result.2 := by
  cases input <;> rfl

theorem expectedWeightedIndexCharge_add {α : Type} (key : SecretKey) (cap : Nat)
    (first second : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedWeightedIndexCharge key cap (fun cache input => first cache input + second cache input) groups remaining computation state =
      expectedWeightedIndexCharge key cap first groups remaining computation state +
        expectedWeightedIndexCharge key cap second groups remaining computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedWeightedIndexCharge_query_bind, expectedWeightedIndexCharge_query_bind, expectedWeightedIndexCharge_query_bind]
      simp_rw [ih, Nat.cast_add, add_mul, mul_add, ENNReal.tsum_add]
      ac_rfl

theorem expectedWeightedIndexCharge_macro_eq {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedWeightedIndexCharge key cap (fun _ => signingMacroHashCost) groups remaining computation state =
      expectedMacroIndexCharge key cap groups remaining computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedWeightedIndexCharge_query_bind, expectedMacroIndexCharge_query_bind]
      simp_rw [ih]

noncomputable abbrev expectedTargetArrivalIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) : ENNReal :=
  expectedWeightedIndexCharge key cap (targetArrivalHashCost key.parameter) groups remaining computation state

noncomputable abbrev expectedUnusedTargetIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) : ENNReal :=
  expectedWeightedIndexCharge key cap (unusedTargetHashCost key.parameter) groups remaining computation state

theorem expectedTargetArrivalIndexCharge_add_unused {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedTargetArrivalIndexCharge key cap groups remaining computation state +
      expectedUnusedTargetIndexCharge key cap groups remaining computation state =
      expectedMacroIndexCharge key cap groups remaining computation state := by
  rw [expectedTargetArrivalIndexCharge, expectedUnusedTargetIndexCharge, ← expectedWeightedIndexCharge_add]
  simp_rw [targetArrivalHashCost_add_unused]
  exact expectedWeightedIndexCharge_macro_eq key cap groups remaining computation state

end SphincsSecurity.Concrete
