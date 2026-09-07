import SphincsSecurity.Proof.PreExceptionChargeComparison
import SphincsSecurity.Proof.MappedQueryCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedPreExceptionOuterCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : QueryCache HashSpec → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ => 0)
    (fun input _ next cache hit =>
      (if hit then 0 else outerHashQueryCharge charge input cache) +
        ∑' result, Pr[= result | runExceptionMonitor exception (expandedAdversaryImpl secretKey input) cache hit] *
          next result.1.1 result.1.2 result.2) computation

@[simp] theorem expectedPreExceptionOuterCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (value : α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception secretKey charge (pure value) cache hit = 0 := rfl

theorem expectedPreExceptionOuterCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception secretKey charge (OracleSpec.query input >>= next) cache hit =
      (if hit then 0 else outerHashQueryCharge charge input cache) +
        ∑' result, Pr[= result | runExceptionMonitor exception (expandedAdversaryImpl secretKey input) cache hit] *
          expectedPreExceptionOuterCharge exception secretKey charge (next result.1.1) result.1.2 result.2 := rfl

@[simp] theorem expectedPreExceptionOuterCharge_true
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedPreExceptionOuterCharge exception secretKey charge computation cache true = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedPreExceptionOuterCharge_query_bind, runExceptionMonitor_true, tsum_probOutput_map_mul]
      simp only [if_true, ih, mul_zero, tsum_zero, zero_add]

theorem expectedPreExceptionOuterCharge_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception secretKey charge (computation >>= next) cache hit =
      expectedPreExceptionOuterCharge exception secretKey charge computation cache hit +
        ∑' result, Pr[= result | runExceptionMonitor exception
          (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit] *
          expectedPreExceptionOuterCharge exception secretKey charge (next result.1.1) result.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind input continuation ih =>
      rw [bind_assoc, expectedPreExceptionOuterCharge_query_bind, expectedPreExceptionOuterCharge_query_bind,
        simulateQ_bind, simulateQ_spec_query, runExceptionMonitor_bind, tsum_probOutput_bind_mul]
      simp_rw [ih, mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      rw [add_assoc]

theorem expectedPreExceptionCharge_expanded_le_add_outer
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (first second outer : QueryCache HashSpec → HashInput → ENNReal)
    (hhash : ∀ cache input, first cache input ≤ second cache input + outer cache input)
    (hsign : ∀ message cache hit, expectedPreExceptionCharge exception first (sign secretKey message) cache hit ≤
      expectedPreExceptionCharge exception second (sign secretKey message) cache hit)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception first (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit ≤
      expectedPreExceptionCharge exception second (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit +
        expectedPreExceptionOuterCharge exception secretKey outer computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind,
        expectedPreExceptionOuterCharge_query_bind]
      have hhead : expectedPreExceptionCharge exception first (expandedAdversaryImpl secretKey input) cache hit ≤
          expectedPreExceptionCharge exception second (expandedAdversaryImpl secretKey input) cache hit +
            if hit then 0 else outerHashQueryCharge outer input cache := by
        cases input with
        | inl query =>
            change expectedPreExceptionCharge exception first (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache hit ≤
              expectedPreExceptionCharge exception second (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache hit +
                if hit then 0 else hashQueryCharge outer cache query
            rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
            cases hit with
            | true => simp
            | false =>
                cases query with
                | inl sample => simp [hashQueryCharge]
                | inr input => exact hhash cache input
        | inr message =>
            simpa only [expandedAdversaryImpl, outerHashQueryCharge, ite_self, add_zero, scheme] using hsign message cache hit
      calc
        _ ≤ (expectedPreExceptionCharge exception second (expandedAdversaryImpl secretKey input) cache hit +
              if hit then 0 else outerHashQueryCharge outer input cache) +
            ∑' result, Pr[= result | runExceptionMonitor exception (expandedAdversaryImpl secretKey input) cache hit] *
              (expectedPreExceptionCharge exception second (simulateQ (expandedAdversaryImpl secretKey) (next result.1.1)) result.1.2 result.2 +
                expectedPreExceptionOuterCharge exception secretKey outer (next result.1.1) result.1.2 result.2) :=
          add_le_add hhead (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1.1 result.1.2 result.2))
        _ = _ := by simp_rw [mul_add, ENNReal.tsum_add]; ac_rfl

end SphincsSecurity.Concrete
