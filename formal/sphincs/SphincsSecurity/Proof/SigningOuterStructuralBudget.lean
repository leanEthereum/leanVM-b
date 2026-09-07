import SphincsSecurity.Proof.SigningStructuralBudget
import SphincsSecurity.Proof.MappedQueryCharge
import SphincsSecurity.Proof.JointProbeNonSecretStructuralBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expectedQueryCharge_expanded_le_add_outer
    (secretKey : SecretKey) (first second outer : QueryCache HashSpec → HashInput → ENNReal)
    (hhash : ∀ cache input, first cache input ≤ second cache input + outer cache input)
    (hsign : ∀ message cache, expectedQueryCharge first (sign secretKey message) cache ≤
      expectedQueryCharge second (sign secretKey message) cache)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedQueryCharge first (simulateQ (expandedAdversaryImpl secretKey) computation) cache ≤
      expectedQueryCharge second (simulateQ (expandedAdversaryImpl secretKey) computation) cache +
        expectedOuterQueryCharge secretKey outer computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [expectedOuterQueryCharge]
  | query_bind input next ih =>
      rw [expectedOuterQueryCharge_query_bind]
      cases input with
      | inl query =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inl, expectedQueryCharge_query_bind, expectedQueryCharge_query_bind]
          have hhead : hashQueryCharge first cache query ≤
              hashQueryCharge second cache query + hashQueryCharge outer cache query := by
            cases query with
            | inl sample => simp [hashQueryCharge]
            | inr input => exact hhash cache input
          calc
            _ ≤ (hashQueryCharge second cache query + hashQueryCharge outer cache query) +
                ∑' result, Pr[= result | (romImpl query).run cache] *
                  (expectedQueryCharge second (simulateQ (expandedAdversaryImpl secretKey) (next result.1)) result.2 +
                    expectedOuterQueryCharge secretKey outer (next result.1) result.2) :=
              add_le_add hhead (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2))
            _ = _ := by
              simp_rw [mul_add, ENNReal.tsum_add]
              cases query <;> simp only [outerHashQueryCharge, unloggedMappedAdversaryImpl] <;> ac_rfl
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr, expectedQueryCharge_bind, expectedQueryCharge_bind]
          calc
            _ ≤ expectedQueryCharge second (sign secretKey message) cache +
                ∑' result, Pr[= result | (simulateQ romImpl (sign secretKey message)).run cache] *
                  (expectedQueryCharge second (simulateQ (expandedAdversaryImpl secretKey) (next result.1)) result.2 +
                    expectedOuterQueryCharge secretKey outer (next result.1) result.2) :=
              add_le_add (hsign message cache) (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2))
            _ = _ := by
              simp_rw [mul_add, ENNReal.tsum_add]
              simp only [outerHashQueryCharge, zero_add]
              ac_rfl

theorem expectedStructuralCharge_expanded_le_hashQueries_add_outerNonSecret
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey) (simulateQ (expandedAdversaryImpl secretKey) computation) cache ≤
      expectedQueryCharge (fun _ _ => 1) (simulateQ (expandedAdversaryImpl secretKey) computation) cache +
        expectedOuterQueryCharge secretKey (fun _ input =>
          if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0) computation cache := by
  apply expectedQueryCharge_expanded_le_add_outer
  · exact parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret secretKey
  · exact expectedQueryCharge_sign_le_hashQueries secretKey

theorem expectedPreParentStructuralCharge_expanded_le_hashQueries_add_outerNonSecret
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        (signingStructuralCharge secretKey) (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit ≤
      expectedQueryCharge (fun _ _ => 1) (simulateQ (expandedAdversaryImpl secretKey) computation) cache +
        expectedOuterQueryCharge secretKey (fun _ input =>
          if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0) computation cache :=
  (expectedPreExceptionCharge_le_queryCharge _ _ _ cache hit).trans
    (expectedStructuralCharge_expanded_le_hashQueries_add_outerNonSecret secretKey computation cache)

end SphincsSecurity.Concrete
