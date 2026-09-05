import SphincsSecurity.Proof.RomQueryChargeBind
import SphincsSecurity.Proof.DirectQueryBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def outerHashQueryCharge (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  match input with
  | .inl query => hashQueryCharge charge cache query
  | .inr _ => 0

noncomputable def expectedOuterQueryCharge
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : QueryCache HashSpec → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next cache => outerHashQueryCharge charge input cache +
      ∑' result, Pr[= result | (unloggedMappedAdversaryImpl secretKey input).run cache] *
        next result.1 result.2) computation

theorem expectedOuterQueryCharge_query_bind
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    expectedOuterQueryCharge secretKey charge (OracleSpec.query input >>= next) cache =
      outerHashQueryCharge charge input cache +
        ∑' result, Pr[= result | (unloggedMappedAdversaryImpl secretKey input).run cache] *
          expectedOuterQueryCharge secretKey charge (next result.1) result.2 := rfl

theorem expectedOuterQueryCharge_le_expanded
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedOuterQueryCharge secretKey charge computation cache ≤
      expectedQueryCharge charge (simulateQ (expandedAdversaryImpl secretKey) computation) cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [expectedOuterQueryCharge]
  | query_bind input next ih =>
      rw [expectedOuterQueryCharge_query_bind]
      cases input with
      | inl query =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inl, expectedQueryCharge_query_bind]
          apply add_le_add le_rfl
          exact ENNReal.tsum_le_tsum (fun result => mul_le_mul' le_rfl (ih result.1 result.2))
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr, expectedQueryCharge_bind]
          apply add_le_add (bot_le : (0 : ℝ≥0∞) ≤ _)
          exact ENNReal.tsum_le_tsum (fun result => mul_le_mul' le_rfl (ih result.1 result.2))

end SphincsSecurity.Concrete
