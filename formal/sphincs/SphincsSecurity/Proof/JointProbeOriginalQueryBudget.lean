import SphincsSecurity.Proof.JointProbeOriginalQueryCoupling
import SphincsSecurity.Proof.SigningStoppedStructuralBudget
import SphincsSecurity.Proof.JointProbeNonSecretStructuralBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem preStructural_add_jointProbe_le_preHash_add_outerHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (actualCache : QueryCache HashSpec) (hit : Bool)
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache)
    (state : AdaptiveRevealProbe.State FtsProbeSimulation.Coordinate) (ftsCache : FtsProbeSimulation.SplitHashCache) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey) (expandedAdversaryImpl secretKey input) actualCache hit +
        (if hit then 0 else FtsProbeSimulation.jointOtsQueryCharge secretKey.parameter input context cache state ftsCache +
          FtsProbeSimulation.jointFtsQueryCharge secretKey.parameter input context cache state ftsCache) ≤
      expectedPreExceptionCharge exception (fun _ _ => 1) (expandedAdversaryImpl secretKey input) actualCache hit +
        if hit then 0 else if OtsProbeSimulation.IsOuterHash input then 1 else 0 := by
  cases hit with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true, if_false]
      cases input with
      | inl query =>
          change expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) actualCache false + _ ≤
            expectedPreExceptionCharge exception (fun _ _ => 1)
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) actualCache false + _
          rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
          cases query with
          | inl sample =>
              simp [hashQueryCharge, FtsProbeSimulation.jointOtsQueryCharge, FtsProbeSimulation.jointFtsQueryCharge,
                OtsProbeSimulation.IsOuterHash]
          | inr input =>
              simpa only [hashQueryCharge, Sum.elim_inr, Bool.false_eq_true, if_false, OtsProbeSimulation.IsOuterHash,
                if_true, show (1 : ENNReal) + 1 = 2 by norm_num, signingStructuralCharge] using
                parentStoppedEncoding_ftsParent_jointProbe_queryCharge_le_two secretKey actualCache input context cache state ftsCache
      | inr message =>
          simpa only [expandedAdversaryImpl, scheme, FtsProbeSimulation.jointOtsQueryCharge, FtsProbeSimulation.jointFtsQueryCharge,
            zero_add, add_zero, OtsProbeSimulation.IsOuterHash, if_false] using
            expectedPreExceptionCharge_sign_le_preHashQueries exception secretKey message actualCache false

theorem preStructural_add_jointProbe_le_two_preHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (actualCache : QueryCache HashSpec) (hit : Bool)
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache)
    (state : AdaptiveRevealProbe.State FtsProbeSimulation.Coordinate) (ftsCache : FtsProbeSimulation.SplitHashCache) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey) (expandedAdversaryImpl secretKey input) actualCache hit +
        (if hit then 0 else FtsProbeSimulation.jointOtsQueryCharge secretKey.parameter input context cache state ftsCache +
          FtsProbeSimulation.jointFtsQueryCharge secretKey.parameter input context cache state ftsCache) ≤
      2 * expectedPreExceptionCharge exception (fun _ _ => 1) (expandedAdversaryImpl secretKey input) actualCache hit := by
  apply (preStructural_add_jointProbe_le_preHash_add_outerHash exception secretKey input actualCache hit context cache state ftsCache).trans
  rw [two_mul]
  apply add_le_add le_rfl
  cases hit with
  | true => simp
  | false =>
      cases input with
      | inl query =>
          change (if OtsProbeSimulation.IsOuterHash (.inl query) then (1 : ENNReal) else 0) ≤
            expectedPreExceptionCharge exception (fun _ _ => 1)
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) actualCache false
          rw [expectedPreExceptionCharge_query]
          cases query <;> simp [hashQueryCharge, OtsProbeSimulation.IsOuterHash]
      | inr message => exact bot_le

end SphincsSecurity.Concrete
