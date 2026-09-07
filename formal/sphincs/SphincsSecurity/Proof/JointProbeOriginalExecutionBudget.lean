import SphincsSecurity.Proof.JointProbeOriginalExecution
import SphincsSecurity.Proof.JointProbeOriginalQueryBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def probeCharge
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) : ENNReal :=
  match frame with
  | none => 0
  | some frame =>
      if frame.Enabled parameter otsTable ftsTable input cache hit then
        jointOtsQueryCharge parameter input frame.context frame.cache.1 frame.state frame.cache.2 +
          jointFtsQueryCharge parameter input frame.context frame.cache.1 frame.state frame.cache.2
      else 0

noncomputable def expectedProbeCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Option Frame → QueryCache HashSpec → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next frame cache hit =>
      probeCharge parameter otsTable ftsTable input frame cache hit +
        ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
          next pair.2.1.1 pair.1 pair.2.1.2 pair.2.2) computation

@[simp] theorem expectedProbeCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedProbeCharge exception parameter root otsTable ftsTable (pure value) frame cache hit = 0 := rfl

theorem expectedProbeCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedProbeCharge exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit =
      probeCharge parameter otsTable ftsTable input frame cache hit +
        ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
          expectedProbeCharge exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2 := rfl

@[simp] theorem expectedProbeCharge_none
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedProbeCharge exception parameter root otsTable ftsTable computation none cache hit = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind, step, tsum_probOutput_map_mul]
      simp only [probeCharge, ih, mul_zero, tsum_zero, zero_add]

@[simp] theorem expectedProbeCharge_true
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) :
    expectedProbeCharge exception parameter root otsTable ftsTable computation frame cache true = 0 := by
  cases computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next =>
      cases frame with
      | none => exact expectedProbeCharge_none exception parameter root otsTable ftsTable _ cache true
      | some frame =>
          have hdisabled : ¬ frame.Enabled parameter otsTable ftsTable input cache true := fun h => Bool.noConfusion h.1
          rw [expectedProbeCharge_query_bind, probeCharge, if_neg hdisabled, step, dif_neg hdisabled, tsum_probOutput_map_mul]
          simp only [expectedProbeCharge_none, mul_zero, tsum_zero, zero_add]

theorem expectedProbeCharge_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedProbeCharge exception parameter root otsTable ftsTable (computation >>= next) frame cache hit =
      expectedProbeCharge exception parameter root otsTable ftsTable computation frame cache hit +
        ∑' pair, Pr[= pair | run exception parameter root otsTable ftsTable computation frame cache hit] *
          expectedProbeCharge exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value =>
      rw [pure_bind, expectedProbeCharge_pure, run_pure, tsum_probOutput_pure_mul, zero_add]
  | query_bind input continuation ih =>
      rw [bind_assoc, expectedProbeCharge_query_bind, expectedProbeCharge_query_bind,
        run_query_bind, tsum_probOutput_bind_mul]
      simp_rw [ih, mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      rw [add_assoc]

theorem step_expect_original
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (cost : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool → ENNReal) :
    (∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] * cost pair.2) =
      ∑' result, Pr[= result | runExceptionMonitor exception
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit] * cost result := by
  rw [← tsum_probOutput_map_mul, step_original]
  rfl

private theorem preStructural_query_le_two_preHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge key) (expandedAdversaryImpl key input) cache hit ≤
      2 * expectedPreExceptionCharge exception (fun _ _ => 1) (expandedAdversaryImpl key input) cache hit := by
  cases hit with
  | true => simp
  | false =>
      cases input with
      | inl query =>
          change expectedPreExceptionCharge exception (signingStructuralCharge key)
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache false ≤
            2 * expectedPreExceptionCharge exception (fun _ _ => 1)
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache false
          rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
          cases query with
          | inl sample => simp [hashQueryCharge]
          | inr input =>
              simpa only [hashQueryCharge, Sum.elim_inr, Bool.false_eq_true, if_false, mul_one, signingStructuralCharge] using
                (le_self_add.trans (answerEncoding_parent_ots_fts_queryCharge_le_two key cache input))
      | inr message =>
          apply (expectedPreExceptionCharge_sign_le_preHashQueries exception key message cache false).trans
          rw [two_mul]
          exact le_self_add

theorem preStructural_add_probeCharge_le_two_preHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit +
      probeCharge parameter otsTable ftsTable input frame cache hit ≤
      2 * expectedPreExceptionCharge exception (fun _ _ => 1)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit := by
  cases frame with
  | none =>
      simpa only [probeCharge, add_zero] using
        preStructural_query_le_two_preHash exception (secretKey parameter root otsTable ftsTable) input cache hit
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
      · rw [probeCharge, if_pos h]
        simpa only [h.1, Bool.false_eq_true, if_false, secretKey] using
          preStructural_add_jointProbe_le_two_preHash exception (secretKey parameter root otsTable ftsTable) input cache hit
            frame.context frame.cache.1 frame.state frame.cache.2
      · simpa only [probeCharge, if_neg h, add_zero] using
          preStructural_query_le_two_preHash exception (secretKey parameter root otsTable ftsTable) input cache hit

theorem preStructural_add_expectedProbeCharge_le_two_preHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit +
      expectedProbeCharge exception parameter root otsTable ftsTable computation frame cache hit ≤
      2 * expectedPreExceptionCharge exception (fun _ _ => 1)
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind,
        expectedProbeCharge_query_bind]
      rw [← step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => expectedPreExceptionCharge exception (signingStructuralCharge key)
          (simulateQ (expandedAdversaryImpl key) (next result.1.1)) result.1.2 result.2)]
      rw [← step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => expectedPreExceptionCharge exception (fun _ _ => 1)
          (simulateQ (expandedAdversaryImpl key) (next result.1.1)) result.1.2 result.2)]
      calc
        _ = (expectedPreExceptionCharge exception (signingStructuralCharge key) (expandedAdversaryImpl key input) cache hit +
              probeCharge parameter otsTable ftsTable input frame cache hit) +
            ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
              (expectedPreExceptionCharge exception (signingStructuralCharge key)
                (simulateQ (expandedAdversaryImpl key) (next pair.2.1.1)) pair.2.1.2 pair.2.2 +
                expectedProbeCharge exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2) := by
                  simp_rw [mul_add, ENNReal.tsum_add]
                  ac_rfl
        _ ≤ 2 * expectedPreExceptionCharge exception (fun _ _ => 1) (expandedAdversaryImpl key input) cache hit +
            ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
              (2 * expectedPreExceptionCharge exception (fun _ _ => 1)
                (simulateQ (expandedAdversaryImpl key) (next pair.2.1.1)) pair.2.1.2 pair.2.2) :=
          add_le_add (preStructural_add_probeCharge_le_two_preHash exception parameter root otsTable ftsTable input frame cache hit)
            (ENNReal.tsum_le_tsum fun pair => mul_le_mul' le_rfl (ih pair.2.1.1 pair.1 pair.2.1.2 pair.2.2))
        _ = _ := by
          simp_rw [mul_left_comm _ (2 : ENNReal)]
          rw [ENNReal.tsum_mul_left, mul_add]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
