import SphincsSecurity.Proof.FirstExceptionSelectedBind
import SphincsSecurity.Proof.DeficitStructuralStep
import SphincsSecurity.Proof.JointProbeCollisionBeforeFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)

theorem firstExceptionSelectedProbability_expanded_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (selected : ExceptionRecord → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool) :
    firstExceptionSelectedProbability exception selected
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (OracleSpec.query input >>= next)) cache =
      firstExceptionSelectedProbability exception selected (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache false failed] *
          (if result.1.2.2 then 0 else firstExceptionSelectedProbability exception selected
            (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next result.1.2.1.1)) result.1.2.1.2) := by
  rw [simulateQ_bind, simulateQ_spec_query, firstExceptionSelectedProbability_bind]
  congr 1
  let cost := fun result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool =>
    if result.2 then 0 else firstExceptionSelectedProbability exception selected
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next result.1.1)) result.1.2
  have hm := tsum_probOutput_map_mul
    (stepWithFailure exception parameter root otsTable ftsTable input frame cache false failed) Prod.fst (fun result => cost result.2)
  rw [stepWithFailure_project, step_expect_original exception parameter root otsTable ftsTable input frame cache false cost] at hm
  exact hm

theorem expected_deficitCollisionSurvivingStructuralPotential_run_le_record
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache) :
    (∑' result, Pr[= result | runWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
        parameter root otsTable ftsTable computation (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedBeforeFailureCharge
          (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
          (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          parameter root otsTable ftsTable computation (some frame) cache false false * (Fintype.card Digest : ENNReal)⁻¹ +
        firstExceptionSelectedProbability
          (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
          (fun record => MessageHashInput parameter record.input)
          (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache := by
  let key := secretKey parameter root otsTable ftsTable
  let exception := deficitStoppingException key (parentException parameter otsTable ftsTable)
  let charge := collisionSigningStructuralCharge key
  let eps := (Fintype.card Digest : ENNReal)⁻¹
  let selected := fun record : ExceptionRecord => MessageHashInput parameter record.input
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value =>
      rw [runWithFailure_pure, tsum_probOutput_pure_mul]
      simp [collisionSurvivingStructuralPotential]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      rw [runWithFailure_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
            (collisionSurvivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2 +
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2 * eps +
              if head.1.2.2 then 0 else firstExceptionSelectedProbability exception selected
                (simulateQ (expandedAdversaryImpl key) (next head.1.2.1.1)) head.1.2.1.2) := by
          apply ENNReal.tsum_le_tsum
          intro head
          by_cases hs : head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)
          · apply mul_le_mul' le_rfl
            cases hf : head.2 with
            | true =>
                rw [expected_collisionSurvivingStructuralPotential_failed_eq_zero]
                exact zero_le
            | false =>
                have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input (some frame) cache false false head hs
                have hv := stepWithFailure_invariant exception parameter root otsTable ftsTable input (some frame) cache false false
                  (fun live hlive => Option.some.inj hlive ▸ hvalid) (fun live hlive => Option.some.inj hlive ▸ hh) rfl head hs
                cases ho : head.1.2.2 with
                | true =>
                    have hn : head.1.1 = none := by simpa only [ho, Bool.true_or, Option.isNone_iff_eq_none] using hv.2
                    rw [hn]
                    apply (expected_collisionSurvivingStructuralPotential_parent_stopped_le_one exception parameter root otsTable ftsTable
                      (next head.1.2.1.1) head.1.2.1.2).trans
                    simp only [collisionSurvivingStructuralPotential, if_true, Bool.false_eq_true, if_false, add_zero]
                    exact le_self_add
                | false =>
                    cases hm : head.1.1 with
                    | none => simp [hm, ho, hf] at hv
                    | some middle =>
                        have hmiddle := (step_valid exception parameter root otsTable ftsTable input (some frame) cache false head.1 hp middle hm).1
                        have hnext := step_queryBound exception parameter root otsTable ftsTable input next frame cache false hbound head.1 hp middle hm
                        have hc := step_computed exception parameter root otsTable ftsTable input frame cache false hcomputed head.1 hp middle hm
                        have ha := stepWithFailure_original_support exception parameter root otsTable ftsTable input (some frame) cache false false head hs
                        have hfin := finite_cache_of_mem_support _ cache head.1.2.1.1 head.1.2.1.2
                          (runExceptionMonitor_support_project exception _ cache false ha) hfinite
                        have hcleanNext := stepWithFailure_deficit_clean exception parameter root otsTable ftsTable
                          (fun _ _ _ h => Or.inr h) input (some frame) cache false false (fun _ => hclean) head hs ho
                        exact ih head.1.2.1.1 middle head.1.2.1.2 hfin hmiddle hnext hc hcleanNext
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
        _ = (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              collisionSurvivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps +
            ∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              (if head.1.2.2 then 0 else firstExceptionSelectedProbability exception selected
                (simulateQ (expandedAdversaryImpl key) (next head.1.2.1.1)) head.1.2.1.2) := by
          simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ (collisionStructuralRecordPotential key cache none +
              expectedPreExceptionCharge exception charge (expandedAdversaryImpl key input) cache false * eps +
              firstExceptionSelectedProbability exception selected (expandedAdversaryImpl key input) cache) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps +
            ∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              (if head.1.2.2 then 0 else firstExceptionSelectedProbability exception selected
                (simulateQ (expandedAdversaryImpl key) (next head.1.2.1.1)) head.1.2.1.2) :=
          add_le_add (add_le_add (expected_deficitCollisionSurvivingStructuralPotential_step_le
            parameter root otsTable ftsTable input frame cache hfinite hclean he hcomputed) le_rfl) le_rfl
        _ = _ := by
          rw [firstExceptionSelectedProbability_expanded_query_bind _ _ parameter root otsTable ftsTable input next (some frame) cache false]
          simp only [expectedBeforeFailureCharge_query_bind, Bool.false_eq_true, if_false, add_mul]
          ac_rfl

theorem expected_deficitCollisionSurvivingStructuralPotential_run_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hhash : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) q)
    (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none) :
    (∑' result, Pr[= result | runWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
        parameter root otsTable ftsTable computation (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedBeforeFailureCharge
          (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
          (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          parameter root otsTable ftsTable computation (some frame) cache false false * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / 2 ^ 223 := by
  let key := secretKey parameter root otsTable ftsTable
  have h := expected_deficitCollisionSurvivingStructuralPotential_run_le_record parameter root otsTable ftsTable
    computation frame cache hfinite hvalid hbound hcomputed (messageDeficitExceptional_not_of_no_inputs key cache hnone)
  have hrare := probEvent_firstDeficitMessageRecord_le key (parentException parameter otsTable ftsTable)
    (fun _ _ _ h => h.2) (simulateQ (expandedAdversaryImpl key) computation) q hhash hq cache hfinite hnone
  exact h.trans (add_le_add le_rfl hrare)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
