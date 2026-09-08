import SphincsSecurity.Proof.DoubleSharedParentRefundStep
import SphincsSecurity.Proof.JointFailureCacheCap
import SphincsSecurity.Proof.SharedFailureDiscardStopped
import SphincsSecurity.Proof.JointProbeCollisionBeforeFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_collisionPotential_add_twice_sharedParentDiscard_run_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hcap : ∀ result ∈ support (runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      computation (some frame) cache false false), QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    (∑' result, Pr[= result | runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      computation (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) +
      expectedSharedFailureDiscard (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation (some frame) cache false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          parameter root otsTable ftsTable computation (some frame) cache false false * (Fintype.card Digest : ENNReal)⁻¹ := by
  let exception := parentException parameter otsTable ftsTable
  let key := secretKey parameter root otsTable ftsTable
  let charge := collisionSigningStructuralCharge key
  let reserve := survivingFtsParentReserve key
  let eps := (Fintype.card Digest : ENNReal)⁻¹
  let refund := 2 * eps
  have hreserve : ∀ current, reserve current true = 0 := fun _ => rfl
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value =>
      rw [runWithFailure_pure, tsum_probOutput_pure_mul]
      simp [collisionSurvivingStructuralPotential]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      have htail := runWithFailure_tail_cache_cap exception parameter root otsTable ftsTable input next (some frame) cache false false
        (Fintype.card Digest : ENNReal) hcap
      have hstep : ∀ head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false),
          QueryCache.enncard head.1.2.1.2 ≤ (Fintype.card Digest : ENNReal) := by
        intro head hs
        exact runWithFailure_initial_cache_cap exception parameter root otsTable ftsTable (next head.1.2.1.1)
          head.1.1 head.1.2.1.2 head.1.2.2 head.2 (Fintype.card Digest : ENNReal) (htail head hs)
      rw [runWithFailure_query_bind, tsum_probOutput_bind_mul, expectedSharedFailureDiscard_query_bind, add_mul]
      calc
        _ = (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
            ((∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2] * collisionSurvivingStructuralPotential key result.1.2.1.2 result.1.2.2 result.2) +
              expectedSharedFailureDiscard exception reserve parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2 * refund)) +
            sharedFailureDiscardStep exception reserve parameter root otsTable ftsTable input (some frame) cache false false * refund := by
          dsimp only [refund, eps]
          simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
          ac_rfl
        _ ≤ (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
            (collisionSurvivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2 +
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2 * eps)) +
            sharedFailureDiscardStep exception reserve parameter root otsTable ftsTable input (some frame) cache false false * refund := by
          apply add_le_add _ le_rfl
          apply ENNReal.tsum_le_tsum
          intro head
          by_cases hs : head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)
          · apply mul_le_mul' le_rfl
            cases hf : head.2 with
            | true =>
                rw [expected_collisionSurvivingStructuralPotential_failed_eq_zero, expectedSharedFailureDiscard_failed_eq_zero, zero_mul, zero_add]
                exact zero_le
            | false =>
                have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input (some frame) cache false false head hs
                have hv := stepWithFailure_invariant exception parameter root otsTable ftsTable input (some frame) cache false false
                  (fun live hlive => Option.some.inj hlive ▸ hvalid) (fun live hlive => Option.some.inj hlive ▸ hh) rfl head hs
                cases ho : head.1.2.2 with
                | true =>
                    have hn : head.1.1 = none := by simpa only [ho, Bool.true_or, Option.isNone_iff_eq_none] using hv.2
                    rw [hn, expectedSharedFailureDiscard_hit_eq_zero exception reserve hreserve, zero_mul, add_zero]
                    exact (expected_collisionSurvivingStructuralPotential_parent_stopped_le_one exception parameter root otsTable ftsTable
                      (next head.1.2.1.1) head.1.2.1.2).trans le_self_add
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
                        have hnextcap := htail head hs
                        rw [hm, ho, hf] at hnextcap
                        exact ih head.1.2.1.1 middle head.1.2.1.2 hfin hmiddle hnext hc hnextcap
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
        _ = ((∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              collisionSurvivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2) +
            sharedFailureDiscardStep exception reserve parameter root otsTable ftsTable input (some frame) cache false false * refund) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps := by
          dsimp only [refund, eps]
          simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
          ac_rfl
        _ ≤ (collisionStructuralRecordPotential key cache none +
            expectedPreExceptionCharge exception charge (expandedAdversaryImpl key input) cache false * eps) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps :=
          add_le_add (expected_collisionPotential_add_twice_sharedParentDiscard_step_le parameter root otsTable ftsTable input frame cache hfinite he hcomputed hstep) le_rfl
        _ = _ := by
          simp only [expectedBeforeFailureCharge_query_bind, Bool.false_eq_true, if_false, add_mul]
          ac_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
