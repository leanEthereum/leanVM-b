import SphincsSecurity.Proof.JointProbeOriginalStructuralStep
import SphincsSecurity.Proof.JointProbeOriginalFailurePersistence
import SphincsSecurity.Proof.JointProbeOriginalFailureComparison
import SphincsSecurity.Proof.JointProbeOriginalComputed

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedBeforeFailureCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame cache hit failed =>
      (if failed then 0 else expectedPreExceptionCharge exception charge
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
        next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem expectedBeforeFailureCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (pure value) frame cache hit failed = 0 := rfl

theorem expectedBeforeFailureCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      (if failed then 0 else expectedPreExceptionCharge exception charge
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
        expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next result.1.2.1.1)
          result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

theorem expectedBeforeFailureCharge_le_preExceptionCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedPreExceptionCharge exception charge
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureCharge_query_bind, simulateQ_bind, simulateQ_spec_query, expectedPreExceptionCharge_bind]
      apply add_le_add
      · cases failed <;> simp
      · have hm := tsum_probOutput_map_mul
          (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed) Prod.fst
          (fun result => expectedPreExceptionCharge exception charge
            (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next result.2.1.1)) result.2.1.2 result.2.2)
        rw [stepWithFailure_project, step_expect_original exception parameter root otsTable ftsTable input frame cache hit
          (fun result => expectedPreExceptionCharge exception charge
            (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next result.1.1)) result.1.2 result.2)] at hm
        rw [hm]
        exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
          (ih result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2)

theorem expectedBeforeFailureCharge_failed_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable computation frame cache hit true = 0 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [expectedBeforeFailureCharge_query_bind, if_true, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit true)
      · rw [stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache hit result hr, ih, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem stepWithFailure_original_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (result) (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    result.1.2 ∈ support (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) := by
  have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input frame cache hit failed result hr
  have hm : result.1.2 ∈ support (evalDist (runExceptionMonitor exception
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit)) := by
    rw [← step_original exception parameter root otsTable ftsTable input frame cache hit, support_map]
    exact ⟨result.1, hp, rfl⟩
  exact (mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 hm)

theorem expected_survivingStructuralPotential_failed_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit true] *
      survivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hr : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit true)
  · simp only [runWithFailure_failed exception parameter root otsTable ftsTable computation frame cache hit result hr,
      survivingStructuralPotential, if_true, mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expected_survivingStructuralPotential_parent_stopped_le_one
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable computation none cache true false] *
      survivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤ 1 := by
  rw [runWithFailure_none, runExceptionMonitor_true, evalDist_map, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
  simp only [survivingStructuralPotential, Bool.false_eq_true, if_false, if_true, mul_one]
  exact tsum_probOutput_le_one

theorem expected_survivingStructuralPotential_run_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      computation (some frame) cache false false] *
      survivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
    structuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation (some frame) cache false false * (Fintype.card Digest : ENNReal)⁻¹ := by
  let exception := parentException parameter otsTable ftsTable
  let key := secretKey parameter root otsTable ftsTable
  let charge := signingStructuralCharge key
  let eps := (Fintype.card Digest : ENNReal)⁻¹
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value =>
      rw [runWithFailure_pure, tsum_probOutput_pure_mul]
      simp [survivingStructuralPotential]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      rw [runWithFailure_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
            (survivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2 +
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2 * eps) := by
          apply ENNReal.tsum_le_tsum
          intro head
          by_cases hs : head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)
          · apply mul_le_mul' le_rfl
            cases hf : head.2 with
            | true =>
                rw [expected_survivingStructuralPotential_failed_eq_zero]
                exact zero_le
            | false =>
                have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input (some frame) cache false false head hs
                have hv := stepWithFailure_invariant exception parameter root otsTable ftsTable input (some frame) cache false false
                  (fun live hlive => Option.some.inj hlive ▸ hvalid) (fun live hlive => Option.some.inj hlive ▸ hh) rfl head hs
                cases ho : head.1.2.2 with
                | true =>
                    have hn : head.1.1 = none := by simpa only [ho, Bool.true_or, Option.isNone_iff_eq_none] using hv.2
                    rw [hn]
                    exact (expected_survivingStructuralPotential_parent_stopped_le_one exception parameter root otsTable ftsTable
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
                        exact ih head.1.2.1.1 middle head.1.2.1.2 hfin hmiddle hnext hc
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
        _ = (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              survivingStructuralPotential key head.1.2.1.2 head.1.2.2 head.2) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps := by
          simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ (structuralRecordPotential key cache none +
              expectedPreExceptionCharge exception charge (expandedAdversaryImpl key input) cache false * eps) +
            (∑' head, Pr[= head | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] *
              expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next head.1.2.1.1)
                head.1.1 head.1.2.1.2 head.1.2.2 head.2) * eps :=
          add_le_add (expected_survivingStructuralPotential_step_le parameter root otsTable ftsTable input frame cache hfinite he hcomputed) le_rfl
        _ = _ := by
          simp only [expectedBeforeFailureCharge_query_bind, Bool.false_eq_true, if_false, add_mul]
          ac_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
