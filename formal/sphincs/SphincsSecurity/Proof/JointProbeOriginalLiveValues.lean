import SphincsSecurity.Proof.JointProbeOriginalFailureComparison
import SphincsSecurity.Proof.JointProbeOriginalFailurePersistence

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointReturned (event : α → Prop)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α))) : Prop :=
  ∃ entry, cleanJointResolved result = some entry ∧ event entry.value

namespace JointOriginal

theorem probEvent_runWithFailure_live_failed_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (event : α → Prop)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    Pr[fun result => event result.1.2.1.1 ∧ result.1.2.2 = false ∧ result.2 = false |
      runWithFailure exception parameter root otsTable ftsTable computation frame cache hit true] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro result hr he
  have hf := runWithFailure_failed exception parameter root otsTable ftsTable computation frame cache hit result hr
  simp [hf] at he

theorem probEvent_runWithFailure_live_value_le_fullShared
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (event : α → Prop) (frame : Frame) (cache : QueryCache HashSpec)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel) :
    Pr[fun result => event result.1.2.1.1 ∧ result.1.2.2 = false ∧ result.2 = false |
      runWithFailure exception parameter root otsTable ftsTable computation (some frame) cache false false] ≤
    Pr[JointReturned (fun value => event value.1) | AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceComputation parameter root computation).run frame.cache) frame.context frame.fuel otsTable)] := by
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value =>
      have hbody : (jointSourceComputation parameter root (pure value)).run frame.cache =
          pure (value, prepareNativeCache frame.cache.2 frame.cache.1,
            withNativeOrdinaryCache frame.cache.2 (prepareNativeCache frame.cache.2 frame.cache.1)) := rfl
      rw [hbody, runJointResolved_pure]
      simp [runWithFailure_pure, AdaptiveRevealProbe.runDetailed,
        hvalid.1, JointReturned, cleanJointResolved]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      rw [runWithFailure_query_bind, stepWithFailure, dif_pos he, probEvent_bind_eq_tsum, tsum_probOutput_map_mul]
      change _ ≤ Pr[JointReturned (fun value => event value.1) | AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input >>= fun reply =>
          jointSourceComputation parameter root (next reply)).run frame.cache) frame.context frame.fuel otsTable)]
      rw [runDetailed_jointSourceOuterQuery_bind (hhash := hh), probEvent_bind_eq_tsum]
      let continuation := fun reply => jointSourceComputation parameter root (next reply)
      calc
        _ ≤ ∑' raw, Pr[= raw | (queryCoupling exception parameter root otsTable ftsTable input frame cache false he).1] *
            Pr[JointReturned (fun value => event value.1) |
              resumeJointResolved ftsTable (remainingFtsFuel parameter input frame.ftsFuel) continuation raw.1] := by
          apply ENNReal.tsum_le_tsum
          intro raw
          by_cases hr : raw ∈ support (queryCoupling exception parameter root otsTable ftsTable input frame cache false he).1
          · apply mul_le_mul' le_rfl
            have hs := queryCoupling_support exception parameter root otsTable ftsTable input frame cache false he raw hr
            dsimp only
            cases hf : resume parameter otsTable input frame.ftsFuel raw.1 with
            | none =>
                simp only [Option.isNone_none, Bool.or_true]
                rw [probEvent_runWithFailure_live_failed_eq_zero]
                exact zero_le
            | some middle =>
                rw [resumeJointResolved_eq_of_jointOriginalResume parameter root otsTable ftsTable input continuation frame middle raw.2.1
                  hvalid.1 hvalid.2.1 raw.1 hs.2.1 hs.1 hf]
                simp only [Bool.false_or, Option.isNone_some]
                cases hm : raw.2.2 with
                | true => simp [runWithFailure_none, runExceptionMonitor_true, Function.comp_def]
                | false =>
                    simp only [Bool.false_eq_true, if_false]
                    have hstep : (some middle, raw.2) ∈ support
                        (step exception parameter root otsTable ftsTable input (some frame) cache false) := by
                      rw [step, dif_pos he, support_map]
                      exact ⟨raw, hr, by simp [hm, hf]⟩
                    have hmiddle := (step_valid exception parameter root otsTable ftsTable input (some frame) cache false
                      (some middle, raw.2) hstep middle rfl).1
                    have hnext := step_queryBound exception parameter root otsTable ftsTable input next frame cache false
                      hbound (some middle, raw.2) hstep middle rfl
                    exact ih raw.2.1.1 middle raw.2.1.2 hmiddle hnext
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          have hm := tsum_probOutput_map_mul
            (queryCoupling exception parameter root otsTable ftsTable input frame cache false he).1 Prod.fst
            (fun result => Pr[JointReturned (fun value => event value.1) |
              resumeJointResolved ftsTable (remainingFtsFuel parameter input frame.ftsFuel) continuation result])
          rw [(queryCoupling exception parameter root otsTable ftsTable input frame cache false he).2.map_fst] at hm
          exact hm.symm

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
