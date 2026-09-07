import SphincsSecurity.Proof.JointProbeFailurePersistence
import SphincsSecurity.Proof.JointProbeOriginalFailureMonitor

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resume_none_iff_jointCompletionFailure
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame)
    (hconsistent : frame.context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees frame.context.state otsTable)
    (result) (hresult : result ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable))) :
    resume parameter otsTable input frame.ftsFuel result = none ↔ JointCompletionFailure result := by
  cases result with
  | stopped hit => simp [resume, JointCompletionFailure, cleanJointResolved]
  | done hit state entry =>
      cases hit with
      | true => simp [resume, JointCompletionFailure, cleanJointResolved]
      | false =>
          cases entry with
          | none => simp [resume, JointCompletionFailure, cleanJointResolved]
          | some entry =>
              have hf := resolvedFacts_of_mem_jointDetailed ftsTable _ frame.state state frame.ftsFuel frame.context frame.fuel otsTable entry
                hconsistent hstarts hresult
              simp [resume, JointCompletionFailure, cleanJointResolved, hf.1]

theorem resumeJointResolved_eq_of_jointOriginalResume
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → JointSource α)
    (frame finalFrame : Frame) (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hclean : AdaptiveRevealProbe.tableHits frame.state ftsTable = false)
    (hsynced : RevealedSynced parameter ftsTable frame.state frame.cache.2)
    (result) (hresult : result ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)))
    (hrel : JointOriginalRunRel parameter otsTable ftsTable result actual)
    (hresume : resume parameter otsTable input frame.ftsFuel result = some finalFrame) :
    resumeJointResolved ftsTable (remainingFtsFuel parameter input frame.ftsFuel) next result =
      AdaptiveRevealProbe.runDetailed ftsTable finalFrame.state finalFrame.ftsFuel
        (runJointResolved ((next actual.1).run finalFrame.cache) finalFrame.context finalFrame.fuel otsTable) := by
  cases result with
  | stopped hit => simp [resume] at hresume
  | done hit state entry =>
      cases hit with
      | true => simp [resume] at hresume
      | false =>
          cases entry with
          | none => simp [resume] at hresume
          | some entry =>
              by_cases hc : OtsProbeSimulation.DeferredCompletable otsTable entry.context
              · simp only [resume, if_pos hc, Option.some.injEq] at hresume
                subst finalFrame
                have hi := jointOriginalQuery_continuation_invariants parameter root otsTable ftsTable input frame.state state frame.ftsFuel
                  frame.context frame.fuel frame.cache entry actual hclean hsynced hresult hrel hc
                simp only [resumeJointResolved, hi.1, hi.2.1]
              · simp [resume, hc] at hresume

theorem runWithFailure_none
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable computation none cache hit failed =
      (fun result => ((none, result), failed)) <$>
        evalDist (runExceptionMonitor exception (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit) := by
  induction computation using OracleComp.inductionOn generalizing cache hit failed with
  | pure value => simp [runWithFailure_pure, runExceptionMonitor]
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, stepWithFailure, bind_map_left,
        simulateQ_bind, simulateQ_spec_query, runExceptionMonitor_bind, evalDist_bind, map_bind]
      exact bind_congr fun result => ih result.1.1 result.1.2 result.2 failed

theorem probEvent_runWithFailure_le_fullShared
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel) :
    Pr[fun result => result.2 = true |
      runWithFailure exception parameter root otsTable ftsTable computation (some frame) cache false false] ≤
    Pr[JointCompletionFailure | AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceComputation parameter root computation).run frame.cache) frame.context frame.fuel otsTable)] := by
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value => simp [runWithFailure_pure]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      have hc := hvalid.2.2.1.2.1.valuesConsistent
      have ht := hvalid.2.2.1.2.2.1
      rw [runWithFailure_query_bind, stepWithFailure, dif_pos he, probEvent_bind_eq_tsum, tsum_probOutput_map_mul]
      change _ ≤ Pr[JointCompletionFailure | AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input >>= fun reply =>
          jointSourceComputation parameter root (next reply)).run frame.cache) frame.context frame.fuel otsTable)]
      rw [runDetailed_jointSourceOuterQuery_bind (hhash := hh), probEvent_bind_eq_tsum]
      let continuation := fun reply => jointSourceComputation parameter root (next reply)
      calc
        _ ≤ ∑' raw, Pr[= raw | (queryCoupling exception parameter root otsTable ftsTable input frame cache false he).1] *
            Pr[JointCompletionFailure | resumeJointResolved ftsTable (remainingFtsFuel parameter input frame.ftsFuel) continuation raw.1] := by
          apply ENNReal.tsum_le_tsum
          intro raw
          by_cases hr : raw ∈ support (queryCoupling exception parameter root otsTable ftsTable input frame cache false he).1
          · apply mul_le_mul' le_rfl
            have hs := queryCoupling_support exception parameter root otsTable ftsTable input frame cache false he raw hr
            dsimp only
            cases hf : resume parameter otsTable input frame.ftsFuel raw.1 with
            | none =>
                have hfailed := (resume_none_iff_jointCompletionFailure parameter root otsTable ftsTable input frame hc ht raw.1 hs.2.1).1 hf
                rw [probEvent_jointCompletionFailure_resume_eq_one ftsTable (jointSourceOuterQuery parameter root input)
                  continuation frame.state frame.ftsFuel (remainingFtsFuel parameter input frame.ftsFuel)
                  frame.context frame.fuel otsTable frame.cache hc ht raw.1 hs.2.1 hfailed]
                exact probEvent_le_one
            | some middle =>
                rw [resumeJointResolved_eq_of_jointOriginalResume parameter root otsTable ftsTable input continuation frame middle raw.2.1
                  hvalid.1 hvalid.2.1 raw.1 hs.2.1 hs.1 hf]
                simp only [Bool.false_or, Option.isNone_some]
                cases hm : raw.2.2 with
                | true => simp [runWithFailure_none, Function.comp_def]
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
            (fun result => Pr[JointCompletionFailure |
              resumeJointResolved ftsTable (remainingFtsFuel parameter input frame.ftsFuel) continuation result])
          rw [(queryCoupling exception parameter root otsTable ftsTable input frame cache false he).2.map_fst] at hm
          exact hm.symm

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
