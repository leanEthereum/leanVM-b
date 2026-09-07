import SphincsSecurity.Proof.TargetArrivalStep
import SphincsSecurity.Proof.JointProbeOriginalBeforeFailureCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

abbrev FailureStepResult (input : (OracleWorld + SigningSpec).Domain) :=
  (Option Frame × (((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool)) × Bool

def stepSigningLogState (input : (OracleWorld + SigningSpec).Domain) (log : QueryLog SigningSpec)
    (result : FailureStepResult input) : CoverLogState :=
  (result.1.2.1.2, log ++ signingLogFragment input result.1.2.1.1)

theorem stepWithFailure_expect_logged
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (hit failed : Bool)
    (weight : (OracleWorld + SigningSpec).Range input → CoverLogState → ENNReal) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      weight result.1.2.1.1 (stepSigningLogState input log result)) =
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run (cache, log)] *
        weight result.1 result.2 := by
  have hfirst := tsum_probOutput_map_mul
    (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed) Prod.fst
    (fun result => weight result.2.1.1 (result.2.1.2, log ++ signingLogFragment input result.2.1.1))
  rw [stepWithFailure_project, step_expect_original exception parameter root otsTable ftsTable input frame cache hit
    (fun result => weight result.1.1 (result.1.2, log ++ signingLogFragment input result.1.1))] at hfirst
  simp only [stepSigningLogState]
  rw [← hfirst, logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hmonitor := tsum_probOutput_map_mul
    (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) Prod.fst
    (fun result => weight result.1 (result.2, log ++ signingLogFragment input result.1))
  rw [runExceptionMonitor_project] at hmonitor
  rw [← hmonitor, unloggedMappedAdversaryImpl_eq_simulateQ_expanded]

theorem stepWithFailure_logged_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (hit failed : Bool) (result : FailureStepResult input)
    (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    (result.1.2.1.1, stepSigningLogState input log result) ∈
      support ((logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run (cache, log)) := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map]
  refine ⟨result.1.2.1, ?_, rfl⟩
  rw [unloggedMappedAdversaryImpl_eq_simulateQ_expanded]
  exact runExceptionMonitor_support_project exception _ cache hit
    (stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hresult)

theorem stepWithFailure_hit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec)
    (failed : Bool) (result : FailureStepResult input)
    (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache true failed)) :
    result.1.2.2 = true := by
  have h := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache true failed result hresult
  rw [runExceptionMonitor_true, support_map] at h
  obtain ⟨original, _, heq⟩ := h
  exact congrArg Prod.snd heq.symm

theorem stepWithFailure_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hit failed : Bool) (hstop : (hit || failed) = true) (result : FailureStepResult input)
    (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    (result.1.2.2 || result.2) = true := by
  cases hit with
  | true => rw [stepWithFailure_hit exception parameter root otsTable ftsTable input frame cache failed result hresult]; rfl
  | false =>
      have hf : failed = true := by simpa using hstop
      subst failed
      rw [stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache false result hresult]
      exact Bool.or_true _

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
