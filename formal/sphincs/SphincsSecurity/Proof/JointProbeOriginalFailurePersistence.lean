import SphincsSecurity.Proof.JointProbeOriginalFailureMonitor

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem stepWithFailure_failed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (result) (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit true)) :
    result.2 = true := by
  cases frame with
  | none =>
      rw [stepWithFailure, support_map] at hresult
      obtain ⟨actual, _, rfl⟩ := hresult
      rfl
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
      · rw [stepWithFailure, dif_pos h, support_map] at hresult
        obtain ⟨actual, _, rfl⟩ := hresult
        simp only [Bool.true_or]
      · rw [stepWithFailure, dif_neg h, support_map] at hresult
        obtain ⟨actual, _, rfl⟩ := hresult
        rfl

theorem runWithFailure_failed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (result) (hresult : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit true)) :
    result.2 = true := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit result with
  | pure value =>
      simp only [runWithFailure_pure, support_pure, Set.mem_singleton_iff] at hresult
      exact congrArg Prod.snd hresult
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache hit head hhead] at htail
      exact ih head.1.2.1.1 head.1.1 head.1.2.1.2 head.1.2.2 result htail

theorem runWithFailure_probFailure_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    Pr[⊥ | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] = 0 := by
  rw [← probFailure_map (f := Prod.fst), runWithFailure_project,
    ← probFailure_map (f := Prod.snd), run_original]
  exact OracleComp.ProgramLogic.Relational.probFailure_evalDist_eq_zero _

theorem probEvent_runWithFailure_failed_eq_one
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    Pr[fun result => result.2 = true | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit true] = 1 := by
  exact probEvent_eq_one_iff.mpr ⟨runWithFailure_probFailure_eq_zero exception parameter root otsTable ftsTable computation frame cache hit true,
    runWithFailure_failed exception parameter root otsTable ftsTable computation frame cache hit⟩

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
