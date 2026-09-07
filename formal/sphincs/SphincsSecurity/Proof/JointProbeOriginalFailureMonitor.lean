import SphincsSecurity.Proof.JointProbeOriginalRetainedExecution
import SphincsSecurity.Proof.JointProbeOriginalExecutionBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def stepWithFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    SPMF ((Option Frame × (((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool)) × Bool) :=
  match frame with
  | none => (fun result => ((none, result), failed)) <$>
      evalDist (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit)
  | some frame =>
      if h : frame.Enabled parameter otsTable ftsTable input cache hit then
        (fun pair => ((if pair.2.2 then none else resume parameter otsTable input frame.ftsFuel pair.1, pair.2),
          failed || (resume parameter otsTable input frame.ftsFuel pair.1).isNone)) <$>
          (queryCoupling exception parameter root otsTable ftsTable input frame cache hit h).1
      else (fun result => ((none, result), failed)) <$>
        evalDist (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit)

theorem stepWithFailure_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    Prod.fst <$> stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed =
      step exception parameter root otsTable ftsTable input frame cache hit := by
  cases frame with
  | none => simp only [stepWithFailure, step, Functor.map_map]
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
      · simp only [stepWithFailure, step, dif_pos h, Functor.map_map]
      · simp only [stepWithFailure, step, dif_neg h, Functor.map_map]

theorem stepWithFailure_support_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (result) (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    result.1 ∈ support (step exception parameter root otsTable ftsTable input frame cache hit) := by
  rw [← stepWithFailure_project exception parameter root otsTable ftsTable input frame cache hit failed, support_map]
  exact ⟨result, hresult, rfl⟩

noncomputable def runWithFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → Bool → SPMF ((Option Frame × ((α × QueryCache HashSpec) × Bool)) × Bool) :=
  OracleComp.construct (fun value frame cache hit failed => pure ((frame, ((value, cache), hit)), failed))
    (fun input _ next frame cache hit failed =>
      stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed >>= fun result =>
        next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem runWithFailure_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (pure value) frame cache hit failed =
      pure ((frame, ((value, cache), hit)), failed) := rfl

theorem runWithFailure_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed >>= fun result =>
        runWithFailure exception parameter root otsTable ftsTable (next result.1.2.1.1)
          result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

theorem runWithFailure_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    Prod.fst <$> runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed =
      run exception parameter root otsTable ftsTable computation frame cache hit := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, map_bind]
      simp_rw [ih]
      rw [run_query_bind, ← stepWithFailure_project exception parameter root otsTable ftsTable input frame cache hit failed, bind_map_left]

theorem runWithFailure_support_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (result) (hresult : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)) :
    result.1 ∈ support (run exception parameter root otsTable ftsTable computation frame cache hit) := by
  rw [← runWithFailure_project exception parameter root otsTable ftsTable computation frame cache hit failed, support_map]
  exact ⟨result, hresult, rfl⟩

theorem runWithFailure_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (computation >>= next) frame cache hit failed =
      runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed >>= fun result =>
        runWithFailure exception parameter root otsTable ftsTable (next result.1.2.1.1)
          result.1.1 result.1.2.1.2 result.1.2.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input continuation ih =>
      rw [bind_assoc, runWithFailure_query_bind, runWithFailure_query_bind, bind_assoc]
      exact bind_congr fun result => ih result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2

theorem stepWithFailure_invariant
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hvalid : ∀ live, frame = some live → live.Valid parameter otsTable ftsTable cache)
    (hhash : ∀ live, frame = some live → OtsProbeSimulation.IsOuterHash input → 0 < live.ftsFuel)
    (hstate : frame.isNone = (hit || failed))
    (result) (hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    (∀ live, result.1.1 = some live → live.Valid parameter otsTable ftsTable result.1.2.1.2) ∧
      result.1.1.isNone = (result.1.2.2 || result.2) := by
  have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input frame cache hit failed result hresult
  refine ⟨fun live hlive => (step_valid exception parameter root otsTable ftsTable input frame cache hit result.1 hp live hlive).1, ?_⟩
  cases frame with
  | none =>
      rw [stepWithFailure, support_map] at hresult
      obtain ⟨actual, hactual, rfl⟩ := hresult
      have hwhere : hit = true ∨ failed = true := by simpa only [Option.isNone_none, Bool.or_eq_true_iff] using hstate.symm
      rcases hwhere with hhit | hfailed
      · rw [hhit, runExceptionMonitor_true, evalDist_map, support_map] at hactual
        obtain ⟨original, _, rfl⟩ := hactual
        rfl
      · simp only [hfailed, Bool.or_true, Option.isNone_none]
  | some frame =>
      have hboth : hit = false ∧ failed = false := by simpa only [Option.isNone_some, Bool.or_eq_false_iff] using hstate.symm
      have h : frame.Enabled parameter otsTable ftsTable input cache hit := ⟨hboth.1, hvalid frame rfl, hhash frame rfl⟩
      rw [stepWithFailure, dif_pos h, support_map] at hresult
      obtain ⟨raw, _, rfl⟩ := hresult
      dsimp only
      rw [hboth.2]
      cases raw.2.2 <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.false_or, Bool.true_or, Option.isNone_none]

theorem runWithFailure_invariant
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hvalid : ∀ live, frame = some live → live.Valid parameter otsTable ftsTable cache)
    (hbound : ∀ live, frame = some live → computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash live.ftsFuel)
    (hstate : frame.isNone = (hit || failed))
    (result) (hresult : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)) :
    (∀ live, result.1.1 = some live → live.Valid parameter otsTable ftsTable result.1.2.1.2) ∧
      result.1.1.isNone = (result.1.2.2 || result.2) := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed result with
  | pure value =>
      simp only [runWithFailure_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hvalid, hstate⟩
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hhash : ∀ live, frame = some live → OtsProbeSimulation.IsOuterHash input → 0 < live.ftsFuel := by
        intro live hlive hhash
        have hb := hbound live hlive
        rw [isQueryBoundP_query_bind_iff] at hb
        exact hb.1.elim (fun hn => False.elim (hn hhash)) id
      have hs := stepWithFailure_invariant exception parameter root otsTable ftsTable input frame cache hit failed hvalid hhash hstate head hhead
      have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input frame cache hit failed head hhead
      apply ih head.1.2.1.1 head.1.1 head.1.2.1.2 head.1.2.2 head.2 hs.1 _ hs.2 result htail
      intro middle hm
      cases frame with
      | none =>
          rw [step, support_map] at hp
          obtain ⟨original, _, heq⟩ := hp
          have hnone : head.1.1 = none := (congrArg Prod.fst heq).symm
          simp [hnone] at hm
      | some frame =>
          exact step_queryBound exception parameter root otsTable ftsTable input next frame cache hit
            (hbound frame rfl) head.1 hp middle hm

theorem stepWithFailure_new_failure_probability
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (h : frame.Enabled parameter otsTable ftsTable input cache hit) :
    Pr[fun result => result.2 = true | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache hit false] =
      Pr[fun left => resume parameter otsTable input frame.ftsFuel left = none |
        AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
          (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)] := by
  rw [stepWithFailure, dif_pos h, probEvent_map]
  have hm := congrArg (fun computation => Pr[fun left => resume parameter otsTable input frame.ftsFuel left = none | computation])
    (queryCoupling exception parameter root otsTable ftsTable input frame cache hit h).2.map_fst
  simp only [probEvent_map, Function.comp_def] at hm
  change Pr[fun pair => resume parameter otsTable input frame.ftsFuel pair.1 = none |
      (queryCoupling exception parameter root otsTable ftsTable input frame cache hit h).1] =
    Pr[fun left => resume parameter otsTable input frame.ftsFuel left = none |
      AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)] at hm
  simpa only [Function.comp_def, Bool.false_or, Option.isNone_iff_eq_none] using hm

theorem expectedProbeCharge_bind_withFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedProbeCharge exception parameter root otsTable ftsTable (computation >>= next) frame cache hit =
      expectedProbeCharge exception parameter root otsTable ftsTable computation frame cache hit +
        ∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] *
          expectedProbeCharge exception parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 := by
  rw [expectedProbeCharge_bind]
  congr 1
  rw [← runWithFailure_project exception parameter root otsTable ftsTable computation frame cache hit failed, tsum_probOutput_map_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
