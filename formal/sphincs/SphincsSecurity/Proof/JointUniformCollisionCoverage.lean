import SphincsSecurity.Proof.JointEncodingExhaustionReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resume_uniform_ne_none
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (n : Nat) (frame : Frame) (cache : QueryCache HashSpec) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (result) (hr : result ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root (.inl (.inl n))).run frame.cache) frame.context frame.fuel otsTable))) :
    resume parameter otsTable (.inl (.inl n)) frame.ftsFuel result ≠ none := by
  have hproject := jointSourceNativeBlock_resolved parameter ftsTable frame.state frame.ftsFuel
    (OtsProbeSimulation.splitUniformImpl n)
    (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
    frame.context frame.fuel otsTable frame.cache hvalid.1
  have hn : projectJointResolvedCache parameter ftsTable result ∈ support
      (OtsProbeSimulation.runResolvedFromTable frame.context frame.fuel otsTable
        ((OtsProbeSimulation.splitUniformImpl n).run
          (OtsProbeSimulation.replaceOrdinaryCache frame.cache.1 (mergedCache parameter ftsTable frame.cache.2)))) := by
    rw [← hproject, support_map]
    exact ⟨result, hr, rfl⟩
  unfold OtsProbeSimulation.splitUniformImpl LazyRevealProbe.uniformQuery at hn
  rw [StateT.run_liftM, OtsProbeSimulation.runResolvedFromTable_uniform_query_bind] at hn
  simp only [OtsProbeSimulation.runResolvedFromTable, construct_pure, mem_support_bind_iff, mem_support_pure_iff] at hn
  obtain ⟨output, _, heq⟩ := hn
  cases result with
  | stopped hit => simp [projectJointResolvedCache, cleanJointResolved] at heq
  | done hit state entry =>
      cases hit with
      | true => simp [projectJointResolvedCache, cleanJointResolved] at heq
      | false =>
          cases entry with
          | none => simp [projectJointResolvedCache, cleanJointResolved] at heq
          | some entry =>
              have hc : entry.context = frame.context := by
                simpa only [projectJointResolvedCache, cleanJointResolved, Option.map_some, Option.some.injEq] using
                  congrArg (fun value => value.map OtsProbeSimulation.ResolvedRunResult.context) heq
              simp only [resume, hc, if_pos hvalid.2.2.1.2.2.2.1, ne_eq, reduceCtorEq, not_false_eq_true]

theorem stepWithFailure_uniform_failed_eq_false
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (n : Nat) (frame : Frame) (cache : QueryCache HashSpec)
    (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inl n)) cache false)
    (result) (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable
      (.inl (.inl n)) (some frame) cache false false)) : result.2 = false := by
  rw [stepWithFailure, dif_pos henabled, support_map] at hr
  obtain ⟨pair, hp, rfl⟩ := hr
  have hn := resume_uniform_ne_none parameter root otsTable ftsTable n frame cache henabled.2.1 pair.1
    (queryCoupling_support exception parameter root otsTable ftsTable (.inl (.inl n)) frame cache false henabled pair hp).2.1
  simp only [Bool.false_or]
  cases he : resume parameter otsTable (.inl (.inl n)) frame.ftsFuel pair.1 with
  | none => exact False.elim (hn he)
  | some frame => rfl

theorem stepWithFailure_uniform_cache_hit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (n : Nat) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (result) (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable
      (.inl (.inl n)) frame cache hit failed)) : result.1.2.1.2 = cache ∧ result.1.2.2 = hit := by
  have ha := stepWithFailure_original_support exception parameter root otsTable ftsTable (.inl (.inl n)) frame cache hit failed result hr
  change result.1.2 ∈ support (runExceptionMonitor exception
    (liftM (OracleSpec.query (spec := OracleWorld) (.inl n))) cache hit) at ha
  have hrun : (unifFwdImpl HashSpec n).run cache =
      (fun output => (output, cache)) <$> (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
    simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
      (hashSpec := HashSpec) (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) cache)
  rw [runExceptionMonitor, construct_query] at ha
  simp only [queryException, Bool.or_false] at ha
  change result.1.2 ∈ support ((unifFwdImpl HashSpec n).run cache >>= fun output => pure (output, hit)) at ha
  rw [hrun, bind_map_left] at ha
  simp only [mem_support_bind_iff, mem_support_pure_iff] at ha
  obtain ⟨output, _, heq⟩ := ha
  exact ⟨congrArg (fun value => value.1.2) heq, congrArg Prod.snd heq⟩

theorem expected_jointCollisionCoverageBudget_uniform_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget n : Nat) (frame : Frame) (state : CoverLogState)
    (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inl n)) state.1 false) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inl n)) (some frame) state.1 false false] *
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget
          (stepSigningLogState (.inl (.inl n)) state.2 result) result.1.2.2 result.2) ≤
      jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state false false := by
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inl n)) (some frame) state.1 false false
  calc
    _ = ∑' result, Pr[= result | computation] *
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state false false := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support computation
      · have hp := stepWithFailure_uniform_cache_hit (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable n (some frame) state.1 false false result hr
        have hf := stepWithFailure_uniform_failed_eq_false (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable n frame state.1 henabled result hr
        simp only [stepSigningLogState, signingLogFragment, List.append_nil, hp.1, hp.2, hf, Prod.mk.eta, computation]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
