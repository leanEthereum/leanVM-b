import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveContextCharge
import SphincsSecurity.Proof.OtsProbeNativeQueryTrace
import SphincsSecurity.Proof.OtsProbeRiskAccumulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_nativeQuery_finished_le_guessCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun verdict => verdict = true | runResolvedFromTable context fuel table
      ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) >>= finishResolvedRunIsNone] ≤
      resolvedContextFailureRisk table context + canonicalGuessCharge parameter table input context fuel cache := by
  have hdist := evalDist_canonicalQuery_finished_eq_raw parameter root table ftsSecret input context fuel cache hconsistent hstarts
  have heq := probEvent_congr' (fun _ _ => Iff.rfl) hdist (p := fun verdict => verdict = true)
  exact heq ▸ probEvent_canonicalQuery_finished_le_guessCharge parameter root table ftsSecret input context fuel cache hconsistent hstarts

noncomputable def expectedNativeTerminalRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ℝ≥0∞ :=
  ∑' result, Pr[= result | runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] *
    resolvedOutcomeFailureRisk result.1

theorem expectedNativeTerminalRisk_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    expectedNativeTerminalRisk parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache =
      ∑' option, Pr[= option | runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)] *
        match option with
        | none => 1
        | some result => expectedNativeTerminalRisk parameter root ftsSecret (next result.value.1)
            result.context result.remaining result.table result.value.2 := by
  rw [expectedNativeTerminalRisk, runNativeQueryTrace_query_bind, if_pos hcomplete, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro option
  cases option with
  | none => simp [resolvedOutcomeFailureRisk]
  | some result =>
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem expectedNativeTerminalRisk_le_initial_add_guessCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedNativeTerminalRisk parameter root ftsSecret computation context fuel table cache ≤
      resolvedContextFailureRisk table context + expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (canonicalGuessCharge parameter table) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · simp [expectedNativeTerminalRisk, runNativeQueryTrace, expectedLiveNativeContextCharge,
          resolvedOutcomeFailureRisk, hcomplete]
      · simp [expectedNativeTerminalRisk, runNativeQueryTrace, expectedLiveNativeContextCharge,
          resolvedOutcomeFailureRisk, hcomplete, resolvedContextFailureRisk_of_not_completable table context hcomplete]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [expectedNativeTerminalRisk_query_bind parameter root ftsSecret input next context fuel table cache hcomplete]
        let queryRun := runResolvedFromTable context fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        let tailCharge := fun option : Option (ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache)) =>
          match option with
          | none => (0 : ℝ≥0∞)
          | some result => expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (canonicalGuessCharge parameter table)
              (next result.value.1) result.context result.remaining result.table result.value.2
        have hstep := probEvent_nativeQuery_finished_le_guessCharge parameter root table ftsSecret input
          context fuel cache hconsistent hstarts
        rw [probEvent_finished_eq_expected_outcomeRisk] at hstep
        calc
          _ ≤ ∑' option, Pr[= option | queryRun] * (resolvedOutcomeFailureRisk option + tailCharge option) := by
            apply ENNReal.tsum_le_tsum
            intro option
            by_cases hoption : option ∈ support queryRun
            · cases option with
              | none => simp [queryRun, resolvedOutcomeFailureRisk, tailCharge]
              | some result =>
                  have hcore := resolvedCore_of_mem_runResolvedFromTable
                    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) context fuel table result hconsistent hstarts hoption
                  simp only [resolvedOutcomeFailureRisk, tailCharge, hcore.1]
                  exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.value.2
                    hcore.2.1 hcore.2.2)
            · have hzero := probOutput_eq_zero_of_not_mem_support hoption
              change Pr[= option | queryRun] * _ ≤ _
              simp only [hzero, zero_mul, le_refl]
          _ = (∑' option, Pr[= option | queryRun] * resolvedOutcomeFailureRisk option) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
          _ ≤ (resolvedContextFailureRisk table context + canonicalGuessCharge parameter table input context fuel cache) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := add_le_add hstep le_rfl
          _ = _ := by
            rw [expectedLiveNativeContextCharge_query_bind, if_pos hcomplete]
            exact add_assoc _ _ _
      · rw [expectedNativeTerminalRisk, runNativeQueryTrace_of_not_completable parameter root ftsSecret _
          context fuel table cache hcomplete, tsum_probOutput_pure_mul,
          expectedLiveNativeContextCharge_eq_zero_of_not_completable (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) _ _
            context fuel table cache hcomplete,
          resolvedContextFailureRisk_of_not_completable table context hcomplete]
        simp only [resolvedOutcomeFailureRisk, add_zero, le_refl]

end SphincsSecurity.Concrete.OtsProbeSimulation
