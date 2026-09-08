import SphincsSecurity.Proof.NearUniformRawStep
import SphincsSecurity.Proof.StoppedRemainingCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)

theorem expected_runWithFailure_nearUniformRaw_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hdetect : ∀ cache input answer,
      MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) (cache.cacheQuery input answer) →
        exception cache input answer)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap)
    (hclean : hit = false → ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) state.1)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation state.2) frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight 0 current groups remaining) (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) ≤
      survivingLogPotential (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight budget current groups remaining) state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul, Prod.mk.eta]
      unfold survivingLogPotential
      split_ifs
      · exact le_rfl
      · exact cappedReuseRawEnvelope_budget_mono key nearUniformDigestReuseWeight state (Nat.zero_le budget)
          groups remaining hvalid
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
      have hstep := stepWithFailure_nearUniformRawEnvelope_le exception parameter root otsTable ftsTable cap budget hcap
        input frame state hit failed hsigned hbefore hcost hclean groups remaining hvalid
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ hstep
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
        exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2
          (expanded_query_bound_signing_execution key input next budget hbound state _ hlogged).2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged)
          (stepWithFailure_deficit_clean exception parameter root otsTable ftsTable hdetect input frame state.1 hit failed hclean result hr))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

noncomputable def deficitStoppingException (key : SecretKey)
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) : Prop :=
  exception cache input answer ∨ MessageDeficitExceptional key (cache.cacheQuery input answer)

theorem expected_runWithFailure_deficitStopped_raw_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) q)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q)
    (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception) parameter root otsTable ftsTable
        (withSigningLog computation []) frame cache false failed] *
      survivingLogPotential (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight 0 current groups remaining) (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) ≤
      cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable) nearUniformDigestReuseWeight q (cache, []) groups remaining := by
  have hsigned : SigningDigestsCached parameter cache root [] := by intro entry hentry; cases hentry
  apply (expected_runWithFailure_nearUniformRaw_le _ parameter root otsTable ftsTable (fun _ _ _ h => Or.inr h)
    q q hq computation frame (cache, []) false failed hbound hsigned hcache
    (fun _ => messageDeficitExceptional_not_of_no_inputs _ cache hnone) groups remaining hvalid).trans
  unfold survivingLogPotential
  split_ifs
  · exact zero_le
  · exact le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
