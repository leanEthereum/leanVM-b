import SphincsSecurity.Proof.OtsProbeStartAllowance

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_expectedLiveStartProbeCutAllowance_eq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑ ordinal ∈ Finset.range q, expectedLiveStartCutAllowance (nativeProbeCutAt computation ordinal) context fuel table) =
      liveStartProbeAllowance computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value =>
      simp [nativeProbeCutAt, expectedLiveStartCutAllowance_pure, nativeCutCandidate, unresolvedStartCandidateAllowance, liveStartProbeAllowance]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [liveStartProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have htail (n : Nat) (hnext : ∀ reply, (next reply).IsQueryBoundP LazyRevealProbe.IsProbe n) :
            (∑ ordinal ∈ Finset.range n, expectedLiveStartCutAllowance
              ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
                fun output => nativeProbeCutAt (next output) ordinal) context fuel table) =
            ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
              match result with
              | none => 0
              | some result => liveStartProbeAllowance (next result.value) result.context result.remaining result.table := by
          simp only [expectedLiveStartCutAllowance_bind]
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          apply tsum_congr
          intro result
          by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
          · cases result with
            | none => simp
            | some result =>
                have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                simp only [← Finset.mul_sum]
                rw [ih result.value n result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2) (hnext result.value)]
          · simp [probOutput_eq_zero_of_not_mem_support hresult]
        by_cases hprobe : LazyRevealProbe.IsProbe input
        · cases q with
          | zero => simp [hprobe] at hbound
          | succ q =>
              rw [Finset.sum_range_succ']
              simp only [nativeProbeCutAt_query_bind, if_pos hprobe, expectedLiveStartCutAllowance_pure, if_pos hcomplete]
              have hweight : unresolvedStartCandidateAllowance table context (nativeCutCandidate context (.query input next)) =
                  startProbeInputAllowance table context input := by
                cases input <;> simp [nativeCutCandidate, startProbeInputAllowance, unresolvedStartCandidateAllowance]
              rw [hweight]
              exact (congrArg (fun value => value + startProbeInputAllowance table context input)
                (htail q (fun reply => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using hbound.2 reply))).trans (add_comm _ _)
        · simp only [nativeProbeCutAt_query_bind, if_neg hprobe,
            startProbeInputAllowance_of_not_probe table context input hprobe, zero_add]
          exact htail q (fun reply => by simpa only [if_neg hprobe] using hbound.2 reply)
      · rw [if_neg hcomplete]
        simp only [expectedLiveStartCutAllowance_eq_zero_of_not_completable _ context fuel table hconsistent hstarts hcomplete,
          Finset.sum_const_zero]

theorem sum_nativeProbeCut_startHits_eq_liveAllowance
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
      runResolvedFromTable context fuel table (nativeProbeCutAt computation ordinal)]) =
      liveStartProbeAllowance computation context fuel table := by
  simp_rw [← expectedLiveStartCutAllowance_eq_hitProbability]
  exact sum_expectedLiveStartProbeCutAllowance_eq computation q context fuel table hconsistent hstarts hbound

theorem sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) =
      ∑' table, Pr[= table | sampleOtsHashTable] * liveStartProbeAllowance computation (ensuredInitialContext targets) fuel table := by
  simp only [sampledEnsuredNativeProbeCut, probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [← Finset.mul_sum]
  apply tsum_congr
  intro table
  rw [sum_nativeProbeCut_startHits_eq_liveAllowance computation q (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hbound]

theorem sampledEnsuredLiveStartAllowance_le_chainStartCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q ≤ 2 ^ 126) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑' table, Pr[= table | sampleOtsHashTable] * liveStartProbeAllowance computation (ensuredInitialContext targets) fuel table) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * expectedLiveResolvedQueryCharge chainStartProbeQueryCharge computation
        (ensuredInitialContext targets) fuel table) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [← sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance targets computation fuel q hbound]
  exact sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_expectedChainStartCharge targets computation fuel q hq

end SphincsSecurity.Concrete.OtsProbeSimulation
