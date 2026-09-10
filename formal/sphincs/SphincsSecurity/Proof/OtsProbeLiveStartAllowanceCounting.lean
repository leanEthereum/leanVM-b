import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveResolvedBudget
import SphincsSecurity.Proof.OtsProbeStartAllowance

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_expectedLiveStartProbeCutAllowance_eq_of_liveBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    (∑ ordinal ∈ Finset.range q, expectedLiveStartCutAllowance (nativeProbeCutAt computation ordinal) context fuel table) =
      liveStartProbeAllowance computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value =>
      simp [nativeProbeCutAt, expectedLiveStartCutAllowance_pure, nativeCutCandidate, unresolvedStartCandidateAllowance, liveStartProbeAllowance]
  | query_bind input next ih =>
      rw [liveStartProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have hbound := (liveResolvedQueryBound_query_bind _ _ _ _ _ _ _).mp hbound hcomplete
        have htail (n : Nat) (hnext : ∀ result, some result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input))) →
            LiveResolvedQueryBound LazyRevealProbe.IsProbe (next result.value) n result.context result.remaining result.table) :
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
                rw [ih result.value n result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2) (hnext result hresult)]
          · simp [probOutput_eq_zero_of_not_mem_support hresult]
        by_cases hprobe : LazyRevealProbe.IsProbe input
        · cases q with
          | zero => have := hbound.1 hprobe; omega
          | succ q =>
              rw [Finset.sum_range_succ']
              simp only [nativeProbeCutAt_query_bind, if_pos hprobe, expectedLiveStartCutAllowance_pure, if_pos hcomplete]
              have hweight : unresolvedStartCandidateAllowance table context (nativeCutCandidate context (.query input next)) =
                  startProbeInputAllowance table context input := by
                cases input <;> simp [nativeCutCandidate, startProbeInputAllowance, unresolvedStartCandidateAllowance]
              rw [hweight]
              exact (congrArg (fun value => value + startProbeInputAllowance table context input)
                (htail q (fun result hresult => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using hbound.2 result hresult))).trans (add_comm _ _)
        · simp only [nativeProbeCutAt_query_bind, if_neg hprobe,
            startProbeInputAllowance_of_not_probe table context input hprobe, zero_add]
          exact htail q (fun result hresult => by simpa only [if_neg hprobe] using hbound.2 result hresult)
      · rw [if_neg hcomplete]
        simp only [expectedLiveStartCutAllowance_eq_zero_of_not_completable _ context fuel table hconsistent hstarts hcomplete,
          Finset.sum_const_zero]

theorem sum_nativeProbeCut_startHits_eq_liveAllowance_of_liveBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
      runResolvedFromTable context fuel table (nativeProbeCutAt computation ordinal)]) =
      liveStartProbeAllowance computation context fuel table := by
  simp_rw [← expectedLiveStartCutAllowance_eq_hitProbability]
  exact sum_expectedLiveStartProbeCutAllowance_eq_of_liveBound computation q context fuel table hconsistent hstarts hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
