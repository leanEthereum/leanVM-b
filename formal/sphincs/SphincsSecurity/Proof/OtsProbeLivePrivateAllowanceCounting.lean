import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveResolvedBudget
import SphincsSecurity.Proof.OtsProbePrivateAllowanceHit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_privateLiveProbeOrdinalAllowance_eq_of_liveBound
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : LiveResolvedQueryBound (IsPrivatePositionProbe target) computation q context fuel table) :
    (∑ ordinal ∈ Finset.range q, privateLiveProbeOrdinalAllowance target computation ordinal context fuel table) =
      privateLiveProbeAllowance target computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => simp [privateLiveProbeOrdinalAllowance, privateLiveProbeAllowance]
  | query_bind input next ih =>
      rw [privateLiveProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have hbound := (liveResolvedQueryBound_query_bind _ _ _ _ _ _ _).mp hbound hcomplete
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · simp [privateLiveProbeOrdinalAllowance_query_bind, hcomplete, hdisclose]
        · rw [if_neg hdisclose]
          have htail (n : Nat) (hnext : ∀ result, some result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input))) →
              LiveResolvedQueryBound (IsPrivatePositionProbe target) (next result.value) n result.context result.remaining result.table) :
              (∑ ordinal ∈ Finset.range n, ∑' result,
                Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                  match result with
                  | none => 0
                  | some result => privateLiveProbeOrdinalAllowance target (next result.value) ordinal result.context result.remaining result.table) =
              ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => privateLiveProbeAllowance target (next result.value) result.context result.remaining result.table := by
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            apply tsum_congr
            intro result
            by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
            · cases result with
              | none => simp
              | some result =>
                  simp only [← Finset.mul_sum]
                  rw [ih result.value n result.context result.remaining result.table (hnext result hresult)]
            · simp [probOutput_eq_zero_of_not_mem_support hresult]
          by_cases hprobe : IsPrivatePositionProbe target input
          · cases q with
            | zero => have := hbound.1 hprobe; omega
            | succ q =>
                rw [Finset.sum_range_succ']
                simp only [privateLiveProbeOrdinalAllowance_query_bind, if_pos hcomplete, if_neg hdisclose,
                  hprobe, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel, and_self, if_true]
                exact (congrArg (fun value => value + privateProbeInputAllowance target table context input)
                  (htail q (fun result hresult => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using hbound.2 result hresult))).trans (add_comm _ _)
          · simp only [privateLiveProbeOrdinalAllowance_query_bind, if_pos hcomplete, if_neg hdisclose,
              hprobe, false_and, if_false, privateProbeInputAllowance_of_not_probe target table context input hprobe, zero_add]
            exact htail q (fun result hresult => by simpa only [if_neg hprobe] using hbound.2 result hresult)
      · simp [privateLiveProbeOrdinalAllowance_query_bind, hcomplete]

theorem sum_privateProbeCut_hits_eq_liveAllowance_of_liveBound
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hhidden : .position target ∉ context.state.revealed)
    (hbound : LiveResolvedQueryBound (IsPrivatePositionProbe target) computation q context fuel table) :
    (∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) =
      privateLiveProbeAllowance target computation context fuel table := by
  simp_rw [probEvent_privateProbeCut_hit_eq_ordinalAllowance target computation _ context fuel table hconsistent hstarts hhidden]
  exact sum_privateLiveProbeOrdinalAllowance_eq_of_liveBound target computation q context fuel table hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
