import SphincsSecurity.Proof.OtsProbePrivateAllowanceCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem hidden_of_mem_runResolved_no_disclosure
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hhidden : .position target ∉ context.state.revealed)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    .position target ∉ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp only [runResolvedFromTable, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact hhidden
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivatePositionDisclosure target input := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        intro reply
        simpa using hsafe.2 reply
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel (hnext reply) hhidden htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel (hnext reply) hhidden htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () _ fuel (hnext ()) (by exact hhidden) hresult
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih _ context fuel (hnext _) hhidden hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          apply ih () _ fuel (hnext ()) _ hresult
          simpa [LazyRevealProbe.State.publish, IsPrivatePositionDisclosure, ne_comm] using And.intro hquery hhidden
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              dsimp only at hresult
              split_ifs at hresult
              · exact ih () context remaining (hnext ()) hhidden hresult
              · exact ih () _ remaining (hnext ()) (by exact hhidden) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨resolved, _, htail⟩ := hresult
            cases resolved with
            | none => simp at htail
            | some resolved => exact ih resolved.output _ fuel (hnext resolved.output) (by exact hhidden) htail

theorem probEvent_privateProbeCut_hit_eq_ordinalAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hhidden : .position target ∉ context.state.revealed) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] =
      privateLiveProbeOrdinalAllowance target computation ordinal context fuel table := by
  rw [probEvent_privateResolvedView_selected_eq_expectedAllowance target table context fuel _ _ hconsistent hstarts
    (fun result hresult _ => hidden_of_mem_runResolved_no_disclosure target _ context fuel table result
      (privatePositionProbeCutAt_no_disclosure target computation ordinal) hhidden hresult)]
  apply Eq.trans _ (expected_privateProbeCutAllowance_eq_ordinalAllowance target computation ordinal context fuel table hconsistent hstarts)
  apply tsum_congr
  intro option
  by_cases hoption : option ∈ support (runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal))
  · cases option with
    | none => simp [privateProbeCutAllowance]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
        simp [privateProbeCutAllowance, hcore.1]
  · simp [probOutput_eq_zero_of_not_mem_support hoption]

theorem sum_privateProbeCut_hits_eq_liveAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hhidden : .position target ∉ context.state.revealed)
    (hbound : computation.IsQueryBoundP (IsPrivatePositionProbe target) q) :
    (∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) =
      privateLiveProbeAllowance target computation context fuel table := by
  simp_rw [probEvent_privateProbeCut_hit_eq_ordinalAllowance target computation _ context fuel table hconsistent hstarts hhidden]
  exact sum_privateLiveProbeOrdinalAllowance_eq target computation q context fuel table hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
