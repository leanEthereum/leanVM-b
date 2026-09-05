import SphincsSecurity.Proof.OtsProbePrivateValueProbeCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem PrivateTargetState.probe_target
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (digest : Digest) :
    PrivateTargetState target output (insert digest pending)
      { context with state := context.state.addPending (.position target) digest } := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [← h.2.2.2]
  ext candidate
  simp [LazyRevealProbe.State.mem_pendingAt_iff, LazyRevealProbe.State.addPending]

theorem PrivateTargetState.history_of_mem_runResolved
    {target : Position} {output : HashOutput}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (pending : Finset Digest) (bound : Nat) (result : ResolvedRunResult α)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    PrivateTargetState target output (result.context.state.pendingAt (.position target)) result.context ∧
      pending ⊆ result.context.state.pendingAt (.position target) ∧
      (result.context.state.pendingAt (.position target)).card ≤ pending.card + bound := by
  induction computation using OracleComp.inductionOn generalizing context fuel pending bound with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      simpa only [h.2.2.2] using And.intro h (And.intro (Finset.Subset.refl pending) (Nat.le_add_right pending.card bound))
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe hcount
      have hquery : ¬IsPrivatePositionDisclosure target query := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        intro reply
        simpa using hsafe.2 reply
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel pending bound h (hnext reply)
            (by simpa [IsPrivatePositionProbe] using hcount.2 reply) htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel pending bound h (hnext reply)
            (by simpa [IsPrivatePositionProbe] using hcount.2 reply) htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel pending bound h (hnext ())
            (by simpa [IsPrivatePositionProbe] using hcount.2 ()) hresult
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih _ context fuel pending bound h (hnext _)
            (by simpa [IsPrivatePositionProbe] using hcount.2 _) hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () _ fuel pending bound (h.publish_other coordinate hquery) (hnext ())
            (by simpa [IsPrivatePositionProbe] using hcount.2 ()) hresult
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              dsimp only at hresult
              by_cases htarget : coordinate = .position target
              · subst coordinate
                cases bound with
                | zero => simpa [IsPrivatePositionProbe] using hcount.1
                | succ bound =>
                    rw [if_neg h.2.2.1] at hresult
                    have htail := ih () _ remaining (insert digest pending) bound (h.probe_target digest) (hnext ())
                      (by simpa [IsPrivatePositionProbe] using hcount.2 ()) hresult
                    refine ⟨htail.1, ?_, ?_⟩
                    · exact (Finset.subset_insert digest pending).trans htail.2.1
                    · have hcard := Finset.card_insert_le digest pending
                      have htailCard := htail.2.2
                      omega
              · have hbound : (next ()).IsQueryBoundP (IsPrivatePositionProbe target) bound := by
                  simpa [IsPrivatePositionProbe, htarget] using hcount.2 ()
                split_ifs at hresult
                · exact ih () context remaining pending bound h (hnext ()) hbound hresult
                · exact ih () _ remaining pending bound (h.probe_other coordinate digest htarget) (hnext ()) hbound hresult
      | reveal coordinate =>
          have hbound (reply) : (next reply).IsQueryBoundP (IsPrivatePositionProbe target) bound := by
            simpa [IsPrivatePositionProbe] using hcount.2 reply
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [pure_bind] at hresult
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp [hresolved] at hresult
              | some middle =>
                  simp only [hresolved] at hresult
                  have hvalues := resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩ context middle hresolved
                  exact ih middle.output _ fuel pending bound
                    (h.materialize_other _ middle.output middle.values (by simp) (hvalues ▸ h.2.1))
                    (hnext middle.output) (hbound middle.output) hresult
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨option, hresolve, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some middle =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position output table context middle h.1 h.2.1 hresolve
                  exact ih middle.output _ fuel pending bound (h.materialize_other _ middle.output middle.values hquery hvalue)
                    (hnext middle.output) (hbound middle.output) htail

theorem privatePositionProbeCutAt_history_bound
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (ordinal : Nat)
    (h : PrivateTargetState target output pending context) (result : ResolvedRunResult (PrivateValueCut α))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal))) :
    PrivateTargetState target output (result.context.state.pendingAt (.position target)) result.context ∧
      pending ⊆ result.context.state.pendingAt (.position target) ∧
      (result.context.state.pendingAt (.position target)).card ≤ pending.card + ordinal :=
  h.history_of_mem_runResolved (privatePositionProbeCutAt target computation ordinal) context fuel table pending ordinal result
    (privatePositionProbeCutAt_no_disclosure target computation ordinal) (privatePositionProbeCutAt_probe_bound target computation ordinal) hresult

theorem privatePositionProbeCutAt_live_history_avoids_output
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (ordinal : Nat)
    (h : PrivateTargetState target output pending context) (result : ResolvedRunResult (PrivateValueCut α))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)))
    (hcomplete : DeferredCompletable table result.context) :
    truncateHash output ∉ result.context.state.pendingAt (.position target) := by
  have hfinal := (privatePositionProbeCutAt_history_bound target output computation context fuel table pending ordinal h result hresult).1
  obtain ⟨completion, hcompletion⟩ := hcomplete
  have houtput := hcompletion.2.1 target output hfinal.2.1
  intro hmem
  have hpending := (LazyRevealProbe.State.mem_pendingAt_iff result.context.state (.position target) (truncateHash output)).mp hmem
  exact hcompletion.2.2.1 (.position target) (truncateHash output) hpending (by rw [houtput])

end SphincsSecurity.Concrete.OtsProbeSimulation
