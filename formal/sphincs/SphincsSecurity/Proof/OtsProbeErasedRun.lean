import SphincsSecurity.Proof.OtsProbeErasedHistorySampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem relTriple_runResolvedFromTable_eraseProbeQueries
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (h : PendingRelaxation left right) :
    RelTriple (runResolvedFromTable left fuel table computation)
      (runResolvedFromTable right 0 table (eraseProbeQueries computation)) (OptionRefines PendingRunRel) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value => exact relTriple_pure_pure ⟨h, rfl, rfl⟩
  | query_bind input next ih =>
      rw [eraseProbeQueries, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, runResolvedFromTable_uniform_query_bind]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel h
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel h
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
          exact ih () _ _ fuel (h.ensure coordinate)
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind, runResolvedFromTable_publish_query_bind]
          exact ih () _ _ fuel (h.publish coordinate)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind, runResolvedFromTable_peek_query_bind]
          rw [h.stateValues]
          exact ih _ left right fuel h
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => exact relTriple_none_optionRefines _ _
          | succ fuel =>
              split_ifs
              · exact ih () left right fuel h
              · exact ih () _ right fuel (h.addPending_left coordinate digest)
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind, runResolvedFromTable_reveal_query_bind]
          have hr : RelTriple
              (match coordinate with
              | .chainStart lay tree leafIdx chainIdx => pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ left)
              | .position position => resolveDeferredReveal table position left)
              (match coordinate with
              | .chainStart lay tree leafIdx chainIdx => pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ right)
              | .position position => resolveDeferredReveal table position right) (OptionRefines PendingResolutionRel) := by
            cases coordinate with
            | chainStart lay tree leafIdx chainIdx => exact relTriple_pure_pure (resolveDeferredChainStart_pendingRelaxation table _ left right h)
            | position position => exact relTriple_resolveDeferredReveal_pendingRelaxation table position left right h
          cases coordinate <;> apply relTriple_bind hr <;> intro a b hab
          all_goals
            cases a with
            | none => exact relTriple_none_optionRefines _ _
            | some a =>
                cases b with
                | none => exact False.elim hab
                | some b =>
                    have ho : a.output = b.output := hab.2
                    dsimp only
                    rw [ho]
                    exact ih _ _ _ fuel (h.materialize _ b.output a.values b.values hab.1.privateValues)

theorem probEvent_resolved_value_le_erased
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (event : Option α → Prop) (hnone : ¬event none) :
    Pr[fun result => event (resolvedPrefixValue result) | runResolvedFromTable context fuel table computation] ≤
      Pr[fun result => event (resolvedPrefixValue result) |
        runResolvedFromTable context 0 table (eraseProbeQueries computation)] := by
  apply probEvent_le_of_relTriple
    (relTriple_runResolvedFromTable_eraseProbeQueries computation context context fuel table (PendingRelaxation.refl _))
  intro left right hrel hleft
  cases left with
  | none => exact False.elim (hnone hleft)
  | some left =>
      cases right with
      | none => exact False.elim hrel
      | some right => simpa only [resolvedPrefixValue, Option.map_some, hrel.2.1] using hleft

theorem probEvent_sampled_resolved_value_le_erased_history
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel : Nat) (event : Option α → Prop) (hnone : ¬event none) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[fun result => event (resolvedPrefixValue result) |
        runResolvedFromTable (ensuredInitialContext targets) fuel table computation]) ≤
      Pr[fun entry => event (historyPrefixValue entry) |
        runResolvedHistoryPrefix (eraseProbeQueries computation) (ensuredInitialContext targets) 0 []] := by
  have hcovered : PendingCoveredBy [] (ensuredInitialContext targets) := by
    intro entry hentry
    simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hentry
  have hcard : (ensuredInitialContext targets).state.pending.card < Fintype.card Digest := by
    simpa only [ensuredInitialContext, LazyRevealProbe.State.empty, Finset.card_empty] using Fintype.card_pos (α := Digest)
  have htable (base : OtsSecretIndex → HashOutput) : completedStartTable (ensuredInitialContext targets).state base = base := by
    funext index
    rfl
  have hd := evalDist_sampled_probeFree_value_eq_history_prefix
    (eraseProbeQueries computation) (ensuredInitialContext targets) 0 hcovered hcard (eraseProbeQueries_probeFree _)
  simp only [htable] at hd
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        Pr[fun result => event (resolvedPrefixValue result) |
          runResolvedFromTable (ensuredInitialContext targets) 0 table (eraseProbeQueries computation)] := by
      exact ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
        (probEvent_resolved_value_le_erased computation _ fuel table event hnone)
    _ = _ := by
      have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd (p := event)
      simpa only [probEvent_map, Function.comp_def, probEvent_bind_eq_tsum] using hp

end SphincsSecurity.Concrete.OtsProbeSimulation
