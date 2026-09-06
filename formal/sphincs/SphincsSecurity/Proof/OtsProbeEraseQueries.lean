import SphincsSecurity.Proof.OtsProbePendingRelaxation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def eraseProbeQueries (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    OracleComp (LazyRevealProbe.World Coordinate) α :=
  OracleComp.construct pure (fun input _ next =>
    match input with
    | .probe _ _ => next ()
    | input => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) computation

theorem eraseProbeQueries_probeFree (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    (eraseProbeQueries computation).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [eraseProbeQueries]
  | query_bind input next ih =>
      rw [eraseProbeQueries, OracleComp.construct_query_bind]
      cases input
      case probe coordinate digest => exact ih ()
      all_goals
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [LazyRevealProbe.IsProbe]), fun output => by
          simpa only [eraseProbeQueries, LazyRevealProbe.IsProbe, if_false, Nat.sub_zero] using ih output⟩

theorem eraseProbeQueries_disclosure_bound
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (h : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) bound) :
    (eraseProbeQueries computation).IsQueryBoundP (IsPrivatePositionDisclosure target) bound := by
  induction computation using OracleComp.inductionOn generalizing bound with
  | pure value => simp [eraseProbeQueries]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [eraseProbeQueries, OracleComp.construct_query_bind]
      cases input
      case probe coordinate digest =>
        exact ih () bound (by simpa only [IsPrivatePositionDisclosure, if_false, Nat.sub_zero] using h.2 ())
      all_goals
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨h.1, fun output => ih output _ (h.2 output)⟩

theorem eraseProbeQueries_no_access
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (h : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    (eraseProbeQueries computation).IsQueryBoundP (IsPrivatePositionAccess target) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [eraseProbeQueries]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [eraseProbeQueries, OracleComp.construct_query_bind]
      cases input
      case probe coordinate digest =>
        exact ih () (by simpa only [IsPrivatePositionDisclosure, if_false, Nat.sub_zero] using h.2 ())
      all_goals
        have hn (output) := ih output (by simpa using h.2 output)
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        constructor
        · simpa only [IsPrivatePositionDisclosure, IsPrivatePositionAccess] using h.1
        · intro output
          simpa only [eraseProbeQueries, Nat.zero_sub, ite_self] using hn output

theorem PendingRelaxation.ensure {left right : DeferredContext} (h : PendingRelaxation left right) (coordinate : Coordinate) :
    PendingRelaxation { left with state := left.state.ensure coordinate } { right with state := right.state.ensure coordinate } :=
  ⟨h.stateValues, h.privateValues, h.revealed, h.pending⟩

theorem PendingRelaxation.publish {left right : DeferredContext} (h : PendingRelaxation left right) (coordinate : Coordinate) :
    PendingRelaxation { left with state := left.state.publish coordinate } { right with state := right.state.publish coordinate } := by
  exact ⟨h.stateValues, h.privateValues, by simp [LazyRevealProbe.State.publish, h.revealed], h.pending⟩

theorem PendingRelaxation.addPending_left {left right : DeferredContext} (h : PendingRelaxation left right)
    (coordinate : Coordinate) (digest : Digest) :
    PendingRelaxation { left with state := left.state.addPending coordinate digest } right := by
  exact ⟨h.stateValues, h.privateValues, h.revealed, h.pending.trans (Finset.subset_insert _ _)⟩

theorem PendingRelaxation.materialize {left right : DeferredContext} (h : PendingRelaxation left right)
    (coordinate : Coordinate) (output : HashOutput) (leftValues rightValues : DeferredStructuralValues) (hvalues : leftValues = rightValues) :
    PendingRelaxation { state := left.state.materialize coordinate output, values := leftValues }
      { state := right.state.materialize coordinate output, values := rightValues } := by
  refine ⟨by simp [LazyRevealProbe.State.materialize, h.stateValues], hvalues, h.revealed, ?_⟩
  intro pair hpair
  exact Finset.mem_filter.mpr ⟨h.pending (Finset.mem_filter.mp hpair).1, (Finset.mem_filter.mp hpair).2⟩

def PendingRunRel (left right : ResolvedRunResult α) : Prop :=
  PendingRelaxation left.context right.context ∧ left.value = right.value ∧ left.table = right.table

theorem relTriple_runPrivateErasedPrefix_eraseProbeQueries
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (h : PendingRelaxation left right) :
    RelTriple (runPrivateErasedPrefix target left fuel table computation)
      (runResolvedFromTable right 0 table (eraseProbeQueries computation)) (OptionRefines PendingRunRel) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value => exact relTriple_pure_pure ⟨h, rfl, rfl⟩
  | query_bind input next ih =>
      rw [eraseProbeQueries, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          rw [runPrivateErasedPrefix_uniform_query_bind, runResolvedFromTable_uniform_query_bind]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel h
      | hashOutput =>
          rw [runPrivateErasedPrefix_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel h
      | ensure coordinate =>
          rw [runPrivateErasedPrefix_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
          exact ih () _ _ fuel (h.ensure coordinate)
      | publish coordinate =>
          rw [runPrivateErasedPrefix_publish_query_bind, runResolvedFromTable_publish_query_bind]
          exact ih () _ _ fuel (h.publish coordinate)
      | peek coordinate =>
          rw [runPrivateErasedPrefix_peek_query_bind, runResolvedFromTable_peek_query_bind]
          rw [h.stateValues]
          exact ih _ left right fuel h
      | probe coordinate digest =>
          rw [runPrivateErasedPrefix_probe_query_bind]
          cases fuel with
          | zero => exact relTriple_none_optionRefines _ _
          | succ fuel =>
              split_ifs
              · exact ih () left right fuel h
              · exact ih () _ right fuel (h.addPending_left coordinate digest)
      | reveal coordinate =>
          rw [runPrivateErasedPrefix_reveal_query_bind, runResolvedFromTable_reveal_query_bind]
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

theorem probEvent_privateErasedCandidate_le_probeFree
    (target : Position) (select : α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) :
    Pr[fun candidate => candidate ≠ none | privateErasedCandidate target (fun _ => select) computation context fuel table output] ≤
      Pr[fun result => result.bind (fun result => select result.value) ≠ none |
        runResolvedFromTable (replacePrivatePosition target output context) 0 table (eraseProbeQueries computation)] := by
  unfold privateErasedCandidate privateErasedPrefixValue
  simp only [probEvent_map, Function.comp_def]
  apply probEvent_le_of_relTriple
    (relTriple_runPrivateErasedPrefix_eraseProbeQueries target computation _ _ fuel table (PendingRelaxation.refl _))
  intro left right hrel hleft
  cases left with
  | none => simp at hleft
  | some left =>
      cases right with
      | none => exact False.elim hrel
      | some right => simpa only [Option.map_some, Option.bind_some, hrel.2.1] using hleft

end SphincsSecurity.Concrete.OtsProbeSimulation
