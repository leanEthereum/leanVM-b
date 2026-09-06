import SphincsSecurity.Proof.OtsProbeCappedPrivateGame
import SphincsSecurity.Proof.OtsProbeHistoryQueryPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

theorem PendingRelaxation.no_missingChainStartHit
    {left right : DeferredContext} (h : PendingRelaxation left right) (table : OtsSecretIndex → HashOutput)
    (hleft : ¬MissingChainStartHit table left) : ¬MissingChainStartHit table right := by
  rintro ⟨index, hmissing, hhit⟩
  exact hleft ⟨index, by rw [h.stateValues]; exact hmissing, h.hitAt _ _ hhit⟩

theorem relTriple_resolveDeferredReveal_avoiding_pendingRelaxation
    (position : Position) (left right : DeferredContext) (h : PendingRelaxation left right)
    (hcard : left.state.pending.card < Fintype.card Digest) :
    RelTriple (resolveDeferredReveal (startTableAvoidingPending left) position left)
      (resolveDeferredReveal (startTableAvoidingPending right) position right) (OptionRefines PendingResolutionRel) := by
  have hright : right.state.pending.card < Fintype.card Digest := (Finset.card_le_card h.pending).trans_lt hcard
  apply relTriple_of_evalDist_eq_right
    (evalDist_resolveDeferredReveal_eq_of_no_missingChainStartHit (startTableAvoidingPending right)
      (startTableAvoidingPending left) position right (startTableAvoidingPending_no_missingHit right hright)
      (h.no_missingChainStartHit _ (startTableAvoidingPending_no_missingHit left hcard))).symm
  exact relTriple_resolveDeferredReveal_pendingRelaxation _ position left right h

def PendingHistoryPrefixRel (left right : HistoryResolvedPrefix α) : Prop :=
  PendingRelaxation left.context right.context ∧ left.value = right.value

theorem relTriple_runResolvedHistoryPrefix_eraseProbeQueries
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (h : PendingRelaxation left right)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hcard : left.state.pending.card + bound < Fintype.card Digest) :
    RelTriple (runResolvedHistoryPrefix computation left fuel history)
      (runResolvedHistoryPrefix (eraseProbeQueries computation) right 0 []) (OptionRefines PendingHistoryPrefixRel) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel bound history with
  | pure value => exact relTriple_pure_pure ⟨h, rfl⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryPrefix_query_bind, eraseProbeQueries, construct_query_bind]
      cases input with
      | uniform n =>
          rw [runResolvedHistoryPrefix_query_bind]
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel bound history h (hbound.2 a) hcard
      | hashOutput =>
          rw [runResolvedHistoryPrefix_query_bind]
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          apply relTriple_bind (relTriple_refl _)
          intro a b hab
          subst b
          exact ih a left right fuel bound history h (hbound.2 a) hcard
      | ensure coordinate =>
          rw [runResolvedHistoryPrefix_query_bind]
          exact ih () _ _ fuel bound history (h.ensure coordinate) (hbound.2 ()) hcard
      | publish coordinate =>
          rw [runResolvedHistoryPrefix_query_bind]
          exact ih () _ _ fuel bound history (h.publish coordinate) (hbound.2 ()) hcard
      | peek coordinate =>
          rw [runResolvedHistoryPrefix_query_bind]
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, h.stateValues]
          exact ih _ left right fuel bound history h (hbound.2 _) hcard
      | probe coordinate digest =>
          have hpositive : 0 < bound := by simpa [LazyRevealProbe.IsProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP LazyRevealProbe.IsProbe (bound - 1) := hbound.2 ()
          cases fuel with
          | zero => exact relTriple_none_optionRefines _ _
          | succ fuel =>
              simp only [historyAdaptiveQueryStep]
              split_ifs
              · exact ih () left right fuel (bound - 1) history h htail (by omega)
              · apply ih () _ right fuel (bound - 1) _ (h.addPending_left coordinate digest) htail
                have hsize := Finset.card_insert_le (coordinate, digest) left.state.pending
                change (insert (coordinate, digest) left.state.pending).card + (bound - 1) < _
                omega
      | reveal coordinate =>
          rw [runResolvedHistoryPrefix_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate]
              rw [← h.stateValues]
              cases hknown : left.state.values (.chainStart lay tree leafIdx chainIdx) with
              | none =>
                  simp only
                  apply relTriple_bind (relTriple_refl _)
                  intro a b hab
                  subst b
                  simp only [ChainStartHistoryOutputHit, List.not_mem_nil, false_and, exists_false, if_false]
                  split_ifs
                  · exact relTriple_none_optionRefines _ _
                  · apply ih a _ _ fuel bound history (h.materialize _ a _ _ h.privateValues) (hbound.2 a)
                    change (left.state.materialize (.chainStart lay tree leafIdx chainIdx) a).pending.card + bound < _
                    exact (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) bound).trans_lt hcard
              | some output =>
                  simp only
                  by_cases hhit : left.state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · rw [if_pos hhit]
                    exact relTriple_none_optionRefines _ _
                  · have hright : ¬right.state.hitAt (.chainStart lay tree leafIdx chainIdx) output := fun hh => hhit (h.hitAt _ _ hh)
                    rw [if_neg hhit, if_neg hright]
                    apply ih output _ _ fuel bound history (h.materialize _ output _ _ h.privateValues) (hbound.2 output)
                    exact (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) bound).trans_lt hcard
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
              apply relTriple_bind (relTriple_resolveDeferredReveal_avoiding_pendingRelaxation position left right h (by omega))
              intro a b hab
              cases a with
              | none => exact relTriple_none_optionRefines _ _
              | some a =>
                  cases b with
                  | none => exact False.elim hab
                  | some b =>
                      have ho : a.output = b.output := hab.2
                      dsimp only
                      rw [ho]
                      apply ih b.output _ _ fuel bound history (h.materialize _ b.output _ _ hab.1.privateValues) (hbound.2 _)
                      exact (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) bound).trans_lt hcard

def IsChainStartCut : PrivateValueCut α → Prop
  | .query (.probe (.chainStart _ _ _ _) _) _ => True
  | _ => False

def HistoryChainStartCutReached (entry : Option (HistoryResolvedPrefix (PrivateValueCut α))) : Prop :=
  ∃ result, entry = some result ∧ IsChainStartCut result.value

theorem prefixUnresolvedStartCharge_le_chainStart_indicator
    (entry : Option (HistoryResolvedPrefix (PrivateValueCut α))) :
    prefixUnresolvedStartCharge nativeCutCandidate entry ≤ if HistoryChainStartCutReached entry then 1 else 0 := by
  by_cases hstart : HistoryChainStartCutReached entry
  · rw [if_pos hstart]
    exact prefixUnresolvedStartCharge_le_one nativeCutCandidate entry
  · rw [if_neg hstart]
    cases entry with
    | none => rfl
    | some entry =>
        have hcut : ¬IsChainStartCut entry.value := fun hh => hstart ⟨entry, rfl, hh⟩
        obtain ⟨context, fuel, value, history⟩ := entry
        cases value with
        | done value => simp [prefixUnresolvedStartCharge, nativeCutCandidate, unresolvedStartCandidateCharge]
        | query input next =>
            cases input <;> try simp [prefixUnresolvedStartCharge, nativeCutCandidate, unresolvedStartCandidateCharge]
            case probe coordinate digest =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx => exact (hcut trivial).elim
              | position position => rfl

noncomputable def erasedHistoryStartCutCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (ordinal : Nat) : ENNReal :=
  Pr[HistoryChainStartCutReached | runResolvedHistoryPrefix (eraseProbeQueries (nativeProbeCutAt computation ordinal)) context 0 []]

theorem nativeStartPrefixCharge_le_erasedHistoryStartCutCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat)
    (hordinal : ordinal < Fintype.card Digest) :
    nativeStartPrefixCharge targets computation fuel ordinal ≤
      erasedHistoryStartCutCharge computation (ensuredInitialContext targets) ordinal := by
  have hcouple := relTriple_runResolvedHistoryPrefix_eraseProbeQueries (nativeProbeCutAt computation ordinal)
    (ensuredInitialContext targets) (ensuredInitialContext targets) fuel ordinal [] (PendingRelaxation.refl _)
    (nativeProbeCutAt_probeBound computation ordinal) (by simpa [ensuredInitialContext, LazyRevealProbe.State.empty] using hordinal)
  have hc := expected_cost_le_of_relTriple hcouple (prefixUnresolvedStartCharge nativeCutCandidate)
    (fun entry => if HistoryChainStartCutReached entry then (1 : ENNReal) else 0) (fun _ => 0) (by
      intro left right hrel
      rw [add_zero]
      apply (prefixUnresolvedStartCharge_le_chainStart_indicator left).trans
      by_cases hleft : HistoryChainStartCutReached left
      · obtain ⟨entry, rfl, hentry⟩ := hleft
        cases right with
        | none => exact False.elim hrel
        | some right =>
            have hright : HistoryChainStartCutReached (some right) := ⟨right, rfl, by rw [← hrel.2]; exact hentry⟩
            simp only [if_pos (show HistoryChainStartCutReached (some entry) from ⟨entry, rfl, hentry⟩), if_pos hright]
            exact le_rfl
      · simp only [if_neg hleft]
        exact bot_le)
  simpa only [nativeStartPrefixCharge, erasedHistoryStartCutCharge, probEvent_eq_tsum_ite,
    mul_ite, mul_one, mul_zero, tsum_zero, add_zero] using hc

end SphincsSecurity.Concrete.OtsProbeSimulation
