import SphincsSecurity.Proof.FewTimeOccupancyGrowth
import SphincsSecurity.Proof.CachedSigningViews

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedOptionalSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => observedSigningView? answers root (log.get slot)

theorem coverageOccupancyMoment_mono {n : Nat} (first second : Fin n → Option FewTimeView)
    (hviews : ∀ slot view, first slot = some view → second slot = some view) :
    coverageOccupancyMoment first ≤ coverageOccupancyMoment second := by
  apply Finset.sum_le_sum
  intro index _
  apply Nat.pow_le_pow_left
  apply Finset.card_le_card
  intro slot hslot
  obtain ⟨view, hview, hindex⟩ := (Finset.mem_filter.mp hslot).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, view, hviews slot view hview, hindex⟩

theorem eligibleSigningView?_some_observed {answers : HashInput → Option HashOutput} {root : Digest}
    {payload : HashInput} {entry : SigningEntry} {view : FewTimeView}
    (hview : eligibleSigningView? answers root payload entry = some view) : observedSigningView? answers root entry = some view := by
  unfold eligibleSigningView? at hview
  cases hresponse : entry.2 with
  | none => simp [hresponse] at hview
  | some signature =>
      rw [hresponse] at hview
      change (if messageDigestPayload root entry.1 signature.randomness = payload then none
        else observedSigningView? answers root entry) = some view at hview
      split_ifs at hview with hsame
      exact hview

theorem eligibleSigningViews_occupancy_le (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) :
    coverageOccupancyMoment (eligibleSigningViews answers root payload log) ≤
      coverageOccupancyMoment (observedOptionalSigningViews answers root log) :=
  coverageOccupancyMoment_mono _ _ (fun _ _ hview => eligibleSigningView?_some_observed hview)

theorem observedSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    observedSigningView? (messageAnswers parameter after) root entry = observedSigningView? (messageAnswers parameter before) root entry := by
  cases hresponse : entry.2 with
  | none => simp [observedSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [observedSigningView?, hresponse, houtput, hafter]

theorem observedOptionalSigningViews_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    observedOptionalSigningViews (messageAnswers parameter after) root log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  exact observedSigningView?_cache_stable parameter root before after hcache (log.get slot) (hsigned _ (List.get_mem _ _))

theorem signingSlotsAtIndex_log_card {α : Type} (log : List α) (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0)).sum := by
  rw [signingSlotsAtIndex, Finset.card_eq_sum_ones, Finset.sum_filter, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0))

theorem signingSlotsAtIndex_log_append_card {α : Type} (log : List α) (entry : α)
    (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view ((log ++ [entry]).get slot)) index).card =
      (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card +
        if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0 := by
  simp only [signingSlotsAtIndex_log_card, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]

theorem observedOptionalSigningViews_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (hnone : observedSigningView? answers root entry = none) :
    coverageOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) =
      coverageOccupancyMoment (observedOptionalSigningViews answers root log) := by
  unfold coverageOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero]

theorem observedOptionalSigningViews_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (source : FewTimeView)
    (hsome : observedSigningView? answers root entry = some source) :
    coverageOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) =
      coverageOccupancyMoment (observedOptionalSigningViews answers root log) +
        occupancyIncrementAtIndex (observedOptionalSigningViews answers root log) source.1 := by
  rw [← coverageOccupancyMoment_insert_eq]
  unfold coverageOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, signingSlotsAtIndex_insert_card, hsome, Option.some.injEq, exists_eq_left']

theorem freshCoverageCharge_le_observedOccupancy (parameter : PublicParameter) (before cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (input : HashInput) :
    freshCoverageCharge parameter (fixedSigningViews parameter before root log) cache input ≤
      if cache input = none ∧ FtsProbeSimulation.MessageHashInput parameter input then
        (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers parameter before) root log) : ENNReal) else 0 := by
  unfold freshCoverageCharge
  split_ifs
  · exact Nat.cast_le.mpr (eligibleSigningViews_occupancy_le _ _ _ _)
  · exact le_rfl

end SphincsSecurity.Concrete
