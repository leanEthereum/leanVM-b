import SphincsSecurity.Proof.OtsProbeErasedHistoryPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def resolvedPrefixValue (result : Option (ResolvedRunResult α)) : Option α := result.map ResolvedRunResult.value

def historyPrefixValue (result : Option (HistoryResolvedPrefix α)) : Option α := result.map HistoryResolvedPrefix.value

theorem evalDist_completeHistoryResolvedPrefix_value_of_no_history
    (entry : HistoryResolvedPrefix α) (hhistory : entry.history = []) :
    evalDist (resolvedPrefixValue <$> completeHistoryResolvedPrefix (some entry)) = evalDist (pure (some entry.value) : ProbComp (Option α)) := by
  unfold completeHistoryResolvedPrefix completeResolvedHistory
  simp only [hhistory, ChainStartHistoryHit, List.not_mem_nil, false_and, exists_false, if_false,
    map_bind, map_pure, resolvedPrefixValue, Option.map_some]
  exact evalDist_sampleOtsHashTable_bind_const _

theorem evalDist_sampled_probeFree_value_eq_history_prefix
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (fuel : Nat)
    (hcovered : PendingCoveredBy [] context) (hcard : context.state.pending.card < Fintype.card Digest)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    evalDist (resolvedPrefixValue <$> (sampleOtsHashTable >>= fun base =>
      runResolvedFromTable context fuel (completedStartTable context.state base) computation)) =
      evalDist (historyPrefixValue <$> runResolvedHistoryPrefix computation context fuel []) := by
  have hd := evalDist_history_filtered_runResolved_eq_completion_of_probeFree [] computation context fuel hcovered hcard hbound
  simp only [ChainStartHistoryHit, List.not_mem_nil, false_and, exists_false, if_false] at hd
  rw [runResolvedHistoryCompletion_eq_adaptive_of_probeFree computation context fuel [] hbound,
    runResolvedHistoryAdaptive_eq_prefix_complete] at hd
  calc
    _ = evalDist (resolvedPrefixValue <$> (runResolvedHistoryPrefix computation context fuel [] >>= completeHistoryResolvedPrefix)) :=
      evalDist_map_eq_of_evalDist_eq hd _
    _ = _ := by
      rw [map_bind, map_eq_bind_pure_comp]
      apply evalDist_bind_congr
      intro entry hentry
      cases entry with
      | none => rfl
      | some entry =>
          exact evalDist_completeHistoryResolvedPrefix_value_of_no_history entry
            (historyPrefix_history_eq_of_probeFree computation context fuel [] entry hbound hentry)

def HistoryPrivateProbeCutReached (target : Position) (entry : Option (HistoryResolvedPrefix (PrivateValueCut α))) : Prop :=
  privatePositionAccessCandidate target (entry.map HistoryResolvedPrefix.value) ≠ none

noncomputable def erasedHistoryPrivateCutCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (ordinal : Nat) : ENNReal :=
  Pr[HistoryPrivateProbeCutReached target |
    runResolvedHistoryPrefix (eraseProbeQueries (privatePositionProbeCutAt target computation ordinal)) context 0 []]

theorem sampled_commonPrivateCutCharge_eq_erasedHistory
    (targets : Finset Position) (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] * commonPrivateCutCharge target computation (ensuredInitialContext targets) table ordinal) =
      erasedHistoryPrivateCutCharge target computation (ensuredInitialContext targets) ordinal := by
  have hcovered : PendingCoveredBy [] (ensuredInitialContext targets) := by
    intro entry hentry
    simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hentry
  have hcard : (ensuredInitialContext targets).state.pending.card < Fintype.card Digest := by
    simpa only [ensuredInitialContext, LazyRevealProbe.State.empty, Finset.card_empty] using Fintype.card_pos (α := Digest)
  have htable (base : OtsSecretIndex → HashOutput) : completedStartTable (ensuredInitialContext targets).state base = base := by
    funext index
    rfl
  have hd := evalDist_sampled_probeFree_value_eq_history_prefix
    (eraseProbeQueries (privatePositionProbeCutAt target computation ordinal)) (ensuredInitialContext targets) 0 hcovered hcard
    (eraseProbeQueries_probeFree _)
  simp only [htable] at hd
  have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd (p := fun cut => privatePositionAccessCandidate target cut ≠ none)
  unfold commonPrivateCutCharge erasedHistoryPrivateCutCharge PrivateProbeCutReached HistoryPrivateProbeCutReached
  simpa only [probEvent_map, Function.comp_def, resolvedPrefixValue, historyPrefixValue, probEvent_bind_eq_tsum,
    commonPrivateCutCharge, PrivateProbeCutReached, erasedHistoryPrivateCutCharge, HistoryPrivateProbeCutReached] using hp

theorem sampled_sum_commonPrivateCutCharge_eq_erasedHistory
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q, commonPrivateCutCharge target computation (ensuredInitialContext targets) table ordinal) =
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        erasedHistoryPrivateCutCharge target computation (ensuredInitialContext targets) ordinal := by
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro target _
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro ordinal _
  exact sampled_commonPrivateCutCharge_eq_erasedHistory targets target computation ordinal

end SphincsSecurity.Concrete.OtsProbeSimulation
