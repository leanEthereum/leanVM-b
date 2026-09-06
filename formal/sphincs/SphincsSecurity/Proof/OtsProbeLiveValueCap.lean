import SphincsSecurity.Proof.OtsProbeHistoryCutCap
import SphincsSecurity.Proof.OtsProbeNativeErasedFts

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def flattenCappedLiveValue (result : Option (Nat × Option α)) : Option (Nat × α) :=
  result.bind fun result => result.2.map fun value => (result.1, value)

theorem evalDist_runResolvedLiveValue_cap
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (q : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    evalDist (runResolvedLiveValue table context fuel computation) =
      evalDist (flattenCappedLiveValue <$> runResolvedLiveValue table context fuel (capProbeQueries computation q)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table q with
  | pure value =>
      simp only [capProbeQueries, nativeProbeCutAt, construct_pure, map_pure, privateCutValue,
        runResolvedLiveValue, runResolvedFromTable, construct_pure, pure_bind]
      split_ifs <;> rfl
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · have hbound := (liveResolvedQueryBound_query_bind _ _ _ _ _ _ _).mp hbound hcomplete
        rw [capProbeQueries_query_bind_of_positive input next q hbound.1,
          evalDist_runResolvedLiveValue_bind table context fuel _ _ hconsistent hstarts]
        have hd := evalDist_map_eq_of_evalDist_eq
          (evalDist_runResolvedLiveValue_bind table context fuel (liftM (OracleSpec.query input))
            (fun reply => capProbeQueries (next reply) (if LazyRevealProbe.IsProbe input then q - 1 else q)) hconsistent hstarts)
          flattenCappedLiveValue
        rw [hd, map_bind]
        apply evalDist_bind_congr
        intro result hresult
        cases result with
        | none => rfl
        | some result =>
            have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input))
              context fuel table result hconsistent hstarts hresult
            exact ih result.value result.context result.remaining result.table _ hcore.2.1
              (by rw [hcore.1]; exact hcore.2.2) (by
                by_cases hp : LazyRevealProbe.IsProbe input <;>
                  simpa only [hp, if_true, if_false] using hbound.2 result hresult)
      · rw [evalDist_runResolvedLiveValue_eq_none_of_not_completable table context fuel _ hconsistent hstarts hcomplete]
        have hd := evalDist_map_eq_of_evalDist_eq
          (evalDist_runResolvedLiveValue_eq_none_of_not_completable table context fuel (capProbeQueries ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) q)
            hconsistent hstarts hcomplete) flattenCappedLiveValue
        rw [hd]
        rfl

theorem liveResolvedQueryBound_map_iff
    (predicate : LazyRevealProbe.Query Coordinate → Prop)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (project : α → β)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    LiveResolvedQueryBound predicate (project <$> computation) q context fuel table ↔
      LiveResolvedQueryBound predicate computation q context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table q with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [map_bind, liveResolvedQueryBound_query_bind]
      exact forall_congr' fun _ => and_congr Iff.rfl (forall_congr' fun result =>
        forall_congr' fun _ => ih result.value _ _ _ _)

theorem probEvent_live_value_le_capped_raw
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (q : Nat)
    (event : α → Prop)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    Pr[fun result => ∃ remaining value, result = some (remaining, value) ∧ event value |
      runResolvedLiveValue table context fuel computation] ≤
      Pr[fun result => ∃ entry value, result = some entry ∧ entry.value = some value ∧ event value |
        runResolvedFromTable context fuel table (capProbeQueries computation q)] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_runResolvedLiveValue_cap computation context fuel table q hconsistent hstarts hbound), probEvent_map]
  unfold runResolvedLiveValue
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result with
  | none => simp [flattenCappedLiveValue]
  | some result =>
      dsimp only
      by_cases hcomplete : DeferredCompletable table result.context
      · simp only [if_pos hcomplete, probEvent_pure]
        cases hvalue : result.value <;> simp [flattenCappedLiveValue, hvalue]
      · simp [hcomplete, flattenCappedLiveValue]

theorem probEvent_live_value_eq_retained
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (event : α → Prop)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun result => ∃ remaining value, result = some (remaining, value) ∧ event value |
      runResolvedLiveValue table context fuel computation] =
      Pr[fun result => ∃ value, resolvedPrefixValue (retainCompletableResult result) = some value ∧ event value |
        runResolvedFromTable context fuel table computation] := by
  unfold runResolvedLiveValue
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable context fuel table computation)
  · cases result with
    | none => simp [retainCompletableResult, resolvedPrefixValue]
    | some result =>
        have htable := (resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult).1
        by_cases hcomplete : DeferredCompletable table result.context <;>
          simp [retainCompletableResult, resolvedPrefixValue, htable, hcomplete]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem probEvent_capped_erased_value_le_uncapped
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (event : α → Prop) :
    Pr[fun entry => ∃ value, historyPrefixValue entry = some (some value) ∧ event value |
      runResolvedHistoryPrefix (eraseProbeQueries (capProbeQueries computation q)) context 0 []] ≤
      Pr[fun entry => ∃ value, historyPrefixValue entry = some value ∧ event value |
        runResolvedHistoryPrefix (eraseProbeQueries computation) context 0 []] := by
  conv_rhs => rw [← nativeProbeCutAt_resume computation q]
  rw [capProbeQueries, eraseProbeQueries_map, runResolvedHistoryPrefix_map, probEvent_map,
    eraseProbeQueries_bind, runResolvedHistoryPrefix_bind, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro entry
  cases entry with
  | none => simp [historyPrefixValue]
  | some entry =>
      obtain ⟨context, remaining, cut, history⟩ := entry
      cases cut with
      | done value =>
          simp [privateCutValue, PrivateValueCut.resume, eraseProbeQueries, runResolvedHistoryPrefix, historyPrefixValue]
      | query input next =>
          simp [historyPrefixValue, privateCutValue]

end SphincsSecurity.Concrete.OtsProbeSimulation
