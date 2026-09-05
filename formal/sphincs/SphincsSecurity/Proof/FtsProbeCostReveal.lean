import SphincsSecurity.Proof.FtsProbeCostActions

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000 in
theorem runCharged_revealTail_bound (parameter : PublicParameter) (coordinate : Coordinate)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (revealedValue : Digest)
    (hcovered : ProbeCacheCovered parameter state cache) (hfinite : (splitProbeInputs parameter cache).Finite)
    (hknown : state.revealed coordinate ≠ none)
    (hit : Bool) (finalState : AdaptiveRevealProbe.State Coordinate) (value : Digest)
    (finalCache : SplitHashCache) (cost : Nat)
    (hresult : (.done hit finalState (value, finalCache), cost) ∈ support
      (AdaptiveRevealProbe.runCharged table state fuel
        ((splitHashQuery (.hiddenLeaf coordinate)).run cache >>= fun result =>
          pure (revealedValue, Function.update result.2
            (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2, revealedValue⟩ : FtsSecretProbe).input parameter))
            (some result.1))))) :
    ProbeCacheCovered parameter finalState finalCache ∧ (splitProbeInputs parameter finalCache).Finite ∧
      (splitProbeInputs parameter cache).ncard + cost ≤ (splitProbeInputs parameter finalCache).ncard := by
  let probe : FtsSecretProbe := ⟨coordinate.1, coordinate.2.1, coordinate.2.2, revealedValue⟩
  obtain ⟨middleState, ⟨answer, middleCache⟩, middleFuel, leftCost, rightCost,
      _, hfirst, hsecond, hcost⟩ := AdaptiveRevealProbe.runCharged_bind_done_support table
    ((splitHashQuery (.hiddenLeaf coordinate)).run cache)
    (fun result => pure (revealedValue, Function.update result.2 (.ordinary (probe.input parameter)) (some result.1)))
    state fuel hit finalState (value, finalCache) cost hresult
  obtain ⟨hcoveredMiddle, hfiniteMiddle, hcountMiddle⟩ :=
    probeCostInvariant_splitHashQuery_hidden parameter coordinate table state cache fuel hcovered hfinite
      _ middleState answer middleCache leftCost hfirst
  have hmiddleState := (AdaptiveRevealProbe.runCharged_done_stateFree table state middleState fuel
    ((splitHashQuery (.hiddenLeaf coordinate)).run cache) (splitHashQuery_stateFree _ cache)
    _ (answer, middleCache) leftCost hfirst).1
  simp only [AdaptiveRevealProbe.runCharged, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, AdaptiveRevealProbe.DetailedResult.done.injEq] at hsecond
  have hfinalState : finalState = middleState := hsecond.1.2.1
  have hfinalCache : finalCache = Function.update middleCache (.ordinary (probe.input parameter)) (some answer) :=
    hsecond.1.2.2.2
  have hrightCost : rightCost = 0 := hsecond.2
  rw [hfinalState, hfinalCache]
  have hknownMiddle : middleState.revealed (probe.index, probe.tree, probe.leafIdx) ≠ none := by
    simpa only [hmiddleState, probe] using hknown
  refine ⟨hcoveredMiddle.update_revealed probe answer hknownMiddle, ?_, ?_⟩
  · change (probeCachedInputs parameter _).Finite
    rw [probeCachedInputs_update_probed]
    exact hfiniteMiddle.insert _
  · change _ ≤ (probeCachedInputs parameter _).ncard
    rw [probeCachedInputs_update_probed]
    have hmono := Set.ncard_le_ncard (Set.subset_insert (probe.input parameter)
      (splitProbeInputs parameter middleCache)) (hfiniteMiddle.insert _)
    change _ ≤ (insert (probe.input parameter) (splitProbeInputs parameter middleCache)).ncard
    omega

set_option maxRecDepth 10000 in
theorem probeCostInvariant_revealFtsSecret (parameter : PublicParameter) (coordinate : Coordinate) :
    ProbeCostInvariant parameter (revealFtsSecret parameter coordinate) := by
  intro table state cache fuel hcovered hfinite hit finalState value finalCache cost hresult
  rw [revealFtsSecret_run_eq, AdaptiveRevealProbe.revealQuery,
    AdaptiveRevealProbe.runCharged, OracleComp.construct_query_bind] at hresult
  cases hrevealed : state.revealed coordinate with
  | some revealedValue =>
      simp only [hrevealed] at hresult
      exact runCharged_revealTail_bound parameter coordinate table state cache fuel revealedValue
        hcovered hfinite (by simp [hrevealed]) hit finalState value finalCache cost hresult
  | none =>
      simp only [hrevealed] at hresult
      split_ifs at hresult with hhit
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult
      · exact runCharged_revealTail_bound parameter coordinate table
          (state.install coordinate (table coordinate)) cache fuel (table coordinate)
          (hcovered.install coordinate (table coordinate)) hfinite
          (by simp [AdaptiveRevealProbe.State.install]) hit finalState value finalCache cost hresult

end SphincsSecurity.Concrete.FtsProbeSimulation
