import SphincsSecurity.Proof.FtsProbeCostInvariant

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000 in
theorem probeCostInvariant_probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    ProbeCostInvariant parameter (probingHashQuery parameter input) := by
  intro table state cache fuel hcovered hfinite hit finalState output finalCache cost hresult
  rw [probingHashQuery_run_eq] at hresult
  cases hdecode : decodeProbe? parameter input with
  | none =>
      have hnot := (decodeProbe?_eq_none_iff parameter input).mp hdecode
      apply probeCostInvariant_splitHashQuery_nonprobe parameter input hnot
        table state cache fuel hcovered hfinite hit finalState output finalCache cost
      simpa only [hdecode] using hresult
  | some probe =>
      have hinput := (decodeProbe?_eq_some_iff parameter input probe).mp hdecode
      simp only [hdecode] at hresult
      rw [AdaptiveRevealProbe.probeQuery, AdaptiveRevealProbe.runCharged,
        OracleComp.construct_query_bind] at hresult
      cases fuel with
      | zero =>
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult
      | succ remaining =>
          cases hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) with
          | some revealed =>
              simp only [hrevealed] at hresult
              have hsupport := AdaptiveRevealProbe.runCharged_done_mem_support table state finalState remaining
                ((splitHashQuery (.ordinary input)).run cache) hit (output, finalCache) cost hresult
              obtain ⟨rfl, rfl⟩ := AdaptiveRevealProbe.runCharged_done_stateFree table state finalState remaining
                ((splitHashQuery (.ordinary input)).run cache) (splitHashQuery_stateFree _ cache)
                hit (output, finalCache) cost hresult
              rcases splitHashQuery_support_cache (.ordinary input) cache finalCache output hsupport with
                ⟨rfl, _⟩ | rfl
              · exact ⟨hcovered, hfinite, by omega⟩
              · rw [← hinput]
                have hcoveredAfter := hcovered.update_revealed probe output (by simp [hrevealed])
                have hsets := probeCachedInputs_update_probed parameter cache probe output
                refine ⟨hcoveredAfter, ?_, ?_⟩
                · change (probeCachedInputs parameter _).Finite
                  rw [hsets]
                  exact hfinite.insert _
                · change _ ≤ (probeCachedInputs parameter _).ncard
                  rw [hsets, Nat.add_zero]
                  exact Set.ncard_le_ncard (Set.subset_insert _ _) (hfinite.insert _)
          | none =>
              simp only [hrevealed, support_map, Set.mem_image] at hresult
              obtain ⟨⟨previousResult, previousCost⟩, hrest, heq⟩ := hresult
              have hfirst : previousResult = .done hit finalState (output, finalCache) := congrArg Prod.fst heq
              have hcost : previousCost + AdaptiveRevealProbe.pendingProbeCharge state
                  (probe.index, probe.tree, probe.leafIdx) probe.candidate = cost := congrArg Prod.snd heq
              rw [hfirst] at hrest
              have hsupport := AdaptiveRevealProbe.runCharged_done_mem_support table
                (state.addPending (probe.index, probe.tree, probe.leafIdx) probe.candidate) finalState remaining
                ((splitHashQuery (.ordinary input)).run cache) hit (output, finalCache) previousCost hrest
              obtain ⟨rfl, rfl⟩ := AdaptiveRevealProbe.runCharged_done_stateFree table
                (state.addPending (probe.index, probe.tree, probe.leafIdx) probe.candidate) finalState remaining
                ((splitHashQuery (.ordinary input)).run cache) (splitHashQuery_stateFree _ cache)
                hit (output, finalCache) previousCost hrest
              rw [Nat.zero_add] at hcost
              rw [← hcost]
              rcases splitHashQuery_support_cache (.ordinary input) cache finalCache output hsupport with
                ⟨rfl, hcached⟩ | rfl
              · have hmem : probe.candidate ∈ state.pending (probe.index, probe.tree, probe.leafIdx) := by
                  apply (hcovered probe ?_).resolve_left
                  · exact fun h => h hrevealed
                  · rw [hinput, hcached]
                    simp
                refine ⟨hcovered.addPending _ _, hfinite, ?_⟩
                rw [AdaptiveRevealProbe.pendingProbeCharge, if_pos hmem, Nat.add_zero]
              · rw [← hinput]
                refine ⟨hcovered.update_probed probe output, ?_,
                  hcovered.pendingCharge_le_cache_growth probe output hrevealed hfinite⟩
                change (probeCachedInputs parameter _).Finite
                rw [probeCachedInputs_update_probed]
                exact hfinite.insert _

theorem probeCostInvariant_hiddenFtsLeafHash (parameter : PublicParameter) (coordinate : Coordinate) :
    ProbeCostInvariant parameter (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (probeCostInvariant_splitHashQuery_hidden parameter coordinate).bind fun output =>
    ProbeCostInvariant.pure parameter (truncateHash output)

theorem probeCostInvariant_ordinaryTweakableHash (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput)
    (hordinary : ∀ table : Coordinate → Digest,
      IsOrdinaryInput parameter table (tweakableHashInput parameter domain payload)) :
    ProbeCostInvariant parameter (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (probeCostInvariant_splitHashQuery_nonprobe parameter _
    (no_probe_of_ordinary_all parameter _ hordinary)).bind fun output =>
      ProbeCostInvariant.pure parameter (truncateHash output)

end SphincsSecurity.Concrete.FtsProbeSimulation
