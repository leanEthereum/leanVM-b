import SphincsSecurity.Proof.FtsProbeJointSourceSupport
import SphincsSecurity.Proof.FtsProbeJointQuerySupport
import SphincsSecurity.Proof.OuterHashQueryCapTrace

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedJointSign OtsProbeSimulation.maskedPublishedChronologicalSign

theorem mem_support_jointCapped_after_prefix
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (project : β → γ) (q : Nat) (result : γ)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option γ × OtsProbeSimulation.SplitHashCache))
    (hbudget : q ≤ ftsFuel) (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hvalue : entry.value.1 = some result)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root
          (Option.map project <$> OtsProbeSimulation.capOuterHashQueries (computation >>= next) q)
          context fuel history cache).run ftsCache))) :
    ∃ value stepState capFuel stepFuel stepContext nativeFuel stepHistory nativeCache stepCache,
      capFuel ≤ stepFuel ∧ AdaptiveRevealProbe.tableHits stepState table = false ∧
      RevealedSynced parameter table stepState stepCache ∧
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState stepFuel
          ((maskedJointComputation parameter root (Option.map project <$> OtsProbeSimulation.capOuterHashQueries (next value) capFuel)
            stepContext nativeFuel stepHistory nativeCache).run stepCache)) := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel history cache ftsCache with
  | pure value =>
      exact ⟨value, state, q, ftsFuel, context, fuel, history, cache, ftsCache, hbudget, hclean, hsynced, by simpa using hresult⟩
  | query_bind input tail ih =>
      rw [bind_assoc, OtsProbeSimulation.capOuterHashQueries_query_bind] at hresult
      cases input with
      | inl world =>
          cases world with
          | inl n =>
              simp only [OtsProbeSimulation.IsOuterHash, if_false, map_bind] at hresult
              rw [maskedJointComputation_query_bind] at hresult
              rcases mem_support_bindNativeSteps_done table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache
                (some entry) hclean (liftNativeBlock_probeFree _ context fuel history cache) hresult with
                ⟨hno, _⟩ | ⟨stepState, stepEntry, stepCache, hleft, htail⟩
              · cases hno
              · obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel
                  (OtsProbeSimulation.splitUniformImpl n)
                  (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
                  context fuel history cache ftsCache stepCache (some stepEntry) hsynced hleft
                exact ih stepEntry.value.1 q stepState ftsFuel stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache
                  hbudget (by simpa [hstate] using hclean) hsynced' htail
          | inr input =>
              simp only [OtsProbeSimulation.IsOuterHash, if_true] at hresult
              cases q with
              | zero =>
                  simp only [map_pure, Option.map_none] at hresult
                  have hsource := mem_support_source_of_maskedJointComputation parameter root table (pure (none : Option γ))
                    state finalState ftsFuel context fuel history cache ftsCache finalCache entry (by simp) hclean hsynced hresult
                  simp only [mem_support_pure_iff] at hsource
                  rw [hvalue] at hsource
                  cases hsource
              | succ q =>
                  cases ftsFuel with
                  | zero => omega
                  | succ remaining =>
                      simp only [map_bind] at hresult
                      rw [maskedJointComputation_query_bind] at hresult
                      obtain ⟨stepState, stepEntry, stepCache, hleft, htail⟩ := mem_support_bindNativeSteps_hashQuery_some parameter table input
                        state finalState remaining _ context fuel history cache ftsCache finalCache entry hresult
                      obtain ⟨hclean', hsynced', _⟩ := invariants_maskedJointHashQuery parameter table input state stepState (remaining + 1)
                        context fuel history cache ftsCache stepCache (some stepEntry) hclean hsynced hleft
                      exact ih stepEntry.value.1 q stepState (jointHashRemaining parameter input remaining)
                        stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache
                        ((by omega : q ≤ remaining).trans (jointHashRemaining_ge parameter input remaining)) hclean' hsynced' htail
      | inr message =>
          simp only [OtsProbeSimulation.IsOuterHash, if_false, map_bind] at hresult
          rw [maskedJointComputation_query_bind] at hresult
          rcases mem_support_bindNativeSteps_done table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache
            (some entry) hclean (maskedJointSign_probeFree parameter root message context fuel history cache) hresult with
            ⟨hno, _⟩ | ⟨stepState, stepEntry, stepCache, hleft, htail⟩
          · cases hno
          · have hclean' := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state stepState ftsFuel _ false _ hleft
            have hsynced' := revealedSynced_maskedJointSign parameter root table message state stepState ftsFuel context fuel history cache
              ftsCache stepCache (some stepEntry) hclean hsynced hleft
            exact ih stepEntry.value.1 q stepState ftsFuel stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache
              hbudget hclean' hsynced' htail

end SphincsSecurity.Concrete.FtsProbeSimulation
