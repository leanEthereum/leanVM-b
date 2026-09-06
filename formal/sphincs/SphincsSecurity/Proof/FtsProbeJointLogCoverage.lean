import SphincsSecurity.Proof.FtsProbeJointSourceSupport
import SphincsSecurity.Proof.FtsProbeJointQuerySupport
import SphincsSecurity.Proof.FtsProbeStableDigestTransport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedJointSign OtsProbeSimulation.maskedPublishedChronologicalSign

theorem revealedOnlyFrom_maskedJointSigningTrace_map
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (project : α × QueryLog SigningSpec → β) (log : QueryLog SigningSpec)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (β × OtsProbeSimulation.SplitHashCache))
    (hbound : (project <$> signingTraceComputation computation).IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hlog : ∀ value tail, project (value, tail) = entry.value.1 → ∀ signed, signed ∈ tail → signed ∈ log)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation secretKey.parameter secretKey.root
          (project <$> signingTraceComputation computation) context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log) := by
  induction computation using OracleComp.inductionOn generalizing project state ftsFuel context fuel history cache ftsCache with
  | pure value =>
      simp only [signingTraceComputation, construct_pure, map_pure, maskedJointComputation] at hresult
      have hstate := state_eq_liftNativeBlock table state finalState ftsFuel _ context fuel history cache ftsCache finalCache (some entry) hresult
      rw [hstate]
      exact fun _ _ h => Or.inl h
  | query_bind input next ih =>
      simp only [signingTraceComputation_query_bind, map_bind, Functor.map_map] at hbound hresult
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [maskedJointComputation_query_bind] at hresult
      have finish (reply : (OracleWorld + SigningSpec).Range input)
          (stepState : AdaptiveRevealProbe.State Coordinate) (stepFuel : Nat)
          (stepEntry : OtsProbeSimulation.HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range input × OtsProbeSimulation.SplitHashCache))
          (stepCache : SplitHashCache)
          (hstepClean : AdaptiveRevealProbe.tableHits stepState table = false)
          (hstepSynced : RevealedSynced secretKey.parameter table stepState stepCache)
          (hbudget : ((project ∘ fun result => (result.1, signingLogFragment input reply ++ result.2)) <$>
            signingTraceComputation (next reply)).IsQueryBoundP OtsProbeSimulation.IsOuterHash stepFuel)
          (htail : .done false finalState (some entry, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table stepState stepFuel
              ((maskedJointComputation secretKey.parameter secretKey.root
                ((project ∘ fun result => (result.1, signingLogFragment input reply ++ result.2)) <$>
                  signingTraceComputation (next reply)) stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2).run stepCache)))
          (hprefix : (∀ signed, signed ∈ signingLogFragment input reply → signed ∈ log) →
            StableMergedCacheLE secretKey.parameter table stepCache finalCache →
            RevealedOnlyFrom state stepState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log)) :
          RevealedOnlyFrom state finalState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log) := by
        have hsource := mem_support_source_of_maskedJointComputation secretKey.parameter secretKey.root table _
          stepState finalState stepFuel stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache finalCache entry
          hbudget hstepClean hstepSynced htail
        rw [support_map] at hsource
        obtain ⟨pair, _, hpair⟩ := hsource
        have hfragment : ∀ signed, signed ∈ signingLogFragment input reply → signed ∈ log := by
          intro signed hsigned
          exact hlog pair.1 (signingLogFragment input reply ++ pair.2) hpair signed (List.mem_append_left _ hsigned)
        have hstable := stableMergedCacheLE_maskedJointComputation secretKey.parameter secretKey.root table _
          stepState finalState stepFuel stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache finalCache entry
          hbudget hstepClean hstepSynced htail
        have hbefore := hprefix hfragment hstable
        have hafter := ih reply (project ∘ fun result => (result.1, signingLogFragment input reply ++ result.2))
          stepState stepFuel stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache
          hbudget hstepClean hstepSynced (by
            intro value tail hvalue signed hsigned
            exact hlog value (signingLogFragment input reply ++ tail) hvalue signed (List.mem_append_right _ hsigned)) htail
        intro coordinate value hrevealed
        rcases hafter coordinate value hrevealed with hmiddle | hnew
        · exact hbefore coordinate value hmiddle
        · exact Or.inr hnew
      cases input with
      | inl world =>
          cases world with
          | inl n =>
              rcases mem_support_bindNativeSteps_done table state finalState ftsFuel _ _ context fuel history cache
                ftsCache finalCache (some entry) hclean (liftNativeBlock_probeFree _ context fuel history cache) hresult with
                ⟨hno, _⟩ | ⟨stepState, stepEntry, stepCache, hleft, htail⟩
              · cases hno
              · obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock secretKey.parameter table state stepState ftsFuel
                  (OtsProbeSimulation.splitUniformImpl n)
                  (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
                  context fuel history cache ftsCache stepCache (some stepEntry) hsynced hleft
                apply finish stepEntry.value.1 stepState ftsFuel stepEntry stepCache (by simpa [hstate] using hclean) hsynced'
                  (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 stepEntry.value.1) htail
                intro _ _
                rw [hstate]
                exact fun _ _ h => Or.inl h
          | inr query =>
              have hpositive : 0 < ftsFuel := by simpa [OtsProbeSimulation.IsOuterHash] using hbound.1
              cases ftsFuel with
              | zero => omega
              | succ remaining =>
                  obtain ⟨stepState, stepEntry, stepCache, hleft, htail⟩ :=
                    mem_support_bindNativeSteps_hashQuery_some secretKey.parameter table query state finalState remaining _
                      context fuel history cache ftsCache finalCache entry hresult
                  obtain ⟨hclean', hsynced', hreveal⟩ := invariants_maskedJointHashQuery secretKey.parameter table query state stepState
                    (remaining + 1) context fuel history cache ftsCache stepCache (some stepEntry) hclean hsynced hleft
                  have htailBound : ((project ∘ fun result => (result.1, signingLogFragment (.inl (.inr query)) stepEntry.value.1 ++ result.2)) <$>
                      signingTraceComputation (next stepEntry.value.1)).IsQueryBoundP OtsProbeSimulation.IsOuterHash remaining := by
                    simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 stepEntry.value.1
                  apply finish stepEntry.value.1 stepState (jointHashRemaining secretKey.parameter query remaining) stepEntry stepCache hclean' hsynced'
                    (htailBound.mono (jointHashRemaining_ge secretKey.parameter query remaining)) htail
                  intro _ _ coordinate value hrevealed
                  exact Or.inl (hreveal ▸ hrevealed)
      | inr message =>
          rcases mem_support_bindNativeSteps_done table state finalState ftsFuel _ _ context fuel history cache
            ftsCache finalCache (some entry) hclean (maskedJointSign_probeFree secretKey.parameter secretKey.root message context fuel history cache) hresult with
            ⟨hno, _⟩ | ⟨stepState, stepEntry, stepCache, hleft, htail⟩
          · cases hno
          · have hclean' := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state stepState ftsFuel _ false _ hleft
            have hsynced' := revealedSynced_maskedJointSign secretKey.parameter secretKey.root table message state stepState ftsFuel
              context fuel history cache ftsCache stepCache (some stepEntry) hclean hsynced hleft
            apply finish stepEntry.value.1 stepState ftsFuel stepEntry stepCache hclean' hsynced'
              (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 stepEntry.value.1) htail
            intro hfragment hstable
            have horigin := revealedOnlyFrom_maskedJointSign_laterCache secretKey table message state stepState ftsFuel
              context fuel history cache ftsCache stepCache finalCache stepEntry hclean hsynced hstable f hf hleft
            intro coordinate value hrevealed
            rcases horigin coordinate value hrevealed with hold | hnew
            · exact Or.inl hold
            · obtain ⟨message', signature, index, leaves, hentry, hdigest, hcoordinate⟩ := hnew
              exact Or.inr ⟨message', signature, index, leaves, hfragment _ hentry, hdigest, hcoordinate⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
