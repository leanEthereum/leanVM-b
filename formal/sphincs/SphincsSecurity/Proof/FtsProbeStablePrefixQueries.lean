import SphincsSecurity.Proof.FtsProbeJointQueryEvidence
import SphincsSecurity.Proof.FtsProbeJointSourceSupport
import SphincsSecurity.Proof.OuterHashQueryCapTrace
import SphincsSecurity.Proof.AdaptiveRevealProbeRevealed

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liftHashSource (computation : OracleComp HashSpec α) : OracleComp (OracleWorld + SigningSpec) α :=
  simulateQ (fun input => (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
    OracleComp (OracleWorld + SigningSpec) HashOutput)) computation

theorem liftHashSource_query_bind (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    liftHashSource ((liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput) >>= next) =
      ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
        OracleComp (OracleWorld + SigningSpec) HashOutput) >>= fun output => liftHashSource (next output)) := by
  rw [liftHashSource, simulateQ_bind, simulateQ_spec_query]
  rfl

theorem hiddenHitsRevealed_maskedJointStablePrefix
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp HashSpec α) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (project : β → γ) (q : Nat) (result : γ)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option γ × OtsProbeSimulation.SplitHashCache))
    (hbudget : q ≤ ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hstable : OtsProbeSimulation.QueriesStable parameter f computation)
    (hvalue : entry.value.1 = some result)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root
          (Option.map project <$> OtsProbeSimulation.capOuterHashQueries (liftHashSource computation >>= next) q)
          context fuel history cache).run ftsCache))) :
    HiddenHitsRevealed parameter table f finalState computation := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel history cache ftsCache with
  | pure value =>
      intro input hinput
      simp [queriedInputs_pure] at hinput
  | query_bind input tail ih =>
      have hinputStable : OtsProbeSimulation.StableOrdinaryInput parameter input :=
        hstable input (by rw [queriedInputs_query_bind]; exact List.mem_cons_self)
      rw [liftHashSource_query_bind, bind_assoc, OtsProbeSimulation.capOuterHashQueries_query_bind] at hresult
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
              obtain ⟨stepState, stepEntry, stepCache, hquery, htail⟩ :=
                mem_support_bindNativeSteps_hashQuery_some parameter table input state finalState remaining _
                  context fuel history cache ftsCache finalCache entry hresult
              obtain ⟨hclean', hsynced', _⟩ := invariants_maskedJointHashQuery parameter table input state stepState
                (remaining + 1) context fuel history cache ftsCache stepCache (some stepEntry) hclean hsynced hquery
              have hbudget' : q ≤ jointHashRemaining parameter input remaining :=
                (by omega : q ≤ remaining).trans (jointHashRemaining_ge parameter input remaining)
              have hbound : (Option.map project <$>
                  OtsProbeSimulation.capOuterHashQueries (liftHashSource (tail stepEntry.value.1) >>= next) q).IsQueryBoundP
                  OtsProbeSimulation.IsOuterHash (jointHashRemaining parameter input remaining) := by
                rw [isQueryBoundP_map_iff]
                exact (OtsProbeSimulation.capOuterHashQueries_hashBound _ q).mono hbudget'
              have hcache := stableMergedCacheLE_maskedJointComputation parameter root table _ stepState finalState
                (jointHashRemaining parameter input remaining) stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2
                stepCache finalCache entry hbound hclean' hsynced' htail
              have hcached := maskedJointHashQuery_stable_output_cached parameter table input state stepState remaining
                context fuel history cache ftsCache stepCache stepEntry hinputStable hclean hsynced hquery
              have houtput : f input = stepEntry.value.1 := hf (hcache input stepEntry.value.1 hinputStable hcached)
              have htailStable : OtsProbeSimulation.QueriesStable parameter f (tail stepEntry.value.1) := by
                intro target htarget
                apply hstable target
                rw [queriedInputs_query_bind, houtput]
                exact List.mem_cons_of_mem input htarget
              have htailRevealed := ih stepEntry.value.1 q stepState (jointHashRemaining parameter input remaining)
                stepEntry.context stepEntry.remaining stepEntry.history stepEntry.value.2 stepCache hbudget' hclean' hsynced' htailStable htail
              intro target htarget probe hdecode hhit
              rw [queriedInputs_query_bind] at htarget
              rcases List.mem_cons.mp htarget with hhead | hrest
              · subst target
                obtain ⟨value, hrevealed⟩ := maskedJointHashQuery_done_false_hit_revealed parameter table input probe state stepState
                  (remaining + 1) context fuel history cache ftsCache stepCache stepEntry hdecode hhit hquery
                exact ⟨value, AdaptiveRevealProbe.revealed_of_mem_runDetailed_done table state finalState (remaining + 1)
                  _ false _ _ value hrevealed hresult⟩
              · rw [houtput] at hrest
                exact htailRevealed target hrest probe hdecode hhit

end SphincsSecurity.Concrete.FtsProbeSimulation
