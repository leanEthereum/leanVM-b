import SphincsSecurity.Proof.JointProbeResolvedHashBind

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem jointResolvedCoupledAt_computation
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceComputation parameter root computation)
      (simulateQ (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root
        (fun index tree leaf => table (index, tree, leaf))) computation) context fuel otsTable cache := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel otsTable cache with
  | pure value =>
      exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel (pure value)
        (fun _ => OtsProbeSimulation.CacheMapCommutes.pure _ value) context fuel otsTable cache hclean
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [jointSourceComputation, construct_query_bind, simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl world =>
          cases world with
          | inl n =>
              apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache
                (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
              · exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel (OtsProbeSimulation.splitUniformImpl n)
                  (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n)) context fuel otsTable cache hclean
              · intro finalState entry hresult
                obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state finalState ftsFuel
                  (OtsProbeSimulation.splitUniformImpl n) (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
                  context fuel otsTable cache entry hsynced hresult
                exact ih entry.value.1 finalState ftsFuel entry.context entry.remaining entry.table entry.value.2
                  (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1) (by simpa [hstate] using hclean) hsynced'
          | inr input =>
              have hpositive : 0 < ftsFuel := by simpa [OtsProbeSimulation.IsOuterHash] using hbound.1
              cases ftsFuel with
              | zero => omega
              | succ remaining =>
                  apply jointResolvedCoupledAt_hashQuery_bind parameter table input state remaining _ _ context fuel otsTable cache hclean hsynced
                  intro finalState entry hresult
                  have hclean' := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState (remaining + 1) _ false _ hresult
                  have hsynced' := revealedSynced_jointSourceHashQuery parameter table input state finalState (remaining + 1)
                    context fuel otsTable cache entry hclean hsynced hresult
                  apply ih entry.value.1 finalState (jointHashRemaining parameter input remaining)
                    entry.context entry.remaining entry.table entry.value.2 _ hclean' hsynced'
                  have htail : (next entry.value.1).IsQueryBoundP OtsProbeSimulation.IsOuterHash remaining := by
                    simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1
                  exact htail.mono (jointHashRemaining_ge parameter input remaining)
      | inr message =>
          apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache
            (runJointResolved_probeBound _ 0 (jointSourceSign_probeFree parameter root message cache) context fuel otsTable)
          · exact jointResolvedCoupledAt_sign parameter root table message state ftsFuel context fuel otsTable cache hclean hsynced
          · intro finalState entry hresult
            have hclean' := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState ftsFuel _ false _ hresult
            have hsynced' := revealedSynced_jointSourceSign parameter root table message state finalState ftsFuel
              context fuel otsTable cache entry hclean hsynced hresult
            exact ih entry.value.1 finalState ftsFuel entry.context entry.remaining entry.table entry.value.2
              (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1) hclean' hsynced'

theorem jointResolvedCoupledAt_computation_capped
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state q (jointSourceComputation parameter root (OtsProbeSimulation.capOuterHashQueries computation q))
      (simulateQ (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root
        (fun index tree leaf => table (index, tree, leaf))) (OtsProbeSimulation.capOuterHashQueries computation q)) context fuel otsTable cache :=
  jointResolvedCoupledAt_computation parameter root table _ state q context fuel otsTable cache
    (OtsProbeSimulation.capOuterHashQueries_hashBound computation q) hclean hsynced

end SphincsSecurity.Concrete.FtsProbeSimulation
