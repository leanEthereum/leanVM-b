import SphincsSecurity.Proof.FtsProbeJointContinuation
import SphincsSecurity.Proof.OuterHashQueryCap

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointOuterQuery (parameter : PublicParameter) (root : Digest) :
    (input : (OracleWorld + SigningSpec).Domain) → NativeFtsStep ((OracleWorld + SigningSpec).Range input)
  | .inl (.inl n) => liftNativeBlock (OtsProbeSimulation.splitUniformImpl n)
  | .inl (.inr input) => maskedJointHashQuery parameter input
  | .inr message => maskedJointSign parameter root message

noncomputable def maskedJointComputation (parameter : PublicParameter) (root : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : NativeFtsStep α :=
  OracleComp.construct (fun value => liftNativeBlock (pure value))
    (fun input _ next => bindNativeSteps (jointOuterQuery parameter root input) next) computation

theorem maskedJointComputation_query_bind
    (parameter : PublicParameter) (root : Digest) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    maskedJointComputation parameter root (OracleSpec.query input >>= next) =
      bindNativeSteps (jointOuterQuery parameter root input) (fun output => maskedJointComputation parameter root (next output)) := by
  rw [maskedJointComputation, construct_query_bind]
  rfl

theorem jointHashRemaining_ge (parameter : PublicParameter) (input : HashInput) (remaining : Nat) :
    remaining ≤ jointHashRemaining parameter input remaining := by
  unfold jointHashRemaining
  cases decodeProbe? parameter input <;> simp only <;> omega

attribute [local irreducible] maskedJointSign OtsProbeSimulation.maskedPublishedChronologicalSign

theorem nativeStepRelAt_maskedJointComputation
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepRelAt parameter table state ftsFuel (maskedJointComputation parameter root computation)
      (simulateQ (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root
        (fun index tree leaf => table (index, tree, leaf))) computation) context fuel history cache ftsCache := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel history cache ftsCache with
  | pure value =>
      exact NativeStepCoupledAt.relTriple (projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache (pure value)
        (OtsProbeSimulation.CacheMapCommutes.pure _ value) context fuel history cache hclean)
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [maskedJointComputation_query_bind, simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl world =>
          cases world with
          | inl n =>
              apply nativeStepRelAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache
                (liftNativeBlock_probeFree _ context fuel history cache)
              · exact NativeStepCoupledAt.relTriple (projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache
                  (OtsProbeSimulation.splitUniformImpl n)
                  (OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
                  context fuel history cache hclean)
              · intro finalState entry finalCache hresult
                obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state finalState ftsFuel
                  (OtsProbeSimulation.splitUniformImpl n)
                  (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))
                  context fuel history cache ftsCache finalCache (some entry) hsynced hresult
                exact ih entry.value.1 finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 finalCache
                  (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1)
                  (by simpa [hstate] using hclean) hsynced'
          | inr input =>
              have hpositive : 0 < ftsFuel := by simpa [OtsProbeSimulation.IsOuterHash] using hbound.1
              cases ftsFuel with
              | zero => omega
              | succ remaining =>
                  apply nativeStepRelAt_hashQuery_bind parameter table input state remaining _ _ context fuel history cache ftsCache hclean hsynced
                  intro finalState entry finalCache hresult
                  obtain ⟨hclean', hsynced', _⟩ := invariants_maskedJointHashQuery parameter table input state finalState
                    (remaining + 1) context fuel history cache ftsCache finalCache (some entry) hclean hsynced hresult
                  apply ih entry.value.1 finalState (jointHashRemaining parameter input remaining)
                    entry.context entry.remaining entry.history entry.value.2 finalCache _ hclean' hsynced'
                  have htail : (next entry.value.1).IsQueryBoundP OtsProbeSimulation.IsOuterHash remaining := by
                    simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1
                  exact htail.mono (jointHashRemaining_ge parameter input remaining)
      | inr message =>
          apply nativeStepRelAt_sign_bind parameter root table message state ftsFuel _ _ context fuel history cache ftsCache hclean hsynced
          intro finalState entry finalCache hresult
          have hclean' := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState ftsFuel _ false _ hresult
          have hsynced' := revealedSynced_maskedJointSign parameter root table message state finalState ftsFuel
            context fuel history cache ftsCache finalCache (some entry) hclean hsynced hresult
          exact ih entry.value.1 finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 finalCache
            (by simpa [OtsProbeSimulation.IsOuterHash] using hbound.2 entry.value.1) hclean' hsynced'

theorem nativeStepRelAt_maskedJointComputation_capped
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepRelAt parameter table state q
      (maskedJointComputation parameter root (OtsProbeSimulation.capOuterHashQueries computation q))
      (simulateQ (OtsProbeSimulation.maskedChronologicalExpandedAdversaryImpl parameter root
        (fun index tree leaf => table (index, tree, leaf))) (OtsProbeSimulation.capOuterHashQueries computation q))
      context fuel history cache ftsCache :=
  nativeStepRelAt_maskedJointComputation parameter root table _ state q context fuel history cache ftsCache
    (OtsProbeSimulation.capOuterHashQueries_hashBound computation q) hclean hsynced

end SphincsSecurity.Concrete.FtsProbeSimulation
