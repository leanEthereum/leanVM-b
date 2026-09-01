import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSampleBase

/-!
# Materialized comparison observation tracking

Successful observed executions preserve the tracking invariant through the retained runner and its
guarded clean finalizer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem cleanProbeObservationsTrackedBy_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    CleanProbeObservationsTrackedBy result.observations result.state := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact htracked
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind] at hresult
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2
                    (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                      ((splitUniformImpl n).run cache) observations state fuel table htracked step
                      hstep)
                    (by simpa only [observedMaterializedBoundary] using hrest)
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2
                    (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache) observations state fuel table htracked step hstep)
                    (by simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              exact ih step.value.1 step.observations step.state step.remaining table step.value.2
                (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table htracked step hstep)
                (by simpa only [observedMaterializedBoundary] using hrest)

def ObservedMaterializedOutputTracked :
    Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => True
  | some result =>
      CleanProbeObservationsTrackedBy result.observations result.state

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem observedMaterializedOutputTracked_of_mem_retainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (output : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (houtput : output ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    ObservedMaterializedOutputTracked output := by
  unfold observedMaterializedRetainedRunFromTable at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨rootResult?, hroot, hrest⟩ := houtput
  cases rootResult? with
  | none =>
      simp at hrest
      subst output
      trivial
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none =>
          simp at hreturn
          subst output
          trivial
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          subst output
          have hrootTracked :
              CleanProbeObservationsTrackedBy rootResult.observations rootResult.state :=
            cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
              (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty
              fuel table (by intro observation hobservation; simp at hobservation) rootResult hroot
          exact cleanProbeObservationsTrackedBy_of_mem_observedMaterializedBoundary parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            hrootTracked restResult hrestResult

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_and_observedMaterializedOutputTracked
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (source : ProbComp α)
    (relation : α → Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop)
    (hrelation : RelTriple source
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)
      relation) :
    RelTriple source
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)
      (fun left right => relation left right ∧ ObservedMaterializedOutputTracked right) := by
  have hright :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hrelation
  apply relTriple_post_mono hright
  intro left right hfacts
  exact ⟨hfacts.1,
    observedMaterializedOutputTracked_of_mem_retainedRunFromTable
      (adversary := adversary) (parameter := parameter) (ftsSecret := ftsSecret)
      (fuel := fuel) (table := table) (output := right) hfacts.2⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
