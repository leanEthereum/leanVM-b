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

set_option maxRecDepth 100000 in
theorem cleanProbeObservationsCoverPending_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    CleanProbeObservationsCoverPending result.observations result.state := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact hcovered
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
                    (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                      ((splitUniformImpl n).run cache) observations state fuel table hcovered step
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
                    (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache) observations state fuel table hcovered step hstep)
                    (by simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              exact ih step.value.1 step.observations step.state step.remaining table step.value.2
                (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table hcovered step hstep)
                (by simpa only [observedMaterializedBoundary] using hrest)

set_option maxRecDepth 100000 in
theorem remaining_add_pending_card_le_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.remaining + result.state.pending.card ≤ fuel + state.pending.card := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      simp
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
                  have hfirst := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hstep
                  have htail := ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
                  omega
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hfirst := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hstep
                  have htail := ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
                  omega
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hfirst := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                table step hstep
              have htail := ih step.value.1 step.observations step.state step.remaining table
                step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
              omega

set_option maxRecDepth 100000 in
theorem observations_length_add_remaining_eq_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.observations.length + result.remaining = observations.length + fuel := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      rfl
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
                  have hfirst :=
                    observations_length_add_remaining_eq_of_mem_runObservedCleanFromTable
                      ((splitUniformImpl n).run cache) observations state fuel table step hstep
                  have htail := ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
                  omega
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hfirst :=
                    observations_length_add_remaining_eq_of_mem_runObservedCleanFromTable
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache) observations state fuel table step hstep
                  have htail := ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
                  omega
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hfirst :=
                observations_length_add_remaining_eq_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hstep
              have htail := ih step.value.1 step.observations step.state step.remaining table
                step.value.2 (by simpa only [observedMaterializedBoundary] using hrest)
              omega

set_option maxRecDepth 100000 in
theorem startTableAgrees_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hagrees : StartTableAgrees state table)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.table = table ∧ StartTableAgrees result.state table := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact ⟨rfl, hagrees⟩
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
                  have hfirst := startTableAgrees_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table hagrees step
                    hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hfirst.2
                    (by simpa only [observedMaterializedBoundary] using hrest)
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hfirst := startTableAgrees_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table hagrees step hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hfirst.2
                    (by simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hfirst := startTableAgrees_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                table hagrees step hstep
              exact ih step.value.1 step.observations step.state step.remaining table step.value.2
                hfirst.2 (by simpa only [observedMaterializedBoundary] using hrest)

def ObservedMaterializedOutputTracked :
    Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => True
  | some result =>
      CleanProbeObservationsTrackedBy result.observations result.state

def ObservedMaterializedOutputCovered :
    Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => True
  | some result =>
      CleanProbeObservationsCoverPending result.observations result.state

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

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem observedMaterializedOutputCovered_of_mem_retainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (output : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (houtput : output ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    ObservedMaterializedOutputCovered output := by
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
          have hrootCovered :
              CleanProbeObservationsCoverPending rootResult.observations rootResult.state :=
            cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
              (maskedPublishedTreeRoot.run emptySplitHashCache) []
              LazyRevealProbe.State.empty fuel table (by
                intro entry hentry
                have : False := by
                  simpa [directDeferredContext, LazyRevealProbe.State.empty] using hentry
                contradiction) rootResult hroot
          exact cleanProbeObservationsCoverPending_of_mem_observedMaterializedBoundary parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            hrootCovered restResult hrestResult

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem pending_card_le_fuel_of_mem_observedMaterializedRetainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    result.state.pending.card ≤ fuel := by
  unfold observedMaterializedRetainedRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨rootResult?, hroot, hrest⟩ := hresult
  cases rootResult? with
  | none => simp at hrest
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none => simp at hreturn
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          obtain rfl := Option.some.inj hreturn
          have hrootBudget := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
            table rootResult hroot
          have hrootBudget' :
              rootResult.remaining + rootResult.state.pending.card ≤ fuel := by
            simpa [LazyRevealProbe.State.empty] using hrootBudget
          have hrestBudget :=
            remaining_add_pending_card_le_of_mem_observedMaterializedBoundary parameter
              rootResult.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
              rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
              restResult hrestResult
          change restResult.state.pending.card ≤ fuel
          omega

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem observations_length_le_fuel_of_mem_observedMaterializedRetainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    result.observations.length ≤ fuel := by
  unfold observedMaterializedRetainedRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨rootResult?, hroot, hrest⟩ := hresult
  cases rootResult? with
  | none => simp at hrest
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none => simp at hreturn
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          obtain rfl := Option.some.inj hreturn
          have hrootLength :=
            observations_length_add_remaining_eq_of_mem_runObservedCleanFromTable
              (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
              table rootResult hroot
          have hrestLength :=
            observations_length_add_remaining_eq_of_mem_observedMaterializedBoundary parameter
              rootResult.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
              rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
              restResult hrestResult
          simp only [List.length_nil, Nat.zero_add] at hrootLength
          change restResult.observations.length ≤ fuel
          omega

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem table_eq_and_startTableAgrees_of_mem_observedMaterializedRetainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    result.table = table ∧ StartTableAgrees result.state table := by
  unfold observedMaterializedRetainedRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨rootResult?, hroot, hrest⟩ := hresult
  cases rootResult? with
  | none => simp at hrest
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none => simp at hreturn
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          obtain rfl := Option.some.inj hreturn
          have hrootAgrees := startTableAgrees_of_mem_runObservedCleanFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
            table (startTableAgrees_empty table) rootResult hroot
          exact startTableAgrees_of_mem_observedMaterializedBoundary parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            hrootAgrees.2 restResult hrestResult

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
