import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationCommute

/-!
# Administrative preparation lift

The guarded finite preparation observer is insensitive to administrative changes of the ensured and published sets. These are the nonprobabilistic interpreter cases surrounding structural resolution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_ensure
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (coordinate : Coordinate) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.ensure coordinate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_ensure]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.ensure]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_publish
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (coordinate : Coordinate) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.publish coordinate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_publish]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.publish]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

theorem pendingCoveredBy_ensure
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    PendingCoveredBy candidates
        { context with state := context.state.ensure coordinate } ↔
      PendingCoveredBy candidates context := by
  rfl

theorem pendingCoveredBy_publish
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    PendingCoveredBy candidates
        { context with state := context.state.publish coordinate } ↔
      PendingCoveredBy candidates context := by
  rfl

theorem evalDist_guardedPreparationObserve_ensure
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    evalDist (guardedPreparationObserve candidates
      { context with state := context.state.ensure coordinate }) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  rw [pendingCoveredBy_ensure]
  by_cases hcovered : PendingCoveredBy candidates context
  · simp only [hcovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_ensure candidates.length candidates context
      coordinate
  · simp [hcovered]

theorem evalDist_guardedPreparationObserve_publish
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    evalDist (guardedPreparationObserve candidates
      { context with state := context.state.publish coordinate }) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  rw [pendingCoveredBy_publish]
  by_cases hcovered : PendingCoveredBy candidates context
  · simp only [hcovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_publish candidates.length candidates context
      coordinate
  · simp [hcovered]

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_addPending_chainStart
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (index : OtsSecretIndex) (digest : Digest) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.addPending index.coordinate digest }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_addPending_of_ne target context index.coordinate
                digest (by cases index; simp [OtsSecretIndex.coordinate])]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.addPending]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

theorem pendingCoveredBy_addPending_chainStart_iff
    (candidates : List Probe) (context : DeferredContext)
    (index : OtsSecretIndex) (digest : Digest) :
    PendingCoveredBy candidates
        { context with state := context.state.addPending index.coordinate digest } ↔
      PendingCoveredBy candidates context ∧
        ∃ candidate ∈ candidates,
          candidate.coordinate = index.coordinate ∧ candidate.candidate = digest := by
  constructor
  · intro hcovered
    constructor
    · intro entry hentry
      exact hcovered entry (by
        simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
        exact Or.inr hentry)
    · exact hcovered (index.coordinate, digest) (by
        simp [LazyRevealProbe.State.addPending])
  · rintro ⟨hcovered, candidate, hcandidate, hcoordinate, hdigest⟩
    intro entry hentry
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
    rcases hentry with rfl | hentry
    · exact ⟨candidate, hcandidate, hcoordinate, hdigest⟩
    · exact hcovered entry hentry

theorem evalDist_guardedPreparationObserve_addPending_chainStart_of_mem
    (candidates : List Probe) (context : DeferredContext)
    (index : OtsSecretIndex) (digest : Digest)
    (hmem : ∃ candidate ∈ candidates,
      candidate.coordinate = index.coordinate ∧ candidate.candidate = digest) :
    evalDist (guardedPreparationObserve candidates
      { context with state := context.state.addPending index.coordinate digest }) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  by_cases hcovered : PendingCoveredBy candidates context
  · have hnextCovered : PendingCoveredBy candidates
        { context with state := context.state.addPending index.coordinate digest } :=
      (pendingCoveredBy_addPending_chainStart_iff candidates context index digest).2
        ⟨hcovered, hmem⟩
    simp only [hcovered, hnextCovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_addPending_chainStart candidates.length candidates
      context index digest
  · have hnextNotCovered : ¬PendingCoveredBy candidates
        { context with state := context.state.addPending index.coordinate digest } := by
      intro hnext
      have hparts :=
        (pendingCoveredBy_addPending_chainStart_iff candidates context index digest).1 hnext
      exact hcovered hparts.1
    simp [hcovered, hnextNotCovered]

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_clearPending_chainStart
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (index : OtsSecretIndex) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.clearPending index.coordinate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_clearPending_of_ne target context index.coordinate
                (by cases index; simp [OtsSecretIndex.coordinate])]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.clearPending]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

theorem PendingCoveredBy.clearPending
    {candidates : List Probe} {context : DeferredContext} (coordinate : Coordinate)
    (hcovered : PendingCoveredBy candidates context) :
    PendingCoveredBy candidates
      { context with state := context.state.clearPending coordinate } := by
  apply hcovered.of_subset
  exact Finset.filter_subset _ _

theorem probEvent_guardedPreparationObserve_clearPending_chainStart_le
    (candidates : List Probe) (context : DeferredContext) (index : OtsSecretIndex) :
    Pr[= true | guardedPreparationObserve candidates
      { context with state := context.state.clearPending index.coordinate }] ≤
      Pr[= true | guardedPreparationObserve candidates context] := by
  by_cases hcovered : PendingCoveredBy candidates context
  · have hnextCovered := hcovered.clearPending index.coordinate
    apply le_of_eq
    apply OracleComp.probOutput_congr rfl
    unfold guardedPreparationObserve
    simp only [hcovered, hnextCovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_clearPending_chainStart candidates.length
      candidates context index
  · unfold guardedPreparationObserve
    simp only [hcovered, ↓reduceIte]
    by_cases hnextCovered : PendingCoveredBy candidates
        { context with state := context.state.clearPending index.coordinate }
    · simp only [hnextCovered, ↓reduceIte]
      convert (probOutput_le_one
        (mx := prepareCandidateListFails candidates
          { context with state := context.state.clearPending index.coordinate })
        (x := true)) using 1
      simp
    · simp [hnextCovered]

theorem clearPending_addPending_self
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (digest : Digest) :
    (state.addPending coordinate digest).clearPending coordinate =
      state.clearPending coordinate := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp only [LazyRevealProbe.State.addPending, LazyRevealProbe.State.clearPending,
    LazyRevealProbe.State.pendingAway]
  congr 1
  ext entry
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hentry, hne⟩
    rcases hentry with rfl | hentry
    · exact False.elim (hne rfl)
    · exact ⟨hentry, hne⟩
  · rintro ⟨hentry, hne⟩
    exact ⟨Or.inr hentry, hne⟩

theorem resolveDeferredPositionValue_addPending_self_of_resolved
    (position : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (digest : Digest)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue position context)) :
    resolveDeferredPositionValue position
        { resolved.toDeferredContext with
          state := resolved.state.addPending (.position position) digest } =
      if truncateHash resolved.output = digest then
        pure none
      else
        pure (some resolved) := by
  rw [resolveDeferredPositionValue_eq_bind_output]
  have hvalue := resolveDeferredPositionValue_resolves position context resolved hresolved
  have hpositionValue :
      ({ resolved.toDeferredContext with
        state := resolved.state.addPending (.position position) digest } :
          DeferredContext).positionValue position = some resolved.output := by
    simpa [DeferredContext.positionValue] using hvalue
  unfold deferredPositionOutput
  rw [hpositionValue]
  simp only [pure_bind]
  unfold resolvePrivatePositionWithOutput
  have holdClean : ¬resolved.state.hitAt (.position position) resolved.output := by
    rw [resolveDeferredPositionValue_state_eq_clearPending position context resolved hresolved]
    exact not_hitAt_clearPending_self context.state (.position position) resolved.output
  have hhitIff :
      (resolved.state.addPending (.position position) digest).hitAt
          (.position position) resolved.output ↔
        truncateHash resolved.output = digest := by
    rw [hitAt_addPending_self_iff]
    simp [holdClean]
  by_cases hhit : truncateHash resolved.output = digest
  · have hnewHit := hhitIff.mpr hhit
    simp [hnewHit, hhit]
  · have hnewMiss : ¬(resolved.state.addPending (.position position) digest).hitAt
        (.position position) resolved.output := fun hold => hhit (hhitIff.mp hold)
    simp only [hnewMiss, hhit, ↓reduceIte]
    congr 3
    calc
      completePrivatePosition position
          { state := resolved.state.addPending (.position position) digest
            values := resolved.values }
          resolved.output =
        completePrivatePosition position resolved.toDeferredContext resolved.output := by
          unfold completePrivatePosition
          congr 2
          rw [resolveDeferredPositionValue_state_eq_clearPending position context resolved
            hresolved]
          rw [clearPending_addPending_self, clearPending_idem]
      _ = resolved := completePrivatePosition_resolved_eq position context resolved hresolved

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_addPending_position_of_mem
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (added : Probe) (position : Position)
    (hcoordinate : added.coordinate = .position position)
    (hmem : added ∈ candidates) (hlength : candidates.length ≤ fuel) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with
        state := context.state.addPending added.coordinate added.candidate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero =>
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst candidates
      simp at hmem
  | succ fuel ih =>
      cases candidates with
      | nil => simp at hmem
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              have htailMem : added ∈ remaining := by
                simp only [List.mem_cons] at hmem
                rcases hmem with hhead | htail
                · subst added
                  simp [hcandidate] at hcoordinate
                · exact htail
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context htailMem (by simpa using hlength)
          | position target =>
              by_cases heq : position = target
              · subst position
                have haddedCoordinate : added.coordinate = .position target := hcoordinate
                let continuation : Option DeferredResolution → ProbComp Bool
                  | none => pure true
                  | some resolved =>
                      if candidateListHits target (candidate :: remaining) resolved.output then
                        pure true
                      else
                        prepareCandidateGroupsFails fuel
                          (removeTargetCandidates target (candidate :: remaining))
                          resolved.toDeferredContext
                have hresolver := resolveDeferredPositionValue_then_addPending_self_resolve
                  target context added.candidate
                calc
                  _ = evalDist (resolveDeferredPositionValue target
                        { context with
                          state := context.state.addPending (.position target)
                            added.candidate } >>= continuation) := by
                    unfold prepareCandidateGroupsFails
                    rw [resolvedCandidateGroupsFire, hcandidate, haddedCoordinate]
                    rfl
                  _ = evalDist ((do
                        let first ← resolveDeferredPositionValue target context
                        match first with
                        | none => (pure none : ProbComp (Option DeferredResolution))
                        | some first =>
                            resolveDeferredPositionValue target
                              { first.toDeferredContext with
                                state := first.state.addPending (.position target)
                                  added.candidate }) >>= continuation) :=
                    congrArg evalDist
                      (congrArg (fun resolver => resolver >>= continuation) hresolver.symm)
                  _ = evalDist (resolveDeferredPositionValue target context >>= fun first =>
                        match first with
                        | none => pure true
                        | some first =>
                            if candidateListHits target (candidate :: remaining) first.output then
                              pure true
                            else
                              prepareCandidateGroupsFails fuel
                                (removeTargetCandidates target (candidate :: remaining))
                                first.toDeferredContext) := by
                    simp only [bind_assoc]
                    apply evalDist_bind_congr
                    intro first hfirst
                    cases first with
                    | none => rfl
                    | some first =>
                        simp only
                        rw [resolveDeferredPositionValue_addPending_self_of_resolved target
                          context first added.candidate hfirst]
                        by_cases haddedHit : truncateHash first.output = added.candidate
                        · have hlistHit : candidateListHits target (candidate :: remaining)
                              first.output :=
                            candidateListHits_of_mem target first.output added
                              (candidate :: remaining) hmem haddedCoordinate haddedHit.symm
                          simp [continuation, haddedHit, hlistHit]
                        · simp [continuation, haddedHit]
                  _ = _ := by
                    unfold prepareCandidateGroupsFails
                    rw [resolvedCandidateGroupsFire, hcandidate]
                    simp only
                    rfl
              · have hcoordinateNe : Coordinate.position position ≠ .position target := by
                  intro hold
                  exact heq (Coordinate.position.inj hold)
                have htailMem : added ∈ removeTargetCandidates target
                    (candidate :: remaining) := by
                  unfold removeTargetCandidates
                  apply List.mem_filter.mpr
                  refine ⟨hmem, ?_⟩
                  simp [candidateTargets, hcoordinate, heq]
                simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
                rw [hcoordinate,
                  resolveDeferredPositionValue_addPending_of_ne target context
                    (.position position) added.candidate hcoordinateNe]
                simp only [map_eq_bind_pure_comp, bind_assoc]
                apply evalDist_bind_congr
                intro resolved _hresolved
                cases resolved with
                | none => rfl
                | some resolved =>
                    simp only [Function.comp_apply, pure_bind, Option.map_some,
                      DeferredResolution.addPending]
                    by_cases hhit : candidateListHits target (candidate :: remaining)
                        resolved.output
                    · simp [hhit]
                    · simp only [hhit, ↓reduceIte]
                      have hrestLength :
                          (removeTargetCandidates target
                            (candidate :: remaining)).length ≤ fuel := by
                        have hheadTarget : candidateTargets target candidate = true := by
                          simp [candidateTargets, hcandidate]
                        have hcountPositive : 1 ≤ candidateTargetCount target
                            (candidate :: remaining) := by
                          simp [candidateTargetCount, hheadTarget]
                        have hpartition :=
                          candidateTargetCount_add_removeTargetCandidates_length target
                            (candidate :: remaining)
                        omega
                      have hih := ih
                        (removeTargetCandidates target (candidate :: remaining))
                        resolved.toDeferredContext htailMem hrestLength
                      rw [hcoordinate] at hih
                      exact hih

theorem evalDist_prepareCandidateListFails_addPending_position_of_mem
    (candidates : List Probe) (context : DeferredContext)
    (added : Probe) (position : Position)
    (hcoordinate : added.coordinate = .position position)
    (hmem : added ∈ candidates) :
    evalDist (prepareCandidateListFails candidates
      { context with
        state := context.state.addPending added.coordinate added.candidate }) =
      evalDist (prepareCandidateListFails candidates context) :=
  evalDist_prepareCandidateGroupsFails_addPending_position_of_mem candidates.length candidates
    context added position hcoordinate hmem le_rfl

theorem PendingCoveredBy.addPending_of_mem
    {candidates : List Probe} {context : DeferredContext} (added : Probe)
    (hcovered : PendingCoveredBy candidates context) (hmem : added ∈ candidates) :
    PendingCoveredBy candidates
      { context with
        state := context.state.addPending added.coordinate added.candidate } := by
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with rfl | hentry
  · exact ⟨added, hmem, rfl, rfl⟩
  · exact hcovered entry hentry

theorem evalDist_guardedPreparationObserve_addPending_of_mem
    (candidates : List Probe) (context : DeferredContext) (added : Probe)
    (hmem : added ∈ candidates) :
    evalDist (guardedPreparationObserve candidates
      { context with
        state := context.state.addPending added.coordinate added.candidate }) =
      evalDist (guardedPreparationObserve candidates context) := by
  by_cases hcovered : PendingCoveredBy candidates context
  · have hnextCovered := hcovered.addPending_of_mem added hmem
    unfold guardedPreparationObserve
    simp only [hcovered, hnextCovered, ↓reduceIte]
    cases hcoordinate : added.coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
        have hindex : index.coordinate = added.coordinate := by
          simp [index, OtsSecretIndex.coordinate, hcoordinate]
        rw [← hcoordinate, ← hindex]
        exact evalDist_prepareCandidateGroupsFails_addPending_chainStart candidates.length
          candidates context index added.candidate
    | position position =>
        rw [← hcoordinate]
        exact evalDist_prepareCandidateListFails_addPending_position_of_mem candidates context
          added position hcoordinate hmem
  · have hnextNotCovered : ¬PendingCoveredBy candidates
        { context with
          state := context.state.addPending added.coordinate added.candidate } := by
      intro hnext
      apply hcovered
      intro entry hentry
      exact hnext entry (by
        simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
        exact Or.inr hentry)
    simp [guardedPreparationObserve, hcovered, hnextNotCovered]

theorem evalDist_guardedPreparationObserve_probe_of_mem
    (candidates : List Probe) (context : DeferredContext) (candidate : Probe)
    (hmem : candidate ∈ candidates) :
    evalDist (guardedPreparationObserve candidates
      (if candidate.coordinate ∈ context.state.revealed then
        context
      else
        { context with
          state := context.state.addPending candidate.coordinate candidate.candidate })) =
      evalDist (guardedPreparationObserve candidates context) := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · simp [hrevealed]
  · simp only [hrevealed, ↓reduceIte]
    exact evalDist_guardedPreparationObserve_addPending_of_mem candidates context candidate hmem

theorem probEvent_resolveDeferredChainStart_then_guardedPreparationObserve_le
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (candidates : List Probe) (context : DeferredContext) :
    Pr[= true |
      match resolveDeferredChainStart table index context with
      | none => pure false
      | some resolved => guardedPreparationObserve candidates resolved.toDeferredContext] ≤
      Pr[= true | guardedPreparationObserve candidates context] := by
  cases hresolved : resolveDeferredChainStart table index context with
  | none => simp
  | some resolved =>
      have hstate := resolveDeferredChainStart_state_eq_clearPending table index context
        resolved hresolved
      have hvalues := resolveDeferredChainStart_deferred_values_eq table index context
        resolved hresolved
      have hcontext : resolved.toDeferredContext =
          { context with state := context.state.clearPending index.coordinate } := by
        cases context with
        | mk state values =>
            cases resolved with
            | mk resolvedContext output =>
                cases resolvedContext with
                | mk resolvedState resolvedValues =>
                    simp only at hstate hvalues ⊢
                    subst resolvedState
                    subst resolvedValues
                    rfl
      simp only
      rw [hcontext]
      exact probEvent_guardedPreparationObserve_clearPending_chainStart_le candidates context
        index

end SphincsSecurity.Concrete.OtsProbeSimulation
