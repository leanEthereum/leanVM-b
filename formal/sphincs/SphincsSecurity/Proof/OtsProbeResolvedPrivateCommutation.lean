import SphincsSecurity.Proof.OtsProbeResolvedPrivateSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure RevealedResolution where
  context : DeferredContext
  output : HashOutput

noncomputable def resolvePositionValuesInOrder
    (first second : Position) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let firstResolved ← resolveDeferredPositionValue first context
  match firstResolved with
  | none => pure none
  | some firstResolved => do
      let secondResolved ←
        resolveDeferredPositionValue second firstResolved.toDeferredContext
      match secondResolved with
      | none => pure none
      | some secondResolved =>
          pure (some ⟨secondResolved.toDeferredContext, secondResolved.output⟩)

noncomputable def resolvePositionValuesSwapped
    (first second : Position) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let secondResolved ← resolveDeferredPositionValue second context
  match secondResolved with
  | none => pure none
  | some secondResolved => do
      let firstResolved ←
        resolveDeferredPositionValue first secondResolved.toDeferredContext
      match firstResolved with
      | none => pure none
      | some firstResolved =>
          pure (some ⟨firstResolved.toDeferredContext, secondResolved.output⟩)

theorem clearPending_comm_position
    (state : LazyRevealProbe.State Coordinate) (first second : Position) :
    (state.clearPending (.position first)).clearPending (.position second) =
      (state.clearPending (.position second)).clearPending (.position first) := by
  exact clearPending_comm state (.position first) (.position second)

noncomputable def deferredPositionOutput (position : Position)
    (context : DeferredContext) : ProbComp HashOutput :=
  match context.positionValue position with
  | some output => pure output
  | none => LazyRevealProbe.sampleHashOutput

def completePrivatePosition (position : Position) (context : DeferredContext)
    (output : HashOutput) : DeferredResolution :=
  ⟨{ state := context.state.clearPending (.position position)
     values := context.values.install position output }, output⟩

noncomputable def resolvePrivatePositionWithOutput (position : Position)
    (context : DeferredContext) (output : HashOutput) :
    ProbComp (Option DeferredResolution) :=
  if context.state.hitAt (.position position) output then
    pure none
  else
    pure (some (completePrivatePosition position context output))

theorem resolveDeferredPositionValue_eq_bind_output
    (position : Position) (context : DeferredContext) :
    resolveDeferredPositionValue position context = (do
      let output ← deferredPositionOutput position context
      resolvePrivatePositionWithOutput position context output) := by
  unfold resolveDeferredPositionValue deferredPositionOutput
    resolvePrivatePositionWithOutput completePrivatePosition
  cases hstate : context.state.values (.position position) with
  | some output =>
      simp [DeferredContext.positionValue, hstate]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          have hupdate : context.values.install position output = context.values := by
            unfold DeferredStructuralValues.install
            conv_lhs => rw [← hvalue]
            exact Function.update_eq_self _ _
          simp [DeferredContext.positionValue, hstate, hvalue, hupdate]
      | none =>
          simp [DeferredContext.positionValue, hstate, hvalue]

theorem deferredPositionOutput_completePrivatePosition_of_ne
    (first second : Position) (context : DeferredContext) (output : HashOutput)
    (hne : first ≠ second) :
    deferredPositionOutput second
        (completePrivatePosition first context output).toDeferredContext =
      deferredPositionOutput second context := by
  unfold deferredPositionOutput DeferredContext.positionValue completePrivatePosition
  have hposition : second ≠ first := Ne.symm hne
  simp [LazyRevealProbe.State.clearPending, DeferredStructuralValues.install,
    Function.update_of_ne hposition]

theorem hitAt_completePrivatePosition_of_ne
    (first second : Position) (context : DeferredContext) (firstOutput secondOutput : HashOutput)
    (hne : first ≠ second) :
    (completePrivatePosition first context firstOutput).state.hitAt
        (.position second) secondOutput =
      context.state.hitAt (.position second) secondOutput := by
  unfold completePrivatePosition
  exact propext (hitAt_clearPending_of_ne context.state (.position first) (.position second)
    secondOutput (by
      intro heq
      exact hne (Coordinate.position.inj heq).symm))

theorem completePrivatePosition_comm
    (first second : Position) (context : DeferredContext)
    (firstOutput secondOutput : HashOutput) (hne : first ≠ second) :
    (completePrivatePosition second
        (completePrivatePosition first context firstOutput).toDeferredContext
          secondOutput).toDeferredContext =
      (completePrivatePosition first
        (completePrivatePosition second context secondOutput).toDeferredContext
          firstOutput).toDeferredContext := by
  unfold completePrivatePosition
  change
    ({ state := (context.state.clearPending (.position first)).clearPending (.position second)
       values := (context.values.install first firstOutput).install second secondOutput } :
      DeferredContext) =
    ({ state := (context.state.clearPending (.position second)).clearPending (.position first)
       values := (context.values.install second secondOutput).install first firstOutput } :
      DeferredContext)
  rw [clearPending_comm_position]
  unfold DeferredStructuralValues.install
  rw [Function.update_comm hne]

theorem completePrivatePosition_resolved_eq
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    completePrivatePosition position result.toDeferredContext result.output = result := by
  have hstate := resolveDeferredPositionValue_state_eq_clearPending position context result
    hresult
  have hvalue := resolveDeferredPositionValue_installs position context result hresult
  rcases result with ⟨⟨state, values⟩, output⟩
  simp only at hstate hvalue ⊢
  subst state
  have hupdate : values.install position output = values := by
    unfold DeferredStructuralValues.install
    conv_lhs => rw [← hvalue]
    exact Function.update_eq_self _ _
  unfold completePrivatePosition
  rw [clearPending_idem, hupdate]

theorem resolveDeferredPositionValue_of_resolved
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    resolveDeferredPositionValue position result.toDeferredContext = pure (some result) := by
  rw [resolveDeferredPositionValue_eq_bind_output]
  have hknown := resolveDeferredPositionValue_resolves position context result hresult
  have hclean : ¬result.state.hitAt (.position position) result.output := by
    have hstate := resolveDeferredPositionValue_state_eq_clearPending position context result
      hresult
    rw [hstate]
    exact not_hitAt_clearPending_self context.state (.position position) result.output
  simp [deferredPositionOutput, hknown, resolvePrivatePositionWithOutput, hclean,
    completePrivatePosition_resolved_eq position context result hresult]

theorem evalDist_resolvePositionValues_comm_self
    (position : Position) (context : DeferredContext) :
    evalDist (resolvePositionValuesInOrder position position context) =
      evalDist (resolvePositionValuesSwapped position position context) := by
  unfold resolvePositionValuesInOrder resolvePositionValuesSwapped
  apply evalDist_bind_congr
  intro resolved hresolved
  cases resolved with
  | none => rfl
  | some resolved =>
      simp only
      rw [resolveDeferredPositionValue_of_resolved position context resolved hresolved]
      rfl

def DeferredResolution.clearPending (result : DeferredResolution) (coordinate : Coordinate) :
    DeferredResolution :=
  ⟨{ result.toDeferredContext with state := result.state.clearPending coordinate },
    result.output⟩

theorem deferredPositionOutput_clearPending
    (position : Position) (context : DeferredContext) (coordinate : Coordinate) :
    deferredPositionOutput position
        { context with state := context.state.clearPending coordinate } =
      deferredPositionOutput position context := by
  rfl

theorem hitAt_clearPending_other_position
    (position : Position) (context : DeferredContext) (coordinate : Coordinate)
    (output : HashOutput) (hne : coordinate ≠ .position position) :
    (context.state.clearPending coordinate).hitAt (.position position) output =
      context.state.hitAt (.position position) output := by
  exact propext (hitAt_clearPending_of_ne context.state coordinate (.position position)
    output hne.symm)

theorem completePrivatePosition_clearPending_comm
    (position : Position) (context : DeferredContext) (coordinate : Coordinate)
    (output : HashOutput) :
    completePrivatePosition position
        { context with state := context.state.clearPending coordinate } output =
      (completePrivatePosition position context output).clearPending coordinate := by
  unfold completePrivatePosition DeferredResolution.clearPending
  rw [clearPending_comm]

theorem resolveDeferredPositionValue_clearPending_of_ne
    (position : Position) (context : DeferredContext) (coordinate : Coordinate)
    (hne : coordinate ≠ .position position) :
    resolveDeferredPositionValue position
        { context with state := context.state.clearPending coordinate } =
      (fun result => result.map fun resolved => resolved.clearPending coordinate) <$>
        resolveDeferredPositionValue position context := by
  rw [resolveDeferredPositionValue_eq_bind_output,
    resolveDeferredPositionValue_eq_bind_output, deferredPositionOutput_clearPending]
  rw [map_bind]
  apply bind_congr
  intro output
  unfold resolvePrivatePositionWithOutput
  have hhitEq := hitAt_clearPending_other_position position context coordinate output hne
  by_cases hhit : context.state.hitAt (.position position) output
  · simp [hhitEq, hhit]
  · simp [hhitEq, hhit, completePrivatePosition_clearPending_comm]

noncomputable def resolvePositionThenChainStart
    (position : Position) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let positionResolved ← resolveDeferredPositionValue position context
  match positionResolved with
  | none => pure none
  | some positionResolved =>
      match resolveDeferredChainStart table index positionResolved.toDeferredContext with
      | none => pure none
      | some chainResolved =>
          pure (some ⟨chainResolved.toDeferredContext, chainResolved.output⟩)

noncomputable def resolveChainStartThenPosition
    (position : Position) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) :=
  match resolveDeferredChainStart table index context with
  | none => pure none
  | some chainResolved => do
      let positionResolved ←
        resolveDeferredPositionValue position chainResolved.toDeferredContext
      match positionResolved with
      | none => pure none
      | some positionResolved =>
          pure (some ⟨positionResolved.toDeferredContext, chainResolved.output⟩)

def clearResolutionForChainStart (index : OtsSecretIndex) (table : OtsSecretIndex → HashOutput) :
    Option DeferredResolution → Option RevealedResolution
  | none => none
  | some resolved =>
      some ⟨(resolved.clearPending index.coordinate).toDeferredContext, table index⟩

def resolutionWithChainStartOutput (index : OtsSecretIndex)
    (table : OtsSecretIndex → HashOutput) :
    Option DeferredResolution → Option RevealedResolution
  | none => none
  | some resolved => some ⟨resolved.toDeferredContext, table index⟩

theorem evalDist_resolvePosition_chainStart_comm
    (position : Position) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext)
    (hcompletable : DeferredCompletable table context) :
    evalDist (resolvePositionThenChainStart position table index context) =
      evalDist (resolveChainStartThenPosition position table index context) := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hclean := hcompletable.not_hitAt_chainStart index
  have hcoordinate : index.coordinate ≠ .position position := by
    cases index
    simp [OtsSecretIndex.coordinate]
  have hchain := resolveDeferredChainStart_of_agrees table index context hstarts hclean
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
          pure (clearResolutionForChainStart index table resolved)) := by
      unfold resolvePositionThenChainStart
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hstate := resolveDeferredPositionValue_state_eq_clearPending position context
            resolved hresolved
          have hresolvedStarts : StartTableAgrees resolved.state table :=
            hstarts.of_state_values_eq
              (resolveDeferredPositionValue_preserves_state_values position context resolved
                hresolved)
          have hresolvedClean :
              ¬resolved.state.hitAt index.coordinate (table index) := by
            rw [hstate]
            exact (hitAt_clearPending_of_ne context.state (.position position)
              index.coordinate (table index) hcoordinate).not.mpr hclean
          simp only
          rw [resolveDeferredChainStart_of_agrees table index resolved.toDeferredContext
            hresolvedStarts hresolvedClean]
          rfl
    _ = evalDist (resolveDeferredPositionValue position
          { context with state := context.state.clearPending index.coordinate } >>=
            fun resolved => pure (resolutionWithChainStartOutput index table resolved)) := by
      rw [resolveDeferredPositionValue_clearPending_of_ne position context index.coordinate
        hcoordinate]
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply congrArg evalDist
      apply bind_congr
      intro resolved
      cases resolved <;> rfl
    _ = _ := by
      unfold resolveChainStartThenPosition
      rw [hchain]
      simp only
      apply congrArg evalDist
      apply bind_congr
      intro resolved
      cases resolved <;> rfl

noncomputable def orderedPositionResolutionOutcome
    (first second : Position) (context : DeferredContext)
    (firstOutput secondOutput : HashOutput) : Option RevealedResolution :=
  if context.state.hitAt (.position first) firstOutput then
    none
  else if context.state.hitAt (.position second) secondOutput then
    none
  else
    some ⟨(completePrivatePosition second
      (completePrivatePosition first context firstOutput).toDeferredContext
        secondOutput).toDeferredContext, secondOutput⟩

theorem resolvePositionValuesInOrder_eq_outputs
    (first second : Position) (context : DeferredContext) (hne : first ≠ second) :
    evalDist (resolvePositionValuesInOrder first second context) = evalDist (do
      let firstOutput ← deferredPositionOutput first context
      let secondOutput ← deferredPositionOutput second context
      pure (orderedPositionResolutionOutcome first second context firstOutput secondOutput)) := by
  unfold resolvePositionValuesInOrder
  simp_rw [resolveDeferredPositionValue_eq_bind_output]
  simp only [bind_assoc]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro firstOutput
  unfold resolvePrivatePositionWithOutput
  by_cases hfirstHit : context.state.hitAt (.position first) firstOutput
  · simp only [hfirstHit, ↓reduceIte, pure_bind, orderedPositionResolutionOutcome]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (deferredPositionOutput second context) (by
        simp [deferredPositionOutput, LazyRevealProbe.sampleHashOutput]) (pure none)).symm
  · simp only [hfirstHit, ↓reduceIte, pure_bind]
    rw [deferredPositionOutput_completePrivatePosition_of_ne first second context firstOutput hne]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro secondOutput
    have hsecondHitEq := hitAt_completePrivatePosition_of_ne first second context
      firstOutput secondOutput hne
    by_cases hsecondHit : context.state.hitAt (.position second) secondOutput
    · simp [hsecondHitEq, hsecondHit, orderedPositionResolutionOutcome, hfirstHit]
    · simp [hsecondHitEq, hsecondHit, orderedPositionResolutionOutcome, hfirstHit]
      rfl

theorem resolvePositionValuesSwapped_eq_outputs
    (first second : Position) (context : DeferredContext) (hne : first ≠ second) :
    evalDist (resolvePositionValuesSwapped first second context) = evalDist (do
      let secondOutput ← deferredPositionOutput second context
      let firstOutput ← deferredPositionOutput first context
      pure (orderedPositionResolutionOutcome first second context firstOutput secondOutput)) := by
  unfold resolvePositionValuesSwapped
  simp_rw [resolveDeferredPositionValue_eq_bind_output]
  simp only [bind_assoc]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secondOutput
  unfold resolvePrivatePositionWithOutput
  by_cases hsecondHit : context.state.hitAt (.position second) secondOutput
  · simp only [hsecondHit, ↓reduceIte, pure_bind, orderedPositionResolutionOutcome,
      ite_self]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (deferredPositionOutput first context) (by
        simp [deferredPositionOutput, LazyRevealProbe.sampleHashOutput]) (pure none)).symm
  · simp only [hsecondHit, ↓reduceIte, pure_bind]
    rw [deferredPositionOutput_completePrivatePosition_of_ne second first context secondOutput
      hne.symm]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro firstOutput
    have hfirstHitEq := hitAt_completePrivatePosition_of_ne second first context
      secondOutput firstOutput hne.symm
    by_cases hfirstHit : context.state.hitAt (.position first) firstOutput
    · simp [hfirstHitEq, hfirstHit, orderedPositionResolutionOutcome]
    · have hfirstHitCompleted :
          ¬(completePrivatePosition second context secondOutput).state.hitAt
            (.position first) firstOutput := by
        rw [hfirstHitEq]
        exact hfirstHit
      simp only [hfirstHitCompleted, ↓reduceIte, pure_bind]
      unfold orderedPositionResolutionOutcome
      rw [if_neg hfirstHit, if_neg hsecondHit]
      simp only [completePrivatePosition_comm first second context firstOutput secondOutput hne]
      rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolvePositionValues_comm_of_ne
    (first second : Position) (context : DeferredContext) (hne : first ≠ second) :
    evalDist (resolvePositionValuesInOrder first second context) =
      evalDist (resolvePositionValuesSwapped first second context) := by
  calc
    _ = evalDist (do
          let firstOutput ← deferredPositionOutput first context
          let secondOutput ← deferredPositionOutput second context
          pure (orderedPositionResolutionOutcome first second context firstOutput secondOutput)) :=
      resolvePositionValuesInOrder_eq_outputs first second context hne
    _ = evalDist (do
          let secondOutput ← deferredPositionOutput second context
          let firstOutput ← deferredPositionOutput first context
          pure (orderedPositionResolutionOutcome first second context firstOutput secondOutput)) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        (deferredPositionOutput first context) (deferredPositionOutput second context)
        (fun firstOutput secondOutput =>
          pure (orderedPositionResolutionOutcome first second context firstOutput secondOutput))
    _ = _ := (resolvePositionValuesSwapped_eq_outputs first second context hne).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
