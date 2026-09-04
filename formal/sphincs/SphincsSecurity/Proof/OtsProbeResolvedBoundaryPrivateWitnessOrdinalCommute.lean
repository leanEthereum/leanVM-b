import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalProbability

/-!
# One-ordinal resolution commutation

Resolving an arbitrary structural position before testing one selected candidate cannot increase
the selected fire probability. A resolution at the selected position may stop on an older pending
hit. A different resolution is commuted past the selected deferred draw.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def resolveThenPrivateCandidateFire
    (position : Position) (candidate : Probe) (context : DeferredContext) : ProbComp Bool := do
  let resolved ← resolveDeferredPositionValue position context
  match resolved with
  | none => pure false
  | some resolved => privateCandidateFire candidate resolved.toDeferredContext

theorem deferredPositionOutput_completePrivatePosition_self
    (position : Position) (context : DeferredContext) (output : HashOutput)
    (houtput : output ∈ support (deferredPositionOutput position context)) :
    deferredPositionOutput position
        (completePrivatePosition position context output).toDeferredContext =
      pure output := by
  unfold deferredPositionOutput DeferredContext.positionValue at houtput ⊢
  unfold completePrivatePosition
  cases hstate : context.state.values (.position position) with
  | some value =>
      simp [hstate] at houtput
      subst output
      simp [hstate]
  | none =>
      cases hprivate : context.values position with
      | some value =>
          simp [hstate, hprivate] at houtput
          subst output
          simp [hstate, DeferredStructuralValues.install]
      | none =>
          simp [hstate, DeferredStructuralValues.install]

theorem evalDist_resolveThenPrivateCandidateFire_same
    (target : Position) (candidate : Probe) (context : DeferredContext)
    (hcoordinate : candidate.coordinate = .position target) :
    evalDist (resolveThenPrivateCandidateFire target candidate context) = evalDist (do
      let output ← deferredPositionOutput target context
      if context.state.hitAt (.position target) output then
        pure false
      else
        pure (truncateHash output = candidate.candidate)) := by
  unfold resolveThenPrivateCandidateFire
  rw [resolveDeferredPositionValue_eq_bind_output]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro output _houtput
  unfold resolvePrivatePositionWithOutput
  by_cases hhit : context.state.hitAt (.position target) output
  · simp [hhit]
  · simp only [hhit, ↓reduceIte, pure_bind]
    unfold privateCandidateFire
    simp only [hcoordinate]
    rw [deferredPositionOutput_completePrivatePosition_self target context output _houtput]
    simp

theorem probEvent_resolveThenPrivateCandidateFire_same_le
    (target : Position) (candidate : Probe) (context : DeferredContext)
    (hcoordinate : candidate.coordinate = .position target) :
    Pr[= true | resolveThenPrivateCandidateFire target candidate context] ≤
      Pr[= true | privateCandidateFire candidate context] := by
  have hdist := evalDist_resolveThenPrivateCandidateFire_same target candidate context hcoordinate
  calc
    _ = Pr[= true | do
        let output ← deferredPositionOutput target context
        if context.state.hitAt (.position target) output then
          pure false
        else
          pure (truncateHash output = candidate.candidate)] :=
      OracleComp.probOutput_congr rfl hdist
    _ ≤ Pr[fun output => truncateHash output = candidate.candidate |
        deferredPositionOutput target context] := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_probEvent
      intro output _houtput hmiss
      by_cases hhit : context.state.hitAt (.position target) output
      · simp [hhit]
      · simp [hhit, hmiss]
    _ = Pr[= true | privateCandidateFire candidate context] := by
      unfold privateCandidateFire
      rw [hcoordinate]
      change Pr[fun output => truncateHash output = candidate.candidate |
          deferredPositionOutput target context] =
        Pr[= true | (fun output : HashOutput =>
          decide (truncateHash output = candidate.candidate)) <$>
            deferredPositionOutput target context]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      exact OracleComp.probEvent_congr' (fun _ _ => by simp) rfl

theorem evalDist_resolveThenPrivateCandidateFire_ne
    (position target : Position) (candidate : Probe) (context : DeferredContext)
    (hcoordinate : candidate.coordinate = .position target) (hne : position ≠ target) :
    evalDist (resolveThenPrivateCandidateFire position candidate context) = evalDist (do
      let targetOutput ← deferredPositionOutput target context
      let positionOutput ← deferredPositionOutput position context
      if context.state.hitAt (.position position) positionOutput then
        pure false
      else
        pure (truncateHash targetOutput = candidate.candidate)) := by
  let continuation : HashOutput → HashOutput → ProbComp Bool :=
      fun positionOutput targetOutput =>
    if context.state.hitAt (.position position) positionOutput then
      pure false
    else
      pure (truncateHash targetOutput = candidate.candidate)
  calc
    _ = evalDist (do
        let positionOutput ← deferredPositionOutput position context
        let targetOutput ← deferredPositionOutput target context
        continuation positionOutput targetOutput) := by
      unfold resolveThenPrivateCandidateFire
      rw [resolveDeferredPositionValue_eq_bind_output]
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro positionOutput _hpositionOutput
      unfold resolvePrivatePositionWithOutput
      by_cases hhit : context.state.hitAt (.position position) positionOutput
      · simp only [hhit, ↓reduceIte, pure_bind, continuation]
        exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          (deferredPositionOutput target context)
          (by simp [deferredPositionOutput, LazyRevealProbe.sampleHashOutput])
          (pure false)).symm
      · simp only [hhit, ↓reduceIte, pure_bind, continuation]
        unfold privateCandidateFire
        simp only [hcoordinate]
        rw [deferredPositionOutput_completePrivatePosition_of_ne position target context
          positionOutput hne]
    _ = evalDist (do
        let targetOutput ← deferredPositionOutput target context
        let positionOutput ← deferredPositionOutput position context
        continuation positionOutput targetOutput) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        (deferredPositionOutput position context) (deferredPositionOutput target context)
        continuation
    _ = _ := by rfl

theorem probEvent_resolveThenPrivateCandidateFire_ne_le
    (position target : Position) (candidate : Probe) (context : DeferredContext)
    (hcoordinate : candidate.coordinate = .position target) (hne : position ≠ target) :
    Pr[= true | resolveThenPrivateCandidateFire position candidate context] ≤
      Pr[= true | privateCandidateFire candidate context] := by
  have hdist := evalDist_resolveThenPrivateCandidateFire_ne position target candidate context
    hcoordinate hne
  calc
    _ = Pr[= true | do
        let targetOutput ← deferredPositionOutput target context
        let positionOutput ← deferredPositionOutput position context
        if context.state.hitAt (.position position) positionOutput then
          pure false
        else
          pure (truncateHash targetOutput = candidate.candidate)] :=
      OracleComp.probOutput_congr rfl hdist
    _ ≤ Pr[fun output => truncateHash output = candidate.candidate |
        deferredPositionOutput target context] := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_probEvent
      intro targetOutput _htargetOutput hmiss
      simp [hmiss]
    _ = Pr[= true | privateCandidateFire candidate context] := by
      unfold privateCandidateFire
      rw [hcoordinate]
      change Pr[fun output => truncateHash output = candidate.candidate |
          deferredPositionOutput target context] =
        Pr[= true | (fun output : HashOutput =>
          decide (truncateHash output = candidate.candidate)) <$>
            deferredPositionOutput target context]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      exact OracleComp.probEvent_congr' (fun _ _ => by simp) rfl

theorem probEvent_resolveThenPrivateCandidateFire_le
    (position : Position) (candidate : Probe) (context : DeferredContext) :
    Pr[= true | resolveThenPrivateCandidateFire position candidate context] ≤
      Pr[= true | privateCandidateFire candidate context] := by
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold resolveThenPrivateCandidateFire privateCandidateFire
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro resolved _hresolved
      cases resolved <;> simp [hcoordinate]
  | position target =>
      by_cases heq : position = target
      · subst position
        exact probEvent_resolveThenPrivateCandidateFire_same_le target candidate context hcoordinate
      · exact probEvent_resolveThenPrivateCandidateFire_ne_le position target candidate context
          hcoordinate heq

theorem privateCandidateFire_materialize_chainStart
    (candidate : Probe) (context : DeferredContext)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (output : HashOutput) :
    privateCandidateFire candidate
        { state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output
          values := context.values } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart otherLay otherTree otherLeaf otherChain =>
      simp [privateCandidateFire, hcandidate]
  | position position =>
      rfl

theorem privateCandidateFire_materialize_position_of_positionValue
    (candidate : Probe) (context : DeferredContext)
    (position : Position) (output : HashOutput)
    (hvalue : context.positionValue position = some output) :
    privateCandidateFire candidate
        { state := context.state.materialize (.position position) output
          values := context.values } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position target =>
      by_cases heq : target = position
      · subst target
        unfold privateCandidateFire
        simp only [hcandidate]
        unfold deferredPositionOutput
        have hpost :
            ({ state := context.state.materialize (.position position) output
               values := context.values } : DeferredContext).positionValue position =
              some output := by
          simp [DeferredContext.positionValue, LazyRevealProbe.State.materialize]
        rw [hpost, hvalue]
      · unfold privateCandidateFire
        simp only [hcandidate]
        unfold deferredPositionOutput
        have hcoordinateNe : Coordinate.position target ≠ .position position := by
          intro hcoordinate
          exact heq (Coordinate.position.inj hcoordinate)
        have hpost :
            ({ state := context.state.materialize (.position position) output
               values := context.values } : DeferredContext).positionValue target =
              context.positionValue target := by
          unfold DeferredContext.positionValue
          simp [LazyRevealProbe.State.materialize, Function.update_of_ne hcoordinateNe]
        rw [hpost]

theorem privateCandidateFire_materialize_install_position_of_positionValue
    (candidate : Probe) (context : DeferredContext)
    (position : Position) (output : HashOutput)
    (hvalue : context.positionValue position = some output) :
    privateCandidateFire candidate
        { state := context.state.materialize (.position position) output
          values := context.values.install position output } =
      privateCandidateFire candidate context := by
  have hmaterialized := privateCandidateFire_materialize_position_of_positionValue candidate
    context position output hvalue
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position target =>
      have hpost :
          ({ state := context.state.materialize (.position position) output
             values := context.values.install position output } : DeferredContext).positionValue
                target =
            ({ state := context.state.materialize (.position position) output
               values := context.values } : DeferredContext).positionValue target := by
        unfold DeferredContext.positionValue
        by_cases heq : target = position
        · subst target
          simp [LazyRevealProbe.State.materialize]
        · have hcoordinateNe : Coordinate.position target ≠ .position position := by
            intro hcoordinate
            exact heq (Coordinate.position.inj hcoordinate)
          simp [LazyRevealProbe.State.materialize, Function.update_of_ne hcoordinateNe,
            DeferredStructuralValues.install, Function.update_of_ne heq]
      calc
        _ = privateCandidateFire candidate
            { state := context.state.materialize (.position position) output
              values := context.values } := by
          unfold privateCandidateFire
          simp only [hcandidate]
          unfold deferredPositionOutput
          rw [hpost]
        _ = _ := hmaterialized

theorem privateCandidateFire_materialize_install_eq_complete
    (candidate : Probe) (context : DeferredContext)
    (position : Position) (output : HashOutput)
    (hstate : context.state.values (.position position) = none) :
    privateCandidateFire candidate
        { state := context.state.materialize (.position position) output
          values := context.values.install position output } =
      privateCandidateFire candidate
        (completePrivatePosition position context output).toDeferredContext := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position target =>
      have hpositionValue :
          ({ state := context.state.materialize (.position position) output
             values := context.values.install position output } : DeferredContext).positionValue
                target =
            (completePrivatePosition position context output).toDeferredContext.positionValue
              target := by
        unfold DeferredContext.positionValue completePrivatePosition
        by_cases heq : target = position
        · subst target
          simp [LazyRevealProbe.State.materialize, hstate,
            DeferredStructuralValues.install]
        · have hcoordinateNe : Coordinate.position target ≠ .position position := by
            intro hcoordinate
            exact heq (Coordinate.position.inj hcoordinate)
          simp [LazyRevealProbe.State.materialize, LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway, Function.update_of_ne hcoordinateNe,
            DeferredStructuralValues.install, Function.update_of_ne heq]
      unfold privateCandidateFire
      simp only [hcandidate]
      unfold deferredPositionOutput
      rw [hpositionValue]

end SphincsSecurity.Concrete.OtsProbeSimulation
