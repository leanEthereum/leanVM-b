import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def replaceNativePosition (target : Position) (output : HashOutput)
    (context : DeferredContext) : DeferredContext :=
  { state := { context.state with
      values := Function.update context.state.values (.position target)
        ((context.state.values (.position target)).map fun _ => output) }
    values := context.values.install target output }

def replaceNativeResolution (target : Position) (output : HashOutput) (position : Option Position)
    (result : DeferredResolution) : DeferredResolution :=
  ⟨replaceNativePosition target output result.toDeferredContext,
    if position = some target then output else result.output⟩

structure NativePositionReplaceable (target : Position) (before after : HashOutput)
    (context : DeferredContext) : Prop where
  known : context.positionValue target = some before
  consistent : context.ValuesConsistent
  beforeMiss : ¬context.state.hitAt (.position target) before
  afterMiss : ¬context.state.hitAt (.position target) after

theorem NativePositionReplaceable.auxiliary
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) :
    context.values target = some before := by
  cases hstate : context.state.values (.position target) with
  | none => simpa [DeferredContext.positionValue, hstate] using h.known
  | some output =>
      have heq : output = before := by simpa [DeferredContext.positionValue, hstate] using h.known
      subst output
      exact h.consistent target before hstate

theorem NativePositionReplaceable.state_value
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) :
    context.state.values (.position target) = none ∨
      context.state.values (.position target) = some before := by
  cases hstate : context.state.values (.position target) with
  | none => exact Or.inl rfl
  | some output =>
      right
      have heq : output = before := by simpa [DeferredContext.positionValue, hstate] using h.known
      exact congrArg some heq

theorem NativePositionReplaceable.of_transition
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativePositionReplaceable target before after left)
    (hknown : right.positionValue target = left.positionValue target)
    (hpending : right.state.pending ⊆ left.state.pending)
    (hconsistent : right.ValuesConsistent) :
    NativePositionReplaceable target before after right := by
  refine ⟨hknown.trans h.known, hconsistent, ?_, ?_⟩
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    have hmem := hpending hhit
    first
    | apply h.beforeMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hmem
    | apply h.afterMiss
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hmem

theorem replaceNativePosition_of_private
    (target : Position) (output : HashOutput) (context : DeferredContext)
    (hstate : context.state.values (.position target) = none) :
    replaceNativePosition target output context = replacePrivatePosition target output context := by
  simp only [replaceNativePosition, replacePrivatePosition, hstate, Option.map_none]
  rw [← hstate, Function.update_eq_self]

theorem replaceNativePosition_positionValue
    (target : Position) (output : HashOutput) (context : DeferredContext) :
    (replaceNativePosition target output context).positionValue target = some output := by
  cases hstate : context.state.values (.position target) <;>
    simp [replaceNativePosition, DeferredContext.positionValue, DeferredStructuralValues.install, hstate]

theorem replaceNativePosition_inverse
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) :
    replaceNativePosition target before (replaceNativePosition target after context) = context := by
  have haux : context.values.install target before = context.values := by
    unfold DeferredStructuralValues.install
    rw [← h.auxiliary, Function.update_eq_self]
  have hstate : Function.update context.state.values (.position target)
      ((context.state.values (.position target)).map fun _ => before) = context.state.values := by
    rcases h.state_value with hnone | hsome
    · rw [hnone, Option.map_none, ← hnone, Function.update_eq_self]
    · rw [hsome, Option.map_some, ← hsome, Function.update_eq_self]
  simp only [replaceNativePosition, Function.update_self, Option.map_map,
    Function.comp_def, Function.update_idem, DeferredStructuralValues.install]
  rw [hstate, ← DeferredStructuralValues.install, haux]

theorem DeferredContext.ValuesConsistent.of_replaceNativePosition
    {context : DeferredContext} (h : context.ValuesConsistent)
    (target : Position) (output : HashOutput) :
    (replaceNativePosition target output context).ValuesConsistent := by
  intro position value hvalue
  by_cases heq : position = target
  · subst position
    simp only [replaceNativePosition, Function.update_self] at hvalue
    have heq : output = value := by
      cases hstate : context.state.values (.position target) <;> simp_all
    simp [replaceNativePosition, DeferredStructuralValues.install, heq]
  · have hcoordinate : Coordinate.position position ≠ .position target := by simpa using heq
    change Function.update context.state.values (.position target)
      ((context.state.values (.position target)).map fun _ => output) (.position position) = some value at hvalue
    rw [Function.update_of_ne hcoordinate] at hvalue
    simpa [replaceNativePosition, DeferredStructuralValues.install, heq] using h position value hvalue

theorem nativeValueUpdate_hitAt (state : LazyRevealProbe.State Coordinate)
    (values : Coordinate → Option HashOutput) (coordinate : Coordinate) (output : HashOutput) :
    ({ state with values := values } : LazyRevealProbe.State Coordinate).hitAt coordinate output ↔
      state.hitAt coordinate output := Iff.rfl

theorem nativeValueUpdate_clearPending (state : LazyRevealProbe.State Coordinate)
    (values : Coordinate → Option HashOutput) (coordinate : Coordinate) :
    ({ state with values := values } : LazyRevealProbe.State Coordinate).clearPending coordinate =
      { state.clearPending coordinate with values := values } := rfl

attribute [local simp] nativeValueUpdate_hitAt nativeValueUpdate_clearPending

theorem resolveDeferredPositionValue_replaceNativePosition
    (target position : Position) (before after : HashOutput) (context : DeferredContext)
    (h : NativePositionReplaceable target before after context) :
    resolveDeferredPositionValue position (replaceNativePosition target after context) =
      Option.map (replaceNativeResolution target after (some position)) <$>
        resolveDeferredPositionValue position context := by
  by_cases heq : position = target
  · subst position
    rcases h.state_value with hstate | hstate <;>
      simp [resolveDeferredPositionValue, replaceNativePosition, replaceNativeResolution,
        DeferredStructuralValues.install, hstate, h.auxiliary, h.beforeMiss, h.afterMiss,
        LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]
  · have hcoordinate : Coordinate.position position ≠ .position target := by simpa using heq
    have hcomm (output : HashOutput) :
        (context.values.install target after).install position output =
          (context.values.install position output).install target after := by
      exact Function.update_comm (Ne.symm heq) (some after) (some output) context.values
    cases hstate : context.state.values (.position position) with
    | some output =>
        by_cases hhit : context.state.hitAt (.position position) output <;>
          simp [resolveDeferredPositionValue, replaceNativePosition, replaceNativeResolution,
            hstate, hhit, heq, hcoordinate, hcomm, LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]
    | none =>
        cases hvalue : context.values position with
        | some output =>
            by_cases hhit : context.state.hitAt (.position position) output <;>
              simp [resolveDeferredPositionValue, replaceNativePosition, replaceNativeResolution,
                DeferredStructuralValues.install, hstate, hvalue, hhit, heq, hcoordinate,
                LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]
        | none =>
            simp only [resolveDeferredPositionValue, replaceNativePosition, DeferredStructuralValues.install,
              Function.update_of_ne hcoordinate, hstate, Function.update_of_ne heq, hvalue, map_bind]
            apply bind_congr
            intro output
            by_cases hhit : context.state.hitAt (.position position) output
            · simp [hhit]
            · simpa [hhit, replaceNativeResolution, replaceNativePosition, heq,
                DeferredStructuralValues.install, LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway] using hcomm output

end SphincsSecurity.Concrete.OtsProbeSimulation
