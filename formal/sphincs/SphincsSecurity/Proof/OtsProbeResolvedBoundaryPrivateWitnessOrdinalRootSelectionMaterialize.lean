import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Materialized shadow of a deferred boundary

Only structural outputs already present in `DeferredContext.values` are copied into the shadow
state. No missing output is sampled. The shadow therefore gives the existing directional signer
coupling a fully materialized right context while preserving the completed value at every
coordinate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def materializedDeferredState (context : DeferredContext) :
    LazyRevealProbe.State Coordinate :=
  { context.state with
    values := fun coordinate =>
      match coordinate with
      | .chainStart lay tree leafIdx chainIdx =>
          context.state.values (.chainStart lay tree leafIdx chainIdx)
      | .position position => context.positionValue position }

@[simp] theorem materializedDeferredState_pending (context : DeferredContext) :
    (materializedDeferredState context).pending = context.state.pending := rfl

@[simp] theorem materializedDeferredState_revealed (context : DeferredContext) :
    (materializedDeferredState context).revealed = context.state.revealed := rfl

@[simp] theorem materializedDeferredState_ensured (context : DeferredContext) :
    (materializedDeferredState context).ensured = context.state.ensured := rfl

@[simp] theorem materializedDeferredState_chainStart
    (context : DeferredContext) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    (materializedDeferredState context).values
        (.chainStart lay tree leafIdx chainIdx) =
      context.state.values (.chainStart lay tree leafIdx chainIdx) := rfl

@[simp] theorem materializedDeferredState_position
    (context : DeferredContext) (position : Position) :
    (materializedDeferredState context).values (.position position) =
      context.positionValue position := rfl

theorem clean_of_deferredCompletion
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
      ¬context.state.hitAt coordinate output := by
  intro coordinate output hvalue hhit
  have hcompletionValue := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  unfold LazyRevealProbe.State.hitAt at hhit
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
  exact hcompletion.2.2.1 coordinate (truncateHash output) hhit
    (by rw [hcompletionValue])

end SphincsSecurity.Concrete.OtsProbeSimulation
