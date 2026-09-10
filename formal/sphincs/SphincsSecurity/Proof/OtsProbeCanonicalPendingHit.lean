import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinary
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

def PendingResolvedHit (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : Prop :=
  ∃ coordinate output, resolvedCompletionValue table context coordinate = some output ∧
    context.state.hitAt coordinate output

theorem DeferredCompletable.not_pendingResolvedHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) : ¬PendingResolvedHit table context := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  rintro ⟨coordinate, output, hvalue, hhit⟩
  have heq := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hpending : (coordinate, truncateHash output) ∈ context.state.pending := by
    rwa [← LazyRevealProbe.State.mem_pendingAt_iff]
  exact hcompletion.2.2.1 coordinate (truncateHash output) hpending (by rw [heq])

theorem deferredCompletable_iff_no_pendingResolvedHit
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    DeferredCompletable table context ↔ ¬PendingResolvedHit table context := by
  constructor
  · exact DeferredCompletable.not_pendingResolvedHit
  · intro hclean
    have hvalid : context.Valid := by
      refine ⟨hconsistent, ?_⟩
      intro coordinate output hvalue hhit
      apply hclean
      refine ⟨coordinate, output, ?_, hhit⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
          simp [resolvedCompletionValue, heq]
      | position position => simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
    apply deferredCompletable_of_valid_of_no_boundary_hit table context hvalid hstarts
      (hcard := hcard)
    · rintro ⟨position, output, hhidden, hvalue, hhit⟩
      exact hclean ⟨.position position, output,
        by simp [resolvedCompletionValue, DeferredContext.positionValue, hhidden, hvalue], hhit⟩
    · rintro ⟨index, _hhidden, hhit⟩
      exact hclean ⟨index.coordinate, table index, rfl, hhit⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
