import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Adaptive delayed-signer bridge

The delayed signer is erased under an arbitrary terminal observer that treats doomed contexts as
failure, respects synchronized finalization views, and is neutral to an ensured private position.
The resulting clean interpreter canonicalizes materialized values only at outer-query boundaries.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

theorem valid_of_resolvedCore_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hcompletable : DeferredCompletable table context) : context.Valid := by
  refine ⟨hconsistent, ?_⟩
  intro coordinate output hvalue hhit
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hresolved : resolvedCompletionValue table context coordinate = some output := by
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        simpa [resolvedCompletionValue] using
          (hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue).symm
    | position position =>
        simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
  have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hresolved
  unfold LazyRevealProbe.State.hitAt at hhit
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
  exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])

end SphincsSecurity.Concrete.OtsProbeSimulation
