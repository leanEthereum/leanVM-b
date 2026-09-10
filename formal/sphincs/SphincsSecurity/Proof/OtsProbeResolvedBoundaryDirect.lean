import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

theorem valid_completable_canonicalizeMaterializedValues
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    (canonicalizeMaterializedValues table context).Valid ∧
      DeferredCompletable table (canonicalizeMaterializedValues table context) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output := by
    intro coordinate output hvalue hhit
    have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])
  exact ⟨canonicalizeMaterializedValues_valid table context hvalid hclean,
    ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
