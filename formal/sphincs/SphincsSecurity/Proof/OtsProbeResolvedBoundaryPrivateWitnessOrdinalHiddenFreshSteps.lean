import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenRiskBound

/-!
# Local freshness steps

Canonicalization preserves candidate freshness, and a uniform outer query leaves the deferred
context unchanged. These discharge the uniform premise of the one-unit hidden ordinal theorem.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem CandidatePositionsFresh.canonicalize
    {context : DeferredContext} (hfresh : CandidatePositionsFresh context)
    (table : OtsSecretIndex → HashOutput) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table context) := by
  intro position parent hparent hhidden
  have horiginalHidden : Coordinate.position position ∉ context.state.revealed := by
    simpa [canonicalizeMaterializedValues_revealed] using hhidden
  have hpositionFresh := hfresh position parent hparent horiginalHidden
  constructor
  · unfold canonicalizeMaterializedValues publicMaterializedValues
    simp [horiginalHidden]
  · exact hpositionFresh.2

theorem candidatePositionsFresh_uniformStep
    (n : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Fin (n + 1) × SplitHashCache))
    (hfresh : CandidatePositionsFresh context)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((splitUniformImpl n).run cache))) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table result.context) := by
  unfold splitUniformImpl at hresult
  rw [StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, htail⟩ := hresult
  simp [runDirectResolvedWitnessFromTable] at htail
  subst result
  exact hfresh.canonicalize table

end SphincsSecurity.Concrete.OtsProbeSimulation
