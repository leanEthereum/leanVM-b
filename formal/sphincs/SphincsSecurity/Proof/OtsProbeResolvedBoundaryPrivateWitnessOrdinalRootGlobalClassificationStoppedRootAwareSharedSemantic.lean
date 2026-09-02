import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSharedExperiment

/-!
# Successful shared-prefix semantics

The lemmas in this module eliminate the conservative failure arm of the root-aware outcome under
the successful first-root gate carried by the observed marginal.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

theorem finished_probe_matches_of_successful_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {result : ObservedCleanRunResult α} {candidate : Probe}
    {selected : Fin result.observations.length}
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result))
    (hselected : selected.val = ordinal)
    (hcandidate : candidate = (result.observations.get selected).toProbe)
    (hstored : StoredLayerRoot result.state target leftRoot)
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state) :
    (MaterializedSelectionOutcome.finished (some candidate)).Matches target leftRoot := by
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
      goodSelected, hgoodSelected, hfirst, _hroot⟩,
    hposition⟩, _hcomparison⟩ := hgood
  obtain ⟨hitSelected, hhitSelected, hhit, _hnoEarlier⟩ := hfirst
  have hselectedEq : selected = goodSelected :=
    Fin.ext (hselected.trans hgoodSelected.symm)
  have hhitSelectedEq : hitSelected = goodSelected :=
    Fin.ext (hhitSelected.trans hgoodSelected.symm)
  subst selected
  subst hitSelected
  have hlt : ordinal < result.observations.length := by
    rw [← hgoodSelected]
    exact goodSelected.isLt
  have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = goodSelected :=
    Fin.ext hgoodSelected.symm
  have htargetData :
      (result.observations.get goodSelected).coordinate = .position target ∧
        IsLayerRoot target := by
    simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte] at hposition
    rw [candidateLayerRootPosition?_eq_some_iff, hindex] at hposition
    exact hposition
  obtain ⟨_hhidden, output, hvalueAtProbe, hdigest⟩ := hhit
  have htrackedObservation := htracked
    (result.observations.get goodSelected) (List.get_mem _ _)
  have hfinalValue := htrackedObservation.1 output hvalueAtProbe
  obtain ⟨stored, hstoredValue, hstoredDigest⟩ := hstored
  rw [htargetData.1] at hfinalValue
  have houtput : output = stored := Option.some.inj (hfinalValue.symm.trans hstoredValue)
  subst stored
  change candidate = ⟨.position target, leftRoot⟩
  rw [hcandidate]
  unfold CleanProbeObservation.toProbe
  rw [htargetData.1, ← hdigest, hstoredDigest]

end SphincsSecurity.Concrete.OtsProbeSimulation
