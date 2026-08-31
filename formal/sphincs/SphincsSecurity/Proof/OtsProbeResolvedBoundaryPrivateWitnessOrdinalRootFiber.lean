import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootAdaptive

/-!
# Layer-root ordinal fibers

The root selected by one chronological candidate ordinal is dynamic. This module classifies a
retained witness by that root position so a weighted fiber argument can fix the target without
paying for every possible structural position.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def candidateLayerRootPosition? (candidate : Probe) : Option Position :=
  match candidate.coordinate with
  | .position position => if IsLayerRoot position then some position else none
  | .chainStart _ _ _ _ => none

theorem candidateLayerRootPosition?_eq_some_iff
    (candidate : Probe) (target : Position) :
    candidateLayerRootPosition? candidate = some target ↔
      candidate.coordinate = .position target ∧ IsLayerRoot target := by
  cases candidate with
  | mk coordinate digest =>
      cases coordinate with
      | chainStart => simp [candidateLayerRootPosition?]
      | position position =>
          simp only [candidateLayerRootPosition?]
          by_cases hroot : IsLayerRoot position
          · rw [if_pos hroot]
            simp only [Option.some.injEq, Coordinate.position.injEq]
            constructor
            · intro heq
              subst target
              exact ⟨rfl, hroot⟩
            · rintro ⟨heq, _htarget⟩
              exact heq
          · rw [if_neg hroot]
            constructor
            · simp
            · rintro ⟨heq, htarget⟩
              have hposition : position = target := Coordinate.position.inj heq
              subst target
              exact False.elim (hroot htarget)

noncomputable def selectedLayerRootPosition?
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Option Position :=
  if hselected : ordinal < output.2.length then
    candidateLayerRootPosition? (output.2.get ⟨ordinal, hselected⟩)
  else none

def selectedPrivateWitnessDigest (output : PrivateWitnessPlanOutput) : Digest :=
  match output.1 with
  | none => 0
  | some witness => truncateHash witness.output

theorem selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output) :
    ∃ target, selectedLayerRootPosition? ordinal output = some target := by
  obtain ⟨witness, sourceOrdinal, _hwitness, hordinal, _hfirst, hroot⟩ := hfirst
  obtain ⟨target, hcoordinate, htarget⟩ := hroot
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  refine ⟨target, ?_⟩
  unfold selectedLayerRootPosition?
  rw [dif_pos hselected, candidateLayerRootPosition?_eq_some_iff]
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  rw [hindex]
  exact ⟨hcoordinate, htarget⟩

theorem not_witnessFirstUsesLayerRootOrdinal_of_selectedLayerRootPosition?_eq_none
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hposition : selectedLayerRootPosition? ordinal output = none) :
    ¬WitnessFirstUsesLayerRootOrdinal ordinal output := by
  intro hfirst
  obtain ⟨target, htarget⟩ :=
    selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal hfirst
  rw [hposition] at htarget
  simp at htarget

theorem witnessFirstUsesLayerRootOrdinal_fiber_data
    {ordinal : Nat} {output : PrivateWitnessPlanOutput} {target : Position}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output)
    (hfiber : selectedLayerRootPosition? ordinal output = some target) :
    ∃ witness sourceOrdinal,
      output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
        firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal ∧
        witness.position = target ∧
        truncateHash witness.output = (output.2.get sourceOrdinal).candidate ∧
        IsLayerRoot target := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, _hroot⟩ := hfirst
  have hmatch :=
    privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hsourceFirst
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  have hfiber' := hfiber
  unfold selectedLayerRootPosition? at hfiber'
  rw [dif_pos hselected, candidateLayerRootPosition?_eq_some_iff, hindex] at hfiber'
  unfold PrivateWitnessAtOrdinal at hmatch
  have hposition : witness.position = target := by
    exact Coordinate.position.inj (hmatch.1.symm.trans hfiber'.1)
  exact ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, hposition,
    hmatch.2, hfiber'.2⟩

theorem selectedPrivateWitnessDigest_eq_candidate_of_witnessFirstUsesLayerRootOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output) :
    ∃ hselected : ordinal < output.2.length,
      selectedPrivateWitnessDigest output =
        (output.2.get ⟨ordinal, hselected⟩).candidate := by
  obtain ⟨target, htarget⟩ :=
    selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal hfirst
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, _hposition,
    hroot, _htarget⟩ := witnessFirstUsesLayerRootOrdinal_fiber_data hfirst htarget
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  refine ⟨hselected, ?_⟩
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  rw [hindex, selectedPrivateWitnessDigest, hwitness]
  exact hroot

theorem earlier_fiber_candidate_ne_actual_root
    {ordinal : Nat} {output : PrivateWitnessPlanOutput} {target : Position}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output)
    (hfiber : selectedLayerRootPosition? ordinal output = some target)
    (earlier : Fin output.2.length) (hlt : earlier.val < ordinal)
    (hcoordinate : (output.2.get earlier).coordinate = .position target) :
    (output.2.get earlier).candidate ≠
      truncateHash (Option.get output.1 (by
        obtain ⟨witness, _sourceOrdinal, hwitness, _⟩ :=
          witnessFirstUsesLayerRootOrdinal_fiber_data hfirst hfiber
        rw [hwitness]
        simp)).output := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, hposition,
    _hroot, _htarget⟩ := witnessFirstUsesLayerRootOrdinal_fiber_data hfirst hfiber
  have hwitnessGet : Option.get output.1 (by rw [hwitness]; simp) = witness := by
    simp [hwitness]
  rw [hwitnessGet]
  have huses : WitnessFirstUsesOrdinal ordinal output :=
    ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst⟩
  apply earlier_candidate_ne_of_witnessFirstUsesOrdinal
    huses witness hwitness earlier hlt target hcoordinate hposition

theorem probEvent_witnessFirstUsesLayerRootOrdinal_le_of_position_fibers
    (run : ProbComp PrivateWitnessPlanOutput) (ordinal : Nat)
    (hfiber : ∀ target,
      Pr[fun output => WitnessFirstUsesLayerRootOrdinal ordinal output ∧
          selectedLayerRootPosition? ordinal output = some target | run] ≤
        Pr[fun output => selectedLayerRootPosition? ordinal output = some target | run] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesLayerRootOrdinal ordinal | run] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_uniform_weighted_fibers run
    (WitnessFirstUsesLayerRootOrdinal ordinal)
    (selectedLayerRootPosition? ordinal)
    (((2 ^ digestBits : Nat) : ENNReal)⁻¹)
  intro position?
  cases position? with
  | none =>
      have hzero : Pr[fun output => WitnessFirstUsesLayerRootOrdinal ordinal output ∧
          selectedLayerRootPosition? ordinal output = none | run] = 0 := by
        apply probEvent_eq_zero
        intro output _houtput hevent
        exact not_witnessFirstUsesLayerRootOrdinal_of_selectedLayerRootPosition?_eq_none
          hevent.2 hevent.1
      rw [hzero]
      exact zero_le
  | some target => exact hfiber target

end SphincsSecurity.Concrete.OtsProbeSimulation
