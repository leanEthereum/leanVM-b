import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootJoint

/-!
# Observation transport across an installed root

Installing one hidden structural value early changes only the stored value recorded by probes at
that position. Probe identity and publication status stay unchanged. The comparison-root avoidance
condition therefore preserves the clean strict prefix, while the selected matching probe remains a
hidden hit.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

def installPositionValueAtProbe
    (target : Position) (output : HashOutput)
    (observation : CleanProbeObservation) : CleanProbeObservation :=
  if observation.coordinate = .position target then
    { observation with valueAtProbe := some output }
  else observation

@[simp] theorem installPositionValueAtProbe_coordinate
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation) :
    (installPositionValueAtProbe target output observation).coordinate = observation.coordinate := by
  unfold installPositionValueAtProbe
  split <;> rfl

@[simp] theorem installPositionValueAtProbe_candidate
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation) :
    (installPositionValueAtProbe target output observation).candidate = observation.candidate := by
  unfold installPositionValueAtProbe
  split <;> rfl

@[simp] theorem installPositionValueAtProbe_revealedAtProbe
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation) :
    (installPositionValueAtProbe target output observation).revealedAtProbe =
      observation.revealedAtProbe := by
  unfold installPositionValueAtProbe
  split <;> rfl

@[simp] theorem installPositionValueAtProbe_toProbe
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation) :
    (installPositionValueAtProbe target output observation).toProbe = observation.toProbe := by
  unfold installPositionValueAtProbe CleanProbeObservation.toProbe
  split <;> rfl

theorem installPositionValueAtProbe_existingHiddenHit_iff_of_target
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation)
    (hcoordinate : observation.coordinate = .position target) :
    (installPositionValueAtProbe target output observation).ExistingHiddenHit ↔
      observation.revealedAtProbe = false ∧
        truncateHash output = observation.candidate := by
  simp [installPositionValueAtProbe, hcoordinate, CleanProbeObservation.ExistingHiddenHit]

theorem installPositionValueAtProbe_existingHiddenHit_iff_of_ne
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation)
    (hcoordinate : observation.coordinate ≠ .position target) :
    (installPositionValueAtProbe target output observation).ExistingHiddenHit ↔
      observation.ExistingHiddenHit := by
  simp [installPositionValueAtProbe, hcoordinate]

theorem not_existingHiddenHit_installPositionValueAtProbe_of_avoids
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation)
    (hclean : ¬observation.ExistingHiddenHit)
    (havoid : observation.toProbe ≠
      ⟨.position target, truncateHash output⟩) :
    ¬(installPositionValueAtProbe target output observation).ExistingHiddenHit := by
  by_cases hcoordinate : observation.coordinate = .position target
  · rw [installPositionValueAtProbe_existingHiddenHit_iff_of_target target output observation
      hcoordinate]
    intro hhit
    apply havoid
    cases observation
    simp only [CleanProbeObservation.toProbe, Probe.mk.injEq] at hcoordinate ⊢
    exact ⟨hcoordinate, hhit.2.symm⟩
  · rw [installPositionValueAtProbe_existingHiddenHit_iff_of_ne target output observation
      hcoordinate]
    exact hclean

theorem map_toProbe_map_installPositionValueAtProbe
    (target : Position) (output : HashOutput)
    (observations : List CleanProbeObservation) :
    (observations.map (installPositionValueAtProbe target output)).map
        CleanProbeObservation.toProbe =
      observations.map CleanProbeObservation.toProbe := by
  rw [List.map_map]
  apply List.map_congr_left
  intro observation _hobservation
  exact installPositionValueAtProbe_toProbe target output observation

@[simp] theorem observedPrefixProbes_map_installPositionValueAtProbe
    (target : Position) (output : HashOutput)
    (result : ObservedCleanRunResult α) (ordinal : Nat) :
    observedPrefixProbes ordinal
        (some { result with observations :=
          result.observations.map (installPositionValueAtProbe target output) }) =
      observedPrefixProbes ordinal (some result) := by
  simp only [observedPrefixProbes]
  rw [List.map_take, map_toProbe_map_installPositionValueAtProbe]
  rw [List.map_take]

@[simp] theorem observedFirstLayerRootPosition?_map_installPositionValueAtProbe
    (target : Position) (output : HashOutput)
    (result : ObservedCleanRunResult α) (ordinal : Nat) :
    observedFirstLayerRootPosition? ordinal
        (some { result with observations :=
          result.observations.map (installPositionValueAtProbe target output) }) =
      observedFirstLayerRootPosition? ordinal (some result) := by
  simp only [observedFirstLayerRootPosition?]
  by_cases horiginal : ordinal < result.observations.length
  · have hmapped : ordinal <
        (result.observations.map (installPositionValueAtProbe target output)).length := by
      simpa only [List.length_map] using horiginal
    rw [dif_pos hmapped, dif_pos horiginal]
    simp only [List.get_eq_getElem, List.getElem_map,
      installPositionValueAtProbe_toProbe]
  · have hmapped : ¬ordinal <
        (result.observations.map (installPositionValueAtProbe target output)).length := by
      simpa only [List.length_map] using horiginal
    rw [dif_neg hmapped, dif_neg horiginal]

theorem observedPrefixProbes_eq_of_observations_eq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (hobservations : left.observations = right.observations) :
    observedPrefixProbes ordinal (some left) =
      observedPrefixProbes ordinal (some right) := by
  simp only [observedPrefixProbes]
  rw [hobservations]

theorem observedFirstLayerRootPosition?_eq_of_observations_eq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (hobservations : left.observations = right.observations) :
    observedFirstLayerRootPosition? ordinal (some left) =
      observedFirstLayerRootPosition? ordinal (some right) := by
  simp only [observedFirstLayerRootPosition?]
  rw [hobservations]

theorem firstExistingHiddenHitAt_of_observations_eq
    (left right : ObservedCleanRunResult α) (ordinal : Nat)
    (hobservations : left.observations = right.observations)
    (hfirst : FirstExistingHiddenHitAt left ordinal) :
    FirstExistingHiddenHitAt right ordinal := by
  obtain ⟨selected, hordinal, hhit, hbefore⟩ := hfirst
  let rightSelected : Fin right.observations.length :=
    ⟨selected.val, by rw [← hobservations]; exact selected.isLt⟩
  refine ⟨rightSelected, hordinal, ?_, ?_⟩
  · have hget : right.observations.get rightSelected =
        left.observations.get selected := by
      subst rightSelected
      simp [hobservations]
    rw [ExistingHiddenHitAtOrdinal, hget]
    exact hhit
  · intro rightEarlier hearlier
    let leftEarlier : Fin left.observations.length :=
      ⟨rightEarlier.val, by rw [hobservations]; exact rightEarlier.isLt⟩
    have hget : right.observations.get rightEarlier =
        left.observations.get leftEarlier := by
      subst leftEarlier
      simp [hobservations]
    rw [ExistingHiddenHitAtOrdinal, hget]
    exact hbefore leftEarlier hearlier

theorem firstExistingHiddenRootHitAt_of_first_of_position
    (result : ObservedCleanRunResult α) (ordinal : Nat) (target : Position)
    (hfirst : FirstExistingHiddenHitAt result ordinal)
    (hposition : observedFirstLayerRootPosition? ordinal (some result) = some target) :
    ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some result) := by
  have hfirstData := hfirst
  obtain ⟨selected, hordinal, _hhit, _hbefore⟩ := hfirstData
  refine ⟨selected, hordinal, hfirst, ?_⟩
  have hlt : ordinal < result.observations.length := by
    rw [← hordinal]
    exact selected.isLt
  simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte] at hposition
  have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = selected :=
    Fin.ext hordinal.symm
  rw [hindex, candidateLayerRootPosition?_eq_some_iff] at hposition
  exact ⟨target, hposition.1, hposition.2⟩

theorem no_existingHiddenHit_map_installPositionValueAtProbe_of_avoids
    (target : Position) (output : HashOutput)
    (observations : List CleanProbeObservation)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (havoid : CandidatesAvoidRoot target (truncateHash output)
      (observations.map CleanProbeObservation.toProbe)) :
    ∀ observation ∈ observations.map (installPositionValueAtProbe target output),
      ¬observation.ExistingHiddenHit := by
  intro observation hobservation
  rw [List.mem_map] at hobservation
  obtain ⟨before, hbefore, rfl⟩ := hobservation
  apply not_existingHiddenHit_installPositionValueAtProbe_of_avoids target output before
    (hclean before hbefore)
  apply havoid before.toProbe
  rw [List.mem_map]
  exact ⟨before, hbefore, rfl⟩

theorem installPositionValueAtProbe_eq_self
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation)
    (hvalue : observation.coordinate = .position target →
      observation.valueAtProbe = some output) :
    installPositionValueAtProbe target output observation = observation := by
  unfold installPositionValueAtProbe
  split
  · rename_i hcoordinate
    cases observation
    simp only [CleanProbeObservation.mk.injEq]
    simpa using (hvalue hcoordinate).symm
  · rfl

theorem installPositionValueAtProbe_cleanProbeObservation_eq_self
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (htarget : state.values (.position target) = some output)
    (coordinate : Coordinate) (candidate : Digest) :
    installPositionValueAtProbe target output
        (cleanProbeObservation state coordinate candidate) =
      cleanProbeObservation state coordinate candidate := by
  apply installPositionValueAtProbe_eq_self
  intro hcoordinate
  have : coordinate = .position target := by
    simpa [cleanProbeObservation] using hcoordinate
  subst coordinate
  simp [cleanProbeObservation, htarget]

theorem map_installPositionValueAtProbe_append_cleanProbeObservation
    (target : Position) (output : HashOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate)
    (htarget : state.values (.position target) = some output)
    (coordinate : Coordinate) (candidate : Digest) :
    (observations ++ [cleanProbeObservation state coordinate candidate]).map
        (installPositionValueAtProbe target output) =
      observations.map (installPositionValueAtProbe target output) ++
        [cleanProbeObservation state coordinate candidate] := by
  rw [List.map_append]
  simp [installPositionValueAtProbe_cleanProbeObservation_eq_self target output state htarget]

theorem firstExistingHiddenHitAt_map_installPositionValueAtProbe
    (target : Position) (output : HashOutput)
    (result : ObservedCleanRunResult α) (ordinal : Nat)
    (hfirst : FirstExistingHiddenHitAt result ordinal)
    (hselected : ∀ selected : Fin result.observations.length,
      selected.val = ordinal →
        (result.observations.get selected).coordinate = .position target ∧
          (result.observations.get selected).revealedAtProbe = false ∧
          truncateHash output = (result.observations.get selected).candidate)
    (havoid : ∀ earlier : Fin result.observations.length,
      earlier.val < ordinal →
        (result.observations.get earlier).toProbe ≠
          ⟨.position target, truncateHash output⟩) :
    FirstExistingHiddenHitAt
      { result with observations :=
          result.observations.map (installPositionValueAtProbe target output) }
      ordinal := by
  obtain ⟨selected, hordinal, _hhit, hbefore⟩ := hfirst
  let mappedSelected : Fin
      (result.observations.map (installPositionValueAtProbe target output)).length :=
    ⟨selected.val, by simpa only [List.length_map] using selected.isLt⟩
  refine ⟨mappedSelected, hordinal, ?_, ?_⟩
  · have hselectedData := hselected selected hordinal
    have hget :
        (result.observations.map (installPositionValueAtProbe target output)).get mappedSelected =
          installPositionValueAtProbe target output (result.observations.get selected) := by
      simp [mappedSelected]
    rw [ExistingHiddenHitAtOrdinal, hget,
      installPositionValueAtProbe_existingHiddenHit_iff_of_target target output
        (result.observations.get selected) hselectedData.1]
    exact hselectedData.2
  · intro mappedEarlier hearlier
    let earlier : Fin result.observations.length :=
      ⟨mappedEarlier.val, by simpa using mappedEarlier.isLt⟩
    have hclean : ¬(result.observations.get earlier).ExistingHiddenHit :=
      hbefore earlier hearlier
    have hsafe := not_existingHiddenHit_installPositionValueAtProbe_of_avoids
      target output (result.observations.get earlier) hclean (havoid earlier hearlier)
    have hget :
        (result.observations.map (installPositionValueAtProbe target output)).get mappedEarlier =
          installPositionValueAtProbe target output (result.observations.get earlier) := by
      simp [earlier]
    rw [ExistingHiddenHitAtOrdinal, hget]
    exact hsafe

end SphincsSecurity.Concrete.OtsProbeSimulation
