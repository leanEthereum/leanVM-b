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

end SphincsSecurity.Concrete.OtsProbeSimulation
