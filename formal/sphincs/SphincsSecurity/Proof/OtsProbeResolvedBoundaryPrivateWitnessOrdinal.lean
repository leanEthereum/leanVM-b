import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessPlan
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanNormalizedCount

/-!
# Private witness ordinals

Every retained private witness selects one concrete candidate ordinal. The selection is bounded by
the supported plan length, so a source computation with at most `q` outer hash queries places every
witness in `Fin q` without enumerating structural positions.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PrivateWitnessAtOrdinal
    (witness : PrivateHitWitness) (candidates : List Probe)
    (ordinal : Fin candidates.length) : Prop :=
  let candidate := candidates.get ordinal
  candidate.coordinate = .position witness.position ∧
    truncateHash witness.output = candidate.candidate

theorem exists_privateWitnessAtOrdinal_of_candidateListHits
    (witness : PrivateHitWitness) (candidates : List Probe)
    (hhit : candidateListHits witness.position candidates witness.output) :
    ∃ ordinal, PrivateWitnessAtOrdinal witness candidates ordinal := by
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ :=
    (candidateListHits_iff_exists_mem witness.position candidates witness.output).1 hhit
  obtain ⟨ordinal, hget⟩ := List.mem_iff_get.mp hcandidate
  exact ⟨ordinal, by
    unfold PrivateWitnessAtOrdinal
    rw [hget]
    exact ⟨hcoordinate, hdigest⟩⟩

noncomputable def firstPrivateWitnessOrdinal?
    (witness : PrivateHitWitness) (candidates : List Probe) :
    Option (Fin candidates.length) := by
  classical
  let matching := Finset.univ.filter fun ordinal : Fin candidates.length =>
    PrivateWitnessAtOrdinal witness candidates ordinal
  exact if h : matching.Nonempty then
    some (matching.min' h)
  else
    none

theorem firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits
    (witness : PrivateHitWitness) (candidates : List Probe)
    (hhit : candidateListHits witness.position candidates witness.output) :
    ∃ ordinal, firstPrivateWitnessOrdinal? witness candidates = some ordinal ∧
      PrivateWitnessAtOrdinal witness candidates ordinal := by
  classical
  obtain ⟨ordinal, hordinal⟩ :=
    exists_privateWitnessAtOrdinal_of_candidateListHits witness candidates hhit
  let matching := Finset.univ.filter fun selected : Fin candidates.length =>
    PrivateWitnessAtOrdinal witness candidates selected
  have hmatching : matching.Nonempty := by
    exact ⟨ordinal, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hordinal⟩⟩
  unfold firstPrivateWitnessOrdinal?
  simp only [matching, hmatching, dif_pos]
  refine ⟨matching.min' hmatching, rfl, ?_⟩
  exact (Finset.mem_filter.mp (matching.min'_mem hmatching)).2

theorem firstPrivateWitnessOrdinal?_le_of_eq_some_of_matches
    (witness : PrivateHitWitness) (candidates : List Probe)
    (ordinal other : Fin candidates.length)
    (hfirst : firstPrivateWitnessOrdinal? witness candidates = some ordinal)
    (hother : PrivateWitnessAtOrdinal witness candidates other) :
    ordinal.val ≤ other.val := by
  classical
  let matching := Finset.univ.filter fun selected : Fin candidates.length =>
    PrivateWitnessAtOrdinal witness candidates selected
  have hmatching : matching.Nonempty := by
    exact ⟨other, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩⟩
  unfold firstPrivateWitnessOrdinal? at hfirst
  simp only [matching, hmatching, dif_pos, Option.some.injEq] at hfirst
  subst ordinal
  exact_mod_cast matching.min'_le other
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩)

def WitnessFirstUsesOrdinal
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ witness sourceOrdinal,
    output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
      firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal

def WitnessFirstUsesLayerRootOrdinal
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ witness sourceOrdinal,
    output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
      firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal ∧
      (output.2.get sourceOrdinal).IsLayerRoot

def WitnessFirstUsesNonLayerRootOrdinal
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ witness sourceOrdinal,
    output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
      firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal ∧
      ¬(output.2.get sourceOrdinal).IsLayerRoot

theorem witnessFirstUsesOrdinal_iff_root_or_nonRoot
    {ordinal : Nat} {output : PrivateWitnessPlanOutput} :
    WitnessFirstUsesOrdinal ordinal output ↔
      WitnessFirstUsesLayerRootOrdinal ordinal output ∨
        WitnessFirstUsesNonLayerRootOrdinal ordinal output := by
  constructor
  · rintro ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst⟩
    by_cases hroot : (output.2.get sourceOrdinal).IsLayerRoot
    · exact Or.inl ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst, hroot⟩
    · exact Or.inr ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst, hroot⟩
  · rintro (⟨witness, sourceOrdinal, hwitness, hvalue, hfirst, _hroot⟩ |
      ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst, _hroot⟩)
    · exact ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst⟩
    · exact ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst⟩

noncomputable def boundedPrivateWitnessOrdinal?
    (q : Nat) (output : PrivateWitnessPlanOutput) : Option (Fin q) := by
  classical
  match output.1 with
  | none => exact none
  | some witness =>
      match firstPrivateWitnessOrdinal? witness output.2 with
      | none => exact none
      | some ordinal =>
          if hlt : ordinal.val < q then exact some ⟨ordinal.val, hlt⟩ else exact none

theorem boundedPrivateWitnessOrdinal?_eq_some_of_covered
    (q : Nat) (output : PrivateWitnessPlanOutput) (witness : PrivateHitWitness)
    (hwitness : output.1 = some witness)
    (hcovered : PrivateWitnessCovered output) (hlength : output.2.length ≤ q) :
    ∃ ordinal : Fin q,
      boundedPrivateWitnessOrdinal? q output = some ordinal ∧
        ∃ sourceOrdinal : Fin output.2.length,
          sourceOrdinal.val = ordinal.val ∧
            PrivateWitnessAtOrdinal witness output.2 sourceOrdinal := by
  classical
  have hhit := hcovered witness hwitness
  obtain ⟨sourceOrdinal, hfirst, hsource⟩ :=
    firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits witness output.2 hhit
  have hlt : sourceOrdinal.val < q := sourceOrdinal.isLt.trans_le hlength
  let ordinal : Fin q := ⟨sourceOrdinal.val, hlt⟩
  refine ⟨ordinal, ?_, sourceOrdinal, rfl, hsource⟩
  unfold boundedPrivateWitnessOrdinal?
  simp only [hwitness]
  rw [hfirst]
  simp [hlt, ordinal]

theorem support_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve_length_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value candidates)) :
    output.2.length ≤ candidates.length + q := by
  have herased : erasePrivateWitnessPlanOutput output ∈ support
      (granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
        ftsSecret context fuel value candidates) := by
    rw [← map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary
      parameter table ftsSecret context fuel value candidates, support_map]
    exact ⟨output, houtput, rfl⟩
  exact support_granularDetailedRetainedRestNormalizedPrivatePlanObserve_length_le adversary
    parameter table ftsSecret context fuel value candidates q hbound
    (erasePrivateWitnessPlanOutput output) herased

theorem supported_retained_privateWitness_has_bounded_ordinal
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (hcovered : PendingCoveredBy candidates context)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value candidates))
    (witness : PrivateHitWitness) (hwitness : output.1 = some witness) :
    ∃ ordinal : Fin (candidates.length + q),
      boundedPrivateWitnessOrdinal? (candidates.length + q) output = some ordinal := by
  have houtputCovered :=
    privateWitnessCovered_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
      adversary parameter table ftsSecret context fuel value candidates hcovered output houtput
  have hlength :=
    support_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve_length_le adversary
      parameter table ftsSecret context fuel value candidates q hbound output houtput
  obtain ⟨ordinal, hordinal, _⟩ :=
    boundedPrivateWitnessOrdinal?_eq_some_of_covered (candidates.length + q) output witness
      hwitness houtputCovered hlength
  exact ⟨ordinal, hordinal⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
