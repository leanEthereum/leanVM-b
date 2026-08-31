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
  exact if h : ∃ ordinal, PrivateWitnessAtOrdinal witness candidates ordinal then
    some (Classical.choose h)
  else
    none

theorem firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits
    (witness : PrivateHitWitness) (candidates : List Probe)
    (hhit : candidateListHits witness.position candidates witness.output) :
    ∃ ordinal, firstPrivateWitnessOrdinal? witness candidates = some ordinal ∧
      PrivateWitnessAtOrdinal witness candidates ordinal := by
  classical
  have hexists := exists_privateWitnessAtOrdinal_of_candidateListHits witness candidates hhit
  unfold firstPrivateWitnessOrdinal?
  simp only [hexists, dif_pos]
  exact ⟨Classical.choose hexists, rfl, Classical.choose_spec hexists⟩

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
