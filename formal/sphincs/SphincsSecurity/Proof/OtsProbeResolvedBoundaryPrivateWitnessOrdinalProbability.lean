import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinal

/-!
# One-ordinal private endpoint

One selected plan ordinal tests at most one structural output. The fixed-list endpoint deliberately
ignores every other candidate, since their misses belong to the all-miss prefix that produces the
selected candidate rather than to additional target events.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def plannedOrdinalCandidateFire
    (ordinal : Nat) (candidates : List Probe) : ProbComp Bool :=
  match candidates[ordinal]? with
  | none => pure false
  | some candidate =>
      match candidate.coordinate with
      | .chainStart _ _ _ _ => pure false
      | .position _ => do
          let output ← LazyRevealProbe.sampleHashOutput
          pure (truncateHash output = candidate.candidate)

noncomputable def privateCandidateFire
    (candidate : Probe) (context : DeferredContext) : ProbComp Bool :=
  match candidate.coordinate with
  | .chainStart _ _ _ _ => pure false
  | .position position => do
      let output ← deferredPositionOutput position context
      pure (truncateHash output = candidate.candidate)

theorem privateCandidateFire_eq_planned_of_fresh
    (candidate : Probe) (context : DeferredContext)
    (hstate : ∀ position, candidate.coordinate = .position position →
      context.state.values (.position position) = none)
    (hprivate : ∀ position, candidate.coordinate = .position position →
      context.values position = none) :
    privateCandidateFire candidate context =
      (match candidate.coordinate with
      | .chainStart _ _ _ _ => pure false
      | .position _ => do
          let output ← LazyRevealProbe.sampleHashOutput
          pure (truncateHash output = candidate.candidate)) := by
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcoordinate]
  | position position =>
      simp [privateCandidateFire, hcoordinate, deferredPositionOutput,
        DeferredContext.positionValue, hstate position hcoordinate,
        hprivate position hcoordinate]

theorem probEvent_privateCandidateFire_le_of_fresh
    (candidate : Probe) (context : DeferredContext)
    (hstate : ∀ position, candidate.coordinate = .position position →
      context.state.values (.position position) = none)
    (hprivate : ∀ position, candidate.coordinate = .position position →
      context.values position = none) :
    Pr[= true | privateCandidateFire candidate context] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [privateCandidateFire_eq_planned_of_fresh candidate context hstate hprivate]
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp
  | position position =>
      change Pr[= true | (fun output : HashOutput =>
        decide (truncateHash output = candidate.candidate)) <$>
          LazyRevealProbe.sampleHashOutput] ≤ _
      calc
        _ = Pr[fun output : HashOutput => truncateHash output = candidate.candidate |
            LazyRevealProbe.sampleHashOutput] := by
          rw [← probEvent_eq_eq_probOutput, probEvent_map]
          exact OracleComp.probEvent_congr' (fun _ _ => by simp) rfl
        _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
          unfold LazyRevealProbe.sampleHashOutput
          exact SphincsSecurity.probEvent_uniform_truncateHash_eq _
        _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          rw [show Fintype.card Digest = 2 ^ digestBits by simp]
        _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := le_rfl

theorem probEvent_privateCandidateFire_empty_le (candidate : Probe) :
    Pr[= true | privateCandidateFire candidate
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_privateCandidateFire_le_of_fresh
  · intro position _hcoordinate
    rfl
  · intro position _hcoordinate
    rfl

theorem probEvent_bind_privateCandidateFire_empty_le (candidates : ProbComp Probe) :
    Pr[= true | candidates >>= fun candidate => privateCandidateFire candidate
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro candidate _hcandidate
  rw [probEvent_eq_eq_probOutput]
  exact probEvent_privateCandidateFire_empty_le candidate

theorem probEvent_plannedOrdinalCandidateFire_le
    (ordinal : Nat) (candidates : List Probe) :
    Pr[= true | plannedOrdinalCandidateFire ordinal candidates] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold plannedOrdinalCandidateFire
  cases hcandidate : candidates[ordinal]? with
  | none => simp
  | some candidate =>
      simp only
      cases hcoordinate : candidate.coordinate with
      | chainStart lay tree leafIdx chainIdx => simp
      | position target =>
          change Pr[= true | (fun output : HashOutput =>
            decide (truncateHash output = candidate.candidate)) <$>
              LazyRevealProbe.sampleHashOutput] ≤ _
          calc
            _ = Pr[fun output : HashOutput => truncateHash output = candidate.candidate |
                LazyRevealProbe.sampleHashOutput] := by
              rw [← probEvent_eq_eq_probOutput, probEvent_map]
              exact OracleComp.probEvent_congr' (fun _ _ => by simp) rfl
            _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              unfold LazyRevealProbe.sampleHashOutput
              exact SphincsSecurity.probEvent_uniform_truncateHash_eq _
            _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
              rw [show Fintype.card Digest = 2 ^ digestBits by simp]
            _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := le_rfl

theorem probEvent_bind_plannedOrdinalCandidateFire_le
    (plans : ProbComp (List Probe)) (ordinal : Nat) :
    Pr[= true | plans >>= plannedOrdinalCandidateFire ordinal] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro candidates _hcandidates
  rw [probEvent_eq_eq_probOutput]
  exact probEvent_plannedOrdinalCandidateFire_le ordinal candidates

def WitnessUsesOrdinal
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ witness sourceOrdinal,
    output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
      PrivateWitnessAtOrdinal witness output.2 sourceOrdinal

theorem witnessUsesOrdinal_of_bounded_eq
    (q : Nat) (output : PrivateWitnessPlanOutput) (ordinal : Fin q)
    (hcovered : PrivateWitnessCovered output)
    (hordinal : boundedPrivateWitnessOrdinal? q output = some ordinal) :
    WitnessUsesOrdinal ordinal.val output := by
  classical
  cases hwitness : output.1 with
  | none =>
      unfold boundedPrivateWitnessOrdinal? at hordinal
      simp [hwitness] at hordinal
  | some witness =>
      have hhit := hcovered witness hwitness
      obtain ⟨sourceOrdinal, hfirst, hsource⟩ :=
        firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits witness output.2 hhit
      unfold boundedPrivateWitnessOrdinal? at hordinal
      simp only [hwitness] at hordinal
      rw [hfirst] at hordinal
      by_cases hlt : sourceOrdinal.val < q
      · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hordinal
        have hval := congrArg Fin.val hordinal
        exact ⟨witness, sourceOrdinal, hwitness, hval, hsource⟩
      · simp [hlt] at hordinal

theorem probEvent_privateWitness_le_of_bounded_ordinals
    (run : ProbComp PrivateWitnessPlanOutput) (q : Nat) (epsilon : ℝ≥0∞)
    (hclassifies : ∀ output ∈ support run, output.1.isSome = true →
      ∃ ordinal : Fin q, boundedPrivateWitnessOrdinal? q output = some ordinal)
    (hordinal : ∀ ordinal : Fin q,
      Pr[fun output => boundedPrivateWitnessOrdinal? q output = some ordinal | run] ≤
        epsilon) :
    Pr[fun output => output.1.isSome = true | run] ≤ (q : ℝ≥0∞) * epsilon := by
  classical
  calc
    _ ≤ Pr[fun output => ∃ ordinal ∈ (Finset.univ : Finset (Fin q)),
          boundedPrivateWitnessOrdinal? q output = some ordinal | run] := by
      apply probEvent_mono
      intro output houtput hwitness
      obtain ⟨ordinal, hordinal⟩ := hclassifies output houtput hwitness
      exact ⟨ordinal, Finset.mem_univ ordinal, hordinal⟩
    _ ≤ ∑ ordinal ∈ (Finset.univ : Finset (Fin q)),
          Pr[fun output => boundedPrivateWitnessOrdinal? q output = some ordinal | run] :=
      probEvent_exists_finset_le_sum Finset.univ run
        (fun ordinal output => boundedPrivateWitnessOrdinal? q output = some ordinal)
    _ ≤ ∑ _ordinal ∈ (Finset.univ : Finset (Fin q)), epsilon := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      exact hordinal ordinal
    _ = (q : ℝ≥0∞) * epsilon := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

end SphincsSecurity.Concrete.OtsProbeSimulation
