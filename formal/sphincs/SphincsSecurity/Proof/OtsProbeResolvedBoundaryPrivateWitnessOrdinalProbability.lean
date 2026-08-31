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

noncomputable def preparePrivateCandidate
    (candidate : Probe) (context : DeferredContext) :
    ProbComp (Option DeferredContext) :=
  match candidate.coordinate with
  | .chainStart _ _ _ _ => pure (some context)
  | .position position => do
      let output ← deferredPositionOutput position context
      if truncateHash output = candidate.candidate then
        pure none
      else
        pure (some { context with values := context.values.install position output })

theorem map_isNone_preparePrivateCandidate
    (candidate : Probe) (context : DeferredContext) :
    Option.isNone <$> preparePrivateCandidate candidate context =
      privateCandidateFire candidate context := by
  unfold preparePrivateCandidate privateCandidateFire
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp
  | position position =>
      simp only [map_bind]
      apply bind_congr
      intro output
      by_cases hhit : truncateHash output = candidate.candidate <;> simp [hhit]

theorem privateCandidateFire_ensure
    (candidate : Probe) (context : DeferredContext) (coordinate : Coordinate) :
    privateCandidateFire candidate
        { context with state := context.state.ensure coordinate } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position position => rfl

theorem privateCandidateFire_addPending
    (candidate : Probe) (context : DeferredContext)
    (coordinate : Coordinate) (digest : Digest) :
    privateCandidateFire candidate
        { context with state := context.state.addPending coordinate digest } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position position => rfl

theorem privateCandidateFire_publish
    (candidate : Probe) (context : DeferredContext) (coordinate : Coordinate) :
    privateCandidateFire candidate
        { context with state := context.state.publish coordinate } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position position => rfl

theorem privateCandidateFire_clearPending
    (candidate : Probe) (context : DeferredContext) (coordinate : Coordinate) :
    privateCandidateFire candidate
        { context with state := context.state.clearPending coordinate } =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position position => rfl

theorem privateCandidateFire_canonicalize
    (table : OtsSecretIndex → HashOutput)
    (candidate : Probe) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) :
    privateCandidateFire candidate (canonicalizeMaterializedValues table context) =
      privateCandidateFire candidate context := by
  cases hcandidate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [privateCandidateFire, hcandidate]
  | position position =>
      simp only [privateCandidateFire, hcandidate]
      unfold deferredPositionOutput
      rw [canonicalizeMaterializedValues_positionValue table context hconsistent position]

theorem candidateOutputsSafe_preparePrivateCandidate
    (candidate : Probe) (context prepared : DeferredContext)
    (hprepared : some prepared ∈ support (preparePrivateCandidate candidate context)) :
    CandidateOutputsSafe prepared [candidate] := by
  unfold preparePrivateCandidate at hprepared
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [hcoordinate, CandidateOutputsSafe]
  | position position =>
      simp only [hcoordinate, mem_support_bind_iff] at hprepared
      obtain ⟨output, _houtput, hreturn⟩ := hprepared
      by_cases hhit : truncateHash output = candidate.candidate
      · simp [hhit] at hreturn
      · simp [hhit] at hreturn
        subst prepared
        intro found hfound
        simp only [List.mem_singleton] at hfound
        subst found
        simp only [hcoordinate]
        exact ⟨output, by simp [DeferredStructuralValues.install], hhit⟩

theorem not_recordedCandidateHit_of_preparePrivateCandidate_run
    (candidate : Probe) (context prepared : DeferredContext)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hprepared : some prepared ∈ support (preparePrivateCandidate candidate context))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable prepared fuel table computation)) :
    ¬RecordedCandidateHit result.context [candidate] := by
  have hsafe := candidateOutputsSafe_preparePrivateCandidate candidate context prepared hprepared
  have hvalues := privateValuesLE_of_done_runDirectResolvedDetailedFromTable
    computation prepared fuel table result hresult
  exact not_recordedCandidateHit_of_candidateOutputsSafe result.context [candidate]
    (hsafe.of_privateValuesLE hvalues)

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
    simp [emptyDeferredStructuralValues]

theorem probEvent_preparePrivateCandidate_empty_none_le (candidate : Probe) :
    Pr[= none | preparePrivateCandidate candidate
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun result => Option.isNone result = true |
        preparePrivateCandidate candidate
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }] := by
      rw [← probEvent_eq_eq_probOutput]
      apply OracleComp.probEvent_congr' (fun result _ => by cases result <;> simp) rfl
    _ = Pr[fun hit : Bool => hit = true |
        Option.isNone <$> preparePrivateCandidate candidate
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }] := by
      rw [probEvent_map]
      exact OracleComp.probEvent_congr' (fun result _ => by simp) rfl
    _ = Pr[= true | Option.isNone <$> preparePrivateCandidate candidate
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }] :=
      probEvent_eq_eq_probOutput _ true
    _ = Pr[= true | privateCandidateFire candidate
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }] :=
      OracleComp.probOutput_congr rfl
        (congrArg evalDist (map_isNone_preparePrivateCandidate candidate _))
    _ ≤ _ := probEvent_privateCandidateFire_empty_le candidate

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

theorem witnessUsesOrdinal_of_witnessFirstUsesOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesOrdinal ordinal output) :
    WitnessUsesOrdinal ordinal output := by
  obtain ⟨witness, sourceOrdinal, hwitness, hvalue, hfirst⟩ := hfirst
  have hmatch : PrivateWitnessAtOrdinal witness output.2 sourceOrdinal := by
    classical
    unfold firstPrivateWitnessOrdinal? at hfirst
    let matching := Finset.univ.filter fun selected : Fin output.2.length =>
      PrivateWitnessAtOrdinal witness output.2 selected
    by_cases hmatching : matching.Nonempty
    · simp only [matching, hmatching, dif_pos, Option.some.injEq] at hfirst
      rw [← hfirst]
      exact (Finset.mem_filter.mp (matching.min'_mem hmatching)).2
    · simp [matching, hmatching] at hfirst
  exact ⟨witness, sourceOrdinal, hwitness, hvalue, hmatch⟩

theorem witnessUsesOrdinal_of_witnessFirstUsesNonLayerRootOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesNonLayerRootOrdinal ordinal output) :
    WitnessUsesOrdinal ordinal output := by
  obtain ⟨witness, sourceOrdinal, hwitness, hvalue, hselected, _hroot⟩ := hfirst
  exact witnessUsesOrdinal_of_witnessFirstUsesOrdinal
    ⟨witness, sourceOrdinal, hwitness, hvalue, hselected⟩

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

theorem witnessFirstUsesOrdinal_of_bounded_eq
    (q : Nat) (output : PrivateWitnessPlanOutput) (ordinal : Fin q)
    (hordinal : boundedPrivateWitnessOrdinal? q output = some ordinal) :
    WitnessFirstUsesOrdinal ordinal.val output := by
  classical
  cases hwitness : output.1 with
  | none =>
      unfold boundedPrivateWitnessOrdinal? at hordinal
      simp [hwitness] at hordinal
  | some witness =>
      cases hfirst : firstPrivateWitnessOrdinal? witness output.2 with
      | none =>
          unfold boundedPrivateWitnessOrdinal? at hordinal
          simp [hwitness, hfirst] at hordinal
      | some sourceOrdinal =>
          unfold boundedPrivateWitnessOrdinal? at hordinal
          simp only [hwitness, hfirst] at hordinal
          by_cases hlt : sourceOrdinal.val < q
          · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hordinal
            have hval := congrArg Fin.val hordinal
            exact ⟨witness, sourceOrdinal, hwitness, hval, hfirst⟩
          · simp [hlt] at hordinal

theorem not_privateWitnessAtOrdinal_of_witnessFirstUsesOrdinal_of_lt
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesOrdinal ordinal output)
    (earlier : Fin output.2.length) (hlt : earlier.val < ordinal) :
    ∀ witness, output.1 = some witness →
      ¬PrivateWitnessAtOrdinal witness output.2 earlier := by
  intro witness hwitness hearlier
  obtain ⟨selectedWitness, sourceOrdinal, hselectedWitness, hsourceValue, hsourceFirst⟩ := hfirst
  have hwitnessEq : witness = selectedWitness := by
    exact Option.some.inj (hwitness.symm.trans hselectedWitness)
  subst witness
  have hle := firstPrivateWitnessOrdinal?_le_of_eq_some_of_matches selectedWitness output.2
    sourceOrdinal earlier hsourceFirst hearlier
  omega

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
