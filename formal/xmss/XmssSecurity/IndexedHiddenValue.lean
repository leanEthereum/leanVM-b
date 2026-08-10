import XmssSecurity.HiddenValue
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance : SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

noncomputable def readMany (table : Index → Digest) :
    Nat → (List Bool → Index × Digest) → Bool
  | 0, _ => false
  | queries + 1, strategy =>
      let probe := strategy []
      let hit := decide (table probe.1 = probe.2)
      hit || readMany table queries (fun history => strategy (hit :: history))

noncomputable def experiment (queries : Nat)
    (strategy : List Bool → Index × Digest) : ProbComp Bool := do
  let table ← $ᵗ (Index → Digest)
  return readMany table queries strategy

omit [Fintype Index] [DecidableEq Index] in
theorem readMany_true_iff (table : Index → Digest) (queries : Nat)
    (strategy : List Bool → Index × Digest) :
    readMany table queries strategy = true ↔
      ∃ round < queries,
        table (strategy (List.replicate round false)).1 =
          (strategy (List.replicate round false)).2 := by
  induction queries generalizing strategy with
  | zero => simp [readMany]
  | succ queries ih =>
      rw [readMany]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (hit | later)
        · exact ⟨0, Nat.succ_pos queries, by simpa using hit⟩
        · by_cases hit : table (strategy []).1 = (strategy []).2
          · exact ⟨0, Nat.succ_pos queries, by simpa using hit⟩
          · rw [decide_eq_false (by simpa using hit)] at later
            obtain ⟨round, hround, hhit⟩ :=
              (ih (fun history => strategy (false :: history))).1 later
            exact ⟨round + 1, Nat.succ_lt_succ hround, by
              simpa [List.replicate_succ] using hhit⟩
      · rintro ⟨round, hround, hhit⟩
        cases round with
        | zero => left; simpa using hhit
        | succ round =>
            by_cases hit : table (strategy []).1 = (strategy []).2
            · exact Or.inl hit
            · refine Or.inr ?_
              rw [decide_eq_false (by simpa using hit)]
              exact (ih (fun history => strategy (false :: history))).2
                ⟨round, Nat.lt_of_succ_lt_succ hround, by
                  simpa [List.replicate_succ] using hhit⟩

theorem uniform_table_coordinate_probability (index : Index) (target : Digest) :
    Pr[fun table : Index → Digest => table index = target | $ᵗ (Index → Digest)] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let embed : Unit → Index := fun _ => index
  have hembed : Function.Injective embed := by
    intro left right _
    cases left
    cases right
    rfl
  let evaluate : (Unit → Digest) → Digest := fun table => table ()
  have hevaluate : Function.Bijective evaluate := by
    constructor
    · intro left right heq
      funext input
      cases input
      exact heq
    · intro value
      exact ⟨fun _ => value, rfl⟩
  have hmarginal :
      𝒟[evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))] =
        𝒟[$ᵗ Digest] := by
    have hrestrict :
        𝒟[(fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest))] =
          𝒟[$ᵗ (Unit → Digest)] := by
      simpa [bind_pure_comp] using
        evalDist_uniformSample_map_comp_injective (R := Digest) hembed
    rw [evalDist_map, hrestrict, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross
      (α := Unit → Digest) (β := Digest) evaluate hevaluate
  calc
    Pr[fun table : Index → Digest => table index = target | $ᵗ (Index → Digest)] =
        Pr[fun value : Digest => value = target |
          evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))] := by
      rw [probEvent_map, probEvent_map]
      rfl
    _ = Pr[fun value : Digest => value = target | $ᵗ Digest] :=
      probEvent_congr' (fun _ _ => Iff.rfl) hmarginal
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      by simpa only [probEvent_eq_eq_probOutput] using
        HiddenValue.uniform_digest_point_probability target

/-- Adaptive probes against an indexed table pay once per probe, not once per index. -/
theorem adaptive_guess_le (queries : Nat)
    (strategy : List Bool → Index × Digest) :
    Pr[(fun hit : Bool => hit = true) | experiment queries strategy] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hevent :
      (fun table : Index → Digest => readMany table queries strategy = true) =
        (fun table : Index → Digest => ∃ round ∈ Finset.range queries,
          table (strategy (List.replicate round false)).1 =
            (strategy (List.replicate round false)).2) := by
    funext table
    apply propext
    rw [readMany_true_iff]
    simp only [Finset.mem_range]
  unfold experiment
  change Pr[(fun hit : Bool => hit = true) |
    (fun table : Index → Digest => readMany table queries strategy) <$> ($ᵗ (Index → Digest))] ≤ _
  rw [probEvent_map]
  change Pr[(fun table : Index → Digest => readMany table queries strategy = true) |
    $ᵗ (Index → Digest)] ≤ _
  rw [hevent]
  calc
    Pr[fun table : Index → Digest => ∃ round ∈ Finset.range queries,
          table (strategy (List.replicate round false)).1 =
            (strategy (List.replicate round false)).2 |
        $ᵗ (Index → Digest)] ≤
      ∑ round ∈ Finset.range queries,
        Pr[fun table : Index → Digest =>
          table (strategy (List.replicate round false)).1 =
            (strategy (List.replicate round false)).2 |
          $ᵗ (Index → Digest)] :=
      probEvent_exists_finset_le_sum (Finset.range queries) ($ᵗ (Index → Digest))
        (fun round table => table (strategy (List.replicate round false)).1 =
          (strategy (List.replicate round false)).2)
    _ = ∑ _round ∈ Finset.range queries,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro round _
      exact uniform_table_coordinate_probability
        (strategy (List.replicate round false)).1
        (strategy (List.replicate round false)).2
    _ = (queries : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      rw [div_eq_mul_inv]

noncomputable def adaptiveGuessExperiment
    (strategyGenerator : ProbComp (List Bool → Index × Digest))
    (queries : Nat) : ProbComp Bool :=
  strategyGenerator >>= experiment queries

/-- Public randomness may select indexed probes before the independent hidden table is drawn. -/
theorem adaptive_guess_after_public_sampling_le
    (strategyGenerator : ProbComp (List Bool → Index × Digest))
    (queries : Nat) :
    Pr[(fun hit : Bool => hit = true) |
      adaptiveGuessExperiment strategyGenerator queries] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold adaptiveGuessExperiment
  exact probEvent_bind_le_of_forall_le fun strategy _ =>
    adaptive_guess_le queries strategy

end XmssSecurity.IndexedHiddenValue
