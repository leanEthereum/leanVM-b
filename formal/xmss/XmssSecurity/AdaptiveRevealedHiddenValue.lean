import XmssSecurity.IndexedHiddenValue

open OracleComp ENNReal

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable local instance adaptiveRevealSampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance adaptiveRevealSampleableTable :
    SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

def installReveals (table : Index → Digest) :
    List (Index × Digest) → Index → Digest
  | [] => table
  | reveal :: reveals =>
      Function.update (installReveals table reveals) reveal.1 reveal.2

omit [Fintype Index] in
@[simp]
theorem installReveals_nil (table : Index → Digest) :
    installReveals table [] = table := rfl

omit [Fintype Index] in
theorem installReveals_cons (table : Index → Digest)
    (reveal : Index × Digest) (reveals : List (Index × Digest)) :
    installReveals table (reveal :: reveals) =
      Function.update (installReveals table reveals) reveal.1 reveal.2 := rfl

omit [Fintype Index] in
theorem installReveals_eq_of_not_mem
    (table : Index → Digest) (reveals : List (Index × Digest))
    (index : Index) (hindex : index ∉ reveals.map Prod.fst) :
    installReveals table reveals index = table index := by
  induction reveals with
  | nil => rfl
  | cons reveal reveals ih =>
      have hne : index ≠ reveal.1 := by
        intro heq
        apply hindex
        simp [heq]
      have htail : index ∉ reveals.map Prod.fst := by
        intro hmem
        apply hindex
        simp [hmem]
      rw [installReveals_cons, Function.update_of_ne hne]
      exact ih htail

omit [Fintype Index] [DecidableEq Index] in
theorem readMany_eq_of_probe_values_eq
    (left right : Index → Digest) (queries : Nat)
    (strategy : List Bool → Index × Digest)
    (heq : ∀ history,
      left (strategy history).1 = right (strategy history).1) :
    readMany left queries strategy = readMany right queries strategy := by
  induction queries generalizing strategy with
  | zero => rfl
  | succ queries ih =>
      rw [readMany, readMany, heq []]
      exact congrArg (fun later =>
        decide (right (strategy []).1 = (strategy []).2) || later)
        (ih (fun history => strategy
          (decide (right (strategy []).1 = (strategy []).2) :: history))
          (fun history => heq
            (decide (right (strategy []).1 = (strategy []).2) :: history)))

def AvoidsReveals
    (reveals : List (Index × Digest))
    (strategy : List Bool → Index × Digest) : Prop :=
  ∀ history, (strategy history).1 ∉ reveals.map Prod.fst

omit [Fintype Index] in
theorem readMany_installReveals_eq
    (table : Index → Digest) (reveals : List (Index × Digest))
    (queries : Nat) (strategy : List Bool → Index × Digest)
    (havoid : AvoidsReveals reveals strategy) :
    readMany (installReveals table reveals) queries strategy =
      readMany table queries strategy := by
  apply readMany_eq_of_probe_values_eq
  intro history
  exact installReveals_eq_of_not_mem table reveals
    (strategy history).1 (havoid history)

noncomputable def adaptiveRevealGuessExperiment
    (transcriptGenerator : ProbComp (List (Index × Digest)))
    (queries : Nat)
    (strategy : List (Index × Digest) →
      List Bool → Index × Digest) : ProbComp Bool := do
  let reveals ← transcriptGenerator
  let table ← $ᵗ (Index → Digest)
  return readMany (installReveals table reveals) queries
    (strategy reveals)

/-- An arbitrary randomized disclosure transcript does not weaken adaptive equality-probe security at coordinates outside that transcript. -/
theorem adaptive_guess_after_adaptive_reveals_le
    (transcriptGenerator : ProbComp (List (Index × Digest)))
    (queries : Nat)
    (strategy : List (Index × Digest) →
      List Bool → Index × Digest)
    (havoid : ∀ reveals,
      AvoidsReveals reveals (strategy reveals)) :
    Pr[(fun hit : Bool => hit = true) |
      adaptiveRevealGuessExperiment transcriptGenerator queries strategy] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let strategyGenerator : ProbComp (List Bool → Index × Digest) :=
    strategy <$> transcriptGenerator
  have hdist :
      𝒟[adaptiveRevealGuessExperiment transcriptGenerator queries strategy] =
        𝒟[adaptiveGuessExperiment strategyGenerator queries] := by
    unfold adaptiveRevealGuessExperiment adaptiveGuessExperiment experiment
      strategyGenerator
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro reveals
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro table
    congr 2
    exact readMany_installReveals_eq table reveals queries
      (strategy reveals) (havoid reveals)
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (adaptive_guess_after_public_sampling_le strategyGenerator queries)

end XmssSecurity.IndexedHiddenValue
