import XmssSecurity.Proof.IndexedHiddenValue
import Mathlib.Data.List.GetD

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

omit [Fintype Index] in
theorem installReveals_eq_self_of_values
    (table : Index → Digest) (reveals : List (Index × Digest))
    (hvalues : ∀ reveal ∈ reveals, table reveal.1 = reveal.2) :
    installReveals table reveals = table := by
  induction reveals with
  | nil => rfl
  | cons reveal reveals ih =>
      rw [installReveals_cons, ih (fun candidate hcandidate =>
        hvalues candidate (by simp [hcandidate]))]
      funext index
      by_cases heq : index = reveal.1
      · subst index
        simp [hvalues reveal (by simp)]
      · simp [Function.update_of_ne heq]

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

def listStrategy (default : Index × Digest)
    (probes : List (Index × Digest)) : List Bool → Index × Digest :=
  fun history => probes.getD history.length default

omit [Fintype Index] [DecidableEq Index] in
theorem listStrategy_mem
    (default : Index × Digest) (probes : List (Index × Digest))
    (hdefault : default ∈ probes) (history : List Bool) :
    listStrategy default probes history ∈ probes := by
  unfold listStrategy
  by_cases hlength : history.length < probes.length
  · rw [List.getD_eq_getElem probes default hlength]
    exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hlength)]
    exact hdefault

omit [Fintype Index] [DecidableEq Index] in
theorem listStrategy_avoids
    (reveals probes : List (Index × Digest))
    (default : Index × Digest) (hdefault : default ∈ probes)
    (hprobes : ∀ probe ∈ probes, probe.1 ∉ reveals.map Prod.fst) :
    AvoidsReveals reveals (listStrategy default probes) := by
  intro history
  exact hprobes _ (listStrategy_mem default probes hdefault history)

omit [Fintype Index] [DecidableEq Index] in
theorem readMany_listStrategy_eq_true_of_mem
    (table : Index → Digest) (queries : Nat)
    (probes : List (Index × Digest)) (default probe : Index × Digest)
    (hqueries : probes.length ≤ queries) (hprobe : probe ∈ probes)
    (hhit : table probe.1 = probe.2) :
    readMany table queries (listStrategy default probes) = true := by
  rw [readMany_true_iff]
  obtain ⟨round, hround, hget⟩ := List.mem_iff_getElem.mp hprobe
  refine ⟨round, hround.trans_le hqueries, ?_⟩
  unfold listStrategy
  simp only [List.length_replicate]
  rw [List.getD_eq_getElem probes default hround, hget]
  exact hhit

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

structure RevealProbeView (Index : Type) where
  reveals : List (Index × Digest)
  table : Index → Digest
  strategy : List Bool → Index × Digest

noncomputable def adaptiveRevealViewExperiment
    (transcriptGenerator : ProbComp
      (List (Index × Digest) × (List Bool → Index × Digest))) :
    ProbComp (RevealProbeView Index) := do
  let transcript ← transcriptGenerator
  let table ← $ᵗ (Index → Digest)
  return ⟨transcript.1, installReveals table transcript.1, transcript.2⟩

def RevealProbeView.HitsAvoidingReveals
    (queries : Nat) (view : RevealProbeView Index) : Prop :=
  readMany view.table queries view.strategy = true ∧
    AvoidsReveals view.reveals view.strategy

/-- Even without requiring every generated strategy to be safe, the event that it both avoids its disclosure transcript and hits the installed table costs at most one uniform-digest guess per probe. -/
theorem adaptive_reveal_view_hit_le
    (transcriptGenerator : ProbComp
      (List (Index × Digest) × (List Bool → Index × Digest)))
    (queries : Nat) :
    Pr[RevealProbeView.HitsAvoidingReveals queries |
      adaptiveRevealViewExperiment transcriptGenerator] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold adaptiveRevealViewExperiment
  refine probEvent_bind_le_of_forall_le fun transcript _htranscript => ?_
  change Pr[RevealProbeView.HitsAvoidingReveals queries |
    (fun table : Index → Digest =>
      (⟨transcript.1, installReveals table transcript.1, transcript.2⟩ :
        RevealProbeView Index)) <$> ($ᵗ (Index → Digest))] ≤ _
  rw [probEvent_map]
  by_cases havoid : AvoidsReveals transcript.1 transcript.2
  · have hread : ∀ table : Index → Digest,
        readMany (installReveals table transcript.1) queries transcript.2 =
          readMany table queries transcript.2 := fun table =>
      readMany_installReveals_eq table transcript.1 queries transcript.2 havoid
    calc
      Pr[fun table : Index → Digest =>
          RevealProbeView.HitsAvoidingReveals queries
            ⟨transcript.1, installReveals table transcript.1, transcript.2⟩ |
        $ᵗ (Index → Digest)] =
          Pr[fun table : Index → Digest =>
            readMany table queries transcript.2 = true |
          $ᵗ (Index → Digest)] := by
        apply probEvent_congr' (fun table _ => ?_) rfl
        simp only [RevealProbeView.HitsAvoidingReveals, havoid, and_true]
        rw [hread table]
      _ = Pr[(fun hit : Bool => hit = true) |
          experiment queries transcript.2] := by
        unfold experiment
        change Pr[fun table : Index → Digest =>
            readMany table queries transcript.2 = true |
          $ᵗ (Index → Digest)] =
          Pr[(fun hit : Bool => hit = true) |
            (fun table : Index → Digest => readMany table queries transcript.2) <$>
              ($ᵗ (Index → Digest))]
        rw [probEvent_map]
        rfl
      _ ≤ (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
        adaptive_guess_le queries transcript.2
  · have hzero :
        Pr[(RevealProbeView.HitsAvoidingReveals queries) ∘
            (fun table : Index → Digest =>
              (⟨transcript.1, installReveals table transcript.1, transcript.2⟩ :
                RevealProbeView Index)) |
          $ᵗ (Index → Digest)] = 0 := by
      apply probEvent_eq_zero
      intro table _htable hevent
      exact havoid hevent.2
    rw [hzero]
    exact bot_le

/-- A real experiment with the same view distribution as the ideal reveal experiment inherits the hidden-table bound. -/
theorem reveal_view_coupling_hit_le
    (real : ProbComp (RevealProbeView Index))
    (transcriptGenerator : ProbComp
      (List (Index × Digest) × (List Bool → Index × Digest)))
    (queries : Nat)
    (hdist : 𝒟[real] = 𝒟[adaptiveRevealViewExperiment transcriptGenerator]) :
    Pr[RevealProbeView.HitsAvoidingReveals queries | real] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (adaptive_reveal_view_hit_le transcriptGenerator queries)

end XmssSecurity.IndexedHiddenValue
