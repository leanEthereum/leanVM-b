import SphincsSecurity.Proof.Sampling
import SphincsSecurity.Proof.Honest

/-!
# Adaptive probes into a sampled secret table

A hash input names one structural coordinate and carries one candidate value. Up to the first
correct candidate, an adaptive strategy sees only misses. Its coordinate and candidate at every
such step are therefore fixed by the all-miss history, so a table with per-cell mass at most
`epsilon` is hit with probability at most `q * epsilon`. There is no union over table coordinates.
-/

namespace SphincsSecurity

open OracleComp ENNReal

variable {D R : Type} [DecidableEq R]

/-- Run at most `q` adaptive coordinate-and-value probes against one fixed table. -/
noncomputable def readTableMany (table : D → R) : Nat → (List Bool → D × R) → Bool
  | 0, _ => false
  | q + 1, strategy =>
      let probe := strategy []
      let hit := decide (table probe.1 = probe.2)
      hit || readTableMany table q (fun history => strategy (hit :: history))

/-- Before the first hit, the strategy follows its all-miss path. -/
theorem readTableMany_true_iff (table : D → R) (q : Nat)
    (strategy : List Bool → D × R) :
    readTableMany table q strategy = true ↔
      ∃ j < q,
        let probe := strategy (List.replicate j false)
        table probe.1 = probe.2 := by
  induction q generalizing strategy with
  | zero => simp [readTableMany]
  | succ q ih =>
      rw [readTableMany]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact ⟨0, Nat.succ_pos q, by simpa using h⟩
        · by_cases hhead : table (strategy []).1 = (strategy []).2
          · exact ⟨0, Nat.succ_pos q, by simpa using hhead⟩
          · rw [decide_eq_false (by simpa using hhead)] at h
            obtain ⟨j, hj, hprobe⟩ :=
              (ih (fun history => strategy (false :: history))).1 h
            exact ⟨j + 1, Nat.succ_lt_succ hj, by
              simpa [List.replicate_succ] using hprobe⟩
      · rintro ⟨j, hj, hprobe⟩
        cases j with
        | zero => left; simpa using hprobe
        | succ j =>
            by_cases hhead : table (strategy []).1 = (strategy []).2
            · exact Or.inl hhead
            · refine Or.inr ?_
              rw [decide_eq_false (by simpa using hhead)]
              exact (ih (fun history => strategy (false :: history))).2
                ⟨j, Nat.lt_of_succ_lt_succ hj, by
                  simpa [List.replicate_succ] using hprobe⟩

/-- Sample one table and probe it adaptively. -/
noncomputable def hiddenTableReadMany (tables : ProbComp (D → R)) (q : Nat)
    (strategy : List Bool → D × R) : ProbComp Bool :=
  tables >>= fun table => pure (readTableMany table q strategy)

/-- Adaptive table-cell first-fire bound. Each probe pays only for its chosen cell. -/
theorem probEvent_hiddenTableReadMany_le {tables : ProbComp (D → R)} {ε : ℝ≥0∞}
    (hε : ∀ coordinate candidate,
      Pr[fun table : D → R => table coordinate = candidate | tables] ≤ ε)
    (q : Nat) (strategy : List Bool → D × R) :
    Pr[fun hit : Bool => hit = true | hiddenTableReadMany tables q strategy] ≤
      (q : ℝ≥0∞) * ε := by
  rw [hiddenTableReadMany, probEvent_bind_eq_tsum]
  have hstep : ∀ table : D → R,
      Pr[= table | tables] *
          Pr[fun hit : Bool => hit = true |
            (pure (readTableMany table q strategy) : ProbComp Bool)] ≤
        ∑ j ∈ Finset.range q,
          let probe := strategy (List.replicate j false)
          if table probe.1 = probe.2 then Pr[= table | tables] else 0 := by
    intro table
    by_cases hhit : readTableMany table q strategy = true
    · rw [probEvent_pure]
      simp only [hhit, if_true, mul_one]
      obtain ⟨j, hj, hprobe⟩ := (readTableMany_true_iff table q strategy).1 hhit
      calc
        Pr[= table | tables] =
            (let probe := strategy (List.replicate j false)
              if table probe.1 = probe.2 then Pr[= table | tables] else 0) := by
                simp only
                rw [if_pos hprobe]
        _ ≤ ∑ j ∈ Finset.range q,
              let probe := strategy (List.replicate j false)
              if table probe.1 = probe.2 then Pr[= table | tables] else 0 :=
            Finset.single_le_sum
              (f := fun j =>
                let probe := strategy (List.replicate j false)
                if table probe.1 = probe.2 then Pr[= table | tables] else 0)
              (fun _ _ => by positivity) (Finset.mem_range.2 hj)
    · rw [probEvent_pure, if_neg hhit, mul_zero]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc
    ∑ j ∈ Finset.range q, ∑' table : D → R,
        (let probe := strategy (List.replicate j false)
          if table probe.1 = probe.2 then Pr[= table | tables] else 0) ≤
        ∑ j ∈ Finset.range q, ε := by
      refine Finset.sum_le_sum fun j _ => ?_
      let probe := strategy (List.replicate j false)
      rw [show (∑' table : D → R,
          if table probe.1 = probe.2 then Pr[= table | tables] else 0) =
          Pr[fun table : D → R => table probe.1 = probe.2 | tables] by
            rw [probEvent_eq_tsum_ite]]
      exact hε probe.1 probe.2
    _ = (q : ℝ≥0∞) * ε := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

structure TableCoordinate3 (I J K : Type) where
  first : I
  second : J
  third : K

noncomputable def uncurriedTable3 {I J K R : Type} (table : I → J → K → R) :
    TableCoordinate3 I J K → R :=
  fun coordinate => table coordinate.first coordinate.second coordinate.third

noncomputable local instance {T : Type} [Fintype T] [Nonempty T] : SampleableType T :=
  SampleableType.ofFintype T

/-- Uniform curried function tables have the required per-cell marginal. -/
theorem probEvent_uniformCurriedTable3ReadMany_le {I J K R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Nat) (strategy : List Bool → TableCoordinate3 I J K × R) :
    Pr[fun hit : Bool => hit = true |
        hiddenTableReadMany
          (uncurriedTable3 <$> ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R)))
          q strategy] ≤
      (q : ℝ≥0∞) * ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_hiddenTableReadMany_le
  intro coordinate candidate
  rw [probEvent_map]
  exact le_of_eq (uniform_function_coordinate3_probability coordinate.first coordinate.second
    coordinate.third candidate)

namespace Concrete

structure FtsSecretProbe where
  index : Index
  tree : FtsTree
  leafIdx : FtsLeaf
  candidate : Digest
deriving DecidableEq

def FtsSecretProbe.coordinate (probe : FtsSecretProbe) :
    TableCoordinate3 Index FtsTree FtsLeaf :=
  ⟨probe.index, probe.tree, probe.leafIdx⟩

def FtsSecretProbe.input (parameter : PublicParameter) (probe : FtsSecretProbe) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf probe.index probe.tree probe.leafIdx)
    (digestBytes probe.candidate)

def FtsSecretProbe.Hits
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : FtsSecretProbe) : Prop :=
  ftsSecret probe.index probe.tree probe.leafIdx = probe.candidate

theorem FtsSecretProbe.input_injective (parameter : PublicParameter) :
    Function.Injective (FtsSecretProbe.input parameter) := by
  intro left right heq
  have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
  have hdomain : left.index = right.index ∧ left.tree = right.tree ∧
      left.leafIdx = right.leafIdx := by
    simpa only [HashDomain.ftsLeaf.injEq] using hparts.1
  have hcandidate : left.candidate = right.candidate := digestBytes_injective hparts.2
  cases left
  cases right
  simp only [FtsSecretProbe.mk.injEq] at hdomain hcandidate ⊢
  exact ⟨hdomain.1, hdomain.2.1, hdomain.2.2, hcandidate⟩

theorem FtsSecretProbe.input_eq_honestInput_iff
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : FtsSecretProbe) :
    probe.input parameter =
        honestInput f parameter otsSecret ftsSecret
          (.ftsLeaf probe.index probe.tree probe.leafIdx) ↔
      probe.Hits ftsSecret := by
  constructor
  · intro heq
    have hpayload :=
      (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
    exact (digestBytes_injective hpayload).symm
  · intro hhit
    simp only [FtsSecretProbe.input, honestInput, honestPayload, Position.domain]
    rw [hhit]

structure OtsValueProbe where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  chainIdx : ChainIndex
  digit : Digit
  candidate : Digest
deriving DecidableEq

def OtsValueProbe.target (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (probe : OtsValueProbe) : Digest :=
  honestChain f parameter probe.lay probe.tree probe.leafIdx probe.chainIdx
    (otsSecret probe.lay probe.tree probe.leafIdx probe.chainIdx) probe.digit.val

def OtsValueProbe.Hits (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (probe : OtsValueProbe) : Prop :=
  probe.candidate = probe.target f parameter otsSecret

theorem OtsValueProbe.target_zero {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {probe : OtsValueProbe} (hzero : probe.digit.val = 0) :
    probe.target f parameter otsSecret =
      otsSecret probe.lay probe.tree probe.leafIdx probe.chainIdx := by
  simp only [OtsValueProbe.target, hzero, honestChain_zero]

theorem OtsValueProbe.target_succ {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {probe : OtsValueProbe} {step : ChainStep} (hdigit : probe.digit.val = step.val + 1) :
    probe.target f parameter otsSecret =
      honestValue f parameter otsSecret (fun _ _ _ => 0)
        (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx step) := by
  rw [OtsValueProbe.target, honestValue_chain, hdigit]

end Concrete

end SphincsSecurity
