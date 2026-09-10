import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSampledGuessRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

def ChainStartHistoryHit (context : DeferredContext) (history : List Probe)
    (base : OtsSecretIndex → HashOutput) : Prop :=
  ∃ candidate ∈ history, context.state.values candidate.coordinate = none ∧
    ChainStartEntryHit base (candidate.coordinate, candidate.candidate)

theorem probEvent_chainStartHistoryHit_le (context : DeferredContext) (history : List Probe) :
    Pr[ChainStartHistoryHit context history | sampleOtsHashTable] ≤
      (history.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ = Pr[fun base => ∃ candidate ∈ history.toFinset,
        context.state.values candidate.coordinate = none ∧
          ChainStartEntryHit base (candidate.coordinate, candidate.candidate) | sampleOtsHashTable] := by
      unfold ChainStartHistoryHit
      simp only [List.mem_toFinset]
    _ ≤ ∑ candidate ∈ history.toFinset, Pr[fun base =>
        context.state.values candidate.coordinate = none ∧
          ChainStartEntryHit base (candidate.coordinate, candidate.candidate) | sampleOtsHashTable] :=
      probEvent_exists_finset_le_sum history.toFinset sampleOtsHashTable _
    _ ≤ ∑ _candidate ∈ history.toFinset, ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro candidate _hcandidate
      apply le_trans (probEvent_mono (fun _ _ hhit => hhit.2))
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          exact probEvent_sampleOtsHashTable_cell_truncate_eq ⟨lay, tree, leafIdx, chainIdx⟩ digest
      | position position => simp [ChainStartEntryHit]
    _ = (history.toFinset.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_left (Nat.cast_le.mpr (List.toFinset_card_le history)) _

theorem probEvent_no_chainStartHistoryHit_ge_three_quarters
    (context : DeferredContext) (history : List Probe) (hlength : history.length ≤ 2 ^ 126) :
    (3 / 4 : ℝ≥0∞) ≤ Pr[fun base => ¬ChainStartHistoryHit context history base | sampleOtsHashTable] := by
  have hquarter : Pr[ChainStartHistoryHit context history | sampleOtsHashTable] ≤ (1 / 4 : ℝ≥0∞) := by
    apply (probEvent_chainStartHistoryHit_le context history).trans
    calc
      _ ≤ ((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
        mul_le_mul_left (Nat.cast_le.mpr hlength) _
      _ = _ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]
  have hdouble : Pr[fun base => ¬¬ChainStartHistoryHit context history base | sampleOtsHashTable] ≤
      (1 / 4 : ℝ≥0∞) := by simpa only [not_not] using hquarter
  have hgood := probEvent_one_sub_le_of_compl_le (by simp : Pr[⊥ | sampleOtsHashTable] = 0) hdouble
  have hsum : (1 : ℝ≥0∞) ≤
      Pr[fun base => ¬ChainStartHistoryHit context history base | sampleOtsHashTable] + 1 / 4 :=
    tsub_le_iff_right.mp hgood
  have hreal := (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, by finiteness⟩)).mpr hsum
  apply (ENNReal.toReal_le_toReal (by finiteness) probEvent_ne_top).mp
  rw [ENNReal.toReal_add probEvent_ne_top (by finiteness)] at hreal
  norm_num [ENNReal.toReal_div] at hreal ⊢
  linarith

theorem no_missingChainStartHit_of_history_clean
    (context : DeferredContext) (history : List Probe) (base : OtsSecretIndex → HashOutput)
    (hcovered : PendingCoveredBy history context) (hclean : ¬ChainStartHistoryHit context history base) :
    ¬MissingChainStartHit (completedStartTable context.state base) context := by
  rintro ⟨index, hmissing, hhit⟩
  have hlookup : completedStartTable context.state base index = base index := by
    simp [completedStartTable, hmissing]
  have hpending : (index.coordinate, truncateHash (base index)) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    simpa only [hlookup, LazyRevealProbe.State.hitAt] using hhit
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered _ hpending
  apply hclean
  refine ⟨candidate, hcandidate, by rwa [hcoordinate], ?_⟩
  rw [hcoordinate, hdigest]
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  rfl

theorem expected_history_guarded_chainStart_allowance_le_four_thirds
    (context : DeferredContext) (history : List Probe) (hlength : history.length ≤ 2 ^ 126)
    (index : OtsSecretIndex) (digest : Digest) (hmissing : context.state.values index.coordinate = none) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      if ¬ChainStartHistoryHit context history base then
        candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩)
      else 0) ≤
      ((unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * (4 / 3) *
      Pr[fun base => ¬ChainStartHistoryHit context history base | sampleOtsHashTable] := by
  let charge : ℝ≥0∞ :=
    (unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩) : ℝ≥0∞) *
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  calc
    _ ≤ ∑' base, Pr[= base | sampleOtsHashTable] *
        candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩) := by
      apply ENNReal.tsum_le_tsum
      intro base
      apply mul_le_mul_right
      split_ifs <;> first | exact le_rfl | exact bot_le
    _ ≤ charge := expected_candidateFailureAllowance_chainStart_of_missing context index digest hmissing
    _ = charge * (4 / 3) * (3 / 4) := by
      have hfactor : (4 / 3 : ℝ≥0∞) * (3 / 4) = 1 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      rw [mul_assoc, hfactor, mul_one]
    _ ≤ _ := mul_le_mul_right (probEvent_no_chainStartHistoryHit_ge_three_quarters context history hlength) _

end SphincsSecurity.Concrete.OtsProbeSimulation
