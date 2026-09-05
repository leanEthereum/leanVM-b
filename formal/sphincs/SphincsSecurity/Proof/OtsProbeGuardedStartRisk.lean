import SphincsSecurity.Proof.OtsProbeSampledGuessRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable

theorem probEvent_completedStartTable_not_completable_le
    (context : DeferredContext) (hvalid : context.Valid) (hprivate : ¬PrivateStructuralHit context)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    Pr[fun base => ¬DeferredCompletable (completedStartTable context.state base) context | sampleOtsHashTable] ≤
      (context.state.pending.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply le_trans ?_ (probEvent_missingChainStartHit_completedStartTable_le context)
  apply probEvent_mono
  intro base _hbase hnot
  exact Classical.byContradiction fun hmissing =>
    hnot (deferredCompletable_of_valid_of_no_boundary_hit _ context hvalid
      (startTableAgrees_completedStartTable context.state base) hprivate hmissing hcard)

theorem probEvent_completedStartTable_completable_ge_three_quarters
    (context : DeferredContext) (hvalid : context.Valid) (hprivate : ¬PrivateStructuralHit context)
    (hcard : context.state.pending.card ≤ 2 ^ 126) :
    (3 / 4 : ℝ≥0∞) ≤
      Pr[fun base => DeferredCompletable (completedStartTable context.state base) context | sampleOtsHashTable] := by
  have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
  have hbad := probEvent_completedStartTable_not_completable_le context hvalid hprivate (hcard.trans_lt hspace)
  have hquarter : Pr[fun base => ¬DeferredCompletable (completedStartTable context.state base) context |
      sampleOtsHashTable] ≤ (1 / 4 : ℝ≥0∞) := by
    apply hbad.trans
    calc
      _ ≤ ((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
        mul_le_mul_left (Nat.cast_le.mpr hcard) _
      _ = _ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]
  have hgood := probEvent_one_sub_le_of_compl_le (by simp : Pr[⊥ | sampleOtsHashTable] = 0) hquarter
  have hsum : (1 : ℝ≥0∞) ≤
      Pr[fun base => DeferredCompletable (completedStartTable context.state base) context | sampleOtsHashTable] + 1 / 4 :=
    tsub_le_iff_right.mp hgood
  have hreal := (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, by finiteness⟩)).mpr hsum
  apply (ENNReal.toReal_le_toReal (by finiteness) probEvent_ne_top).mp
  rw [ENNReal.toReal_add probEvent_ne_top (by finiteness)] at hreal
  norm_num [ENNReal.toReal_div] at hreal ⊢
  linarith

theorem expected_guarded_chainStart_allowance_le_four_thirds
    (context : DeferredContext) (index : OtsSecretIndex) (digest : Digest)
    (hmissing : context.state.values index.coordinate = none)
    (hvalid : context.Valid) (hprivate : ¬PrivateStructuralHit context)
    (hcard : context.state.pending.card ≤ 2 ^ 126) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      if DeferredCompletable (completedStartTable context.state base) context then
        candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩)
      else 0) ≤
      ((unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * (4 / 3) *
      Pr[fun base => DeferredCompletable (completedStartTable context.state base) context | sampleOtsHashTable] := by
  classical
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
    _ ≤ _ := mul_le_mul_right
      (probEvent_completedStartTable_completable_ge_three_quarters context hvalid hprivate hcard) _

end SphincsSecurity.Concrete.OtsProbeSimulation
