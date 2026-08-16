import XmssSecurity.CappedEncodingRejection

open OracleComp ENNReal

namespace XmssSecurity.CappedEncodingMonitor

set_option maxRecDepth 100000

noncomputable def State.pendingRisk
    (state : EncodingMonitor.State) : ℝ≥0∞ :=
  (state.pendingCount : ℝ≥0∞) *
    (TargetSum.validDigests.card : ℝ≥0∞)⁻¹

theorem State.pendingRisk_empty :
    State.pendingRisk EncodingMonitor.State.empty = 0 := by
  unfold State.pendingRisk
  rw [EncodingMonitor.State.pendingCount_empty, Nat.cast_zero, zero_mul]

theorem State.pendingRisk_install_add
    (state : EncodingMonitor.State) (epoch : Epoch) (digest : Digest) :
    State.pendingRisk (state.install epoch digest) +
        (state.pending epoch).card *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ =
      State.pendingRisk state := by
  unfold State.pendingRisk
  rw [← add_mul, ← Nat.cast_add,
    EncodingMonitor.State.pendingCount_install_add]

theorem State.pendingRisk_addPending_le
    (state : EncodingMonitor.State) (epoch : Epoch) (digest : Digest) :
    State.pendingRisk (state.addPending epoch digest) ≤
      State.pendingRisk state +
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
  unfold State.pendingRisk
  calc
    ((state.addPending epoch digest).pendingCount : ℝ≥0∞) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ ≤
      ((state.pendingCount + 1 : Nat) : ℝ≥0∞) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast state.pendingCount_addPending_le epoch digest
    _ = (state.pendingCount : ℝ≥0∞) *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ +
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
          push_cast
          rw [add_mul, one_mul]

theorem uniformDigest_if_eq_probability_le
    (target : Digest) (resume : Digest → ProbComp Bool) (ε : ℝ≥0∞)
    (hresume : ∀ digest, digest ≠ target →
      Pr[(· = true) | resume digest] ≤ ε) :
    Pr[(· = true) | do
      let digest ← $ᵗ Digest
      if digest = target then pure true else resume digest] ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ + ε := by
  refine (probEvent_bind_le_probEvent_add
    (p := fun digest : Digest => digest = target) (ε := ε) ?_).trans ?_
  · intro digest _hdigest hmiss
    simpa [hmiss] using hresume digest hmiss
  · rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem uniformDigest_valid_bonus_sum_eq :
    ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          (if TargetSum.ValidDigest digest then
            (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [probOutput_uniformSample]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  change (TargetSum.validDigests.card : ℝ≥0∞) *
      ((Fintype.card Digest : ℝ≥0∞)⁻¹ *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) = _
  calc
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        ((TargetSum.validDigests.card : ℝ≥0∞) *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ * 1 := by
      rw [ENNReal.mul_inv_cancel]
      · exact_mod_cast Nat.ne_of_gt TargetSum.validDigests_card_pos
      · exact ENNReal.natCast_ne_top _
    _ = _ := mul_one _

noncomputable def applyUniformQueryMonitor
    (epoch : Epoch)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool := do
  let digest ← $ᵗ Digest
  match state.signed epoch with
  | some target =>
      if digest = target then pure true else resume digest state
  | none =>
      if TargetSum.ValidDigest digest then
        resume digest (state.addPending epoch digest)
      else resume digest state

theorem applyUniformQueryMonitor_true_probability_le
    (epoch : Epoch)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ digest nextState,
      Pr[(· = true) | resume digest nextState] ≤
        (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk nextState) :
    Pr[(· = true) | applyUniformQueryMonitor epoch resume state] ≤
      (fuel.succ : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        State.pendingRisk state := by
  cases hsigned : state.signed epoch with
  | some target =>
      unfold applyUniformQueryMonitor
      rw [hsigned]
      refine (uniformDigest_if_eq_probability_le target
        (fun digest => resume digest state)
        ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk state) ?_).trans_eq ?_
      · intro digest _hne
        exact hresume digest state
      · rw [Nat.cast_succ, add_mul, one_mul]
        ac_rfl
  | none =>
      unfold applyUniformQueryMonitor
      rw [hsigned, probEvent_bind_eq_tsum, tsum_fintype]
      calc
        ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              Pr[(· = true) |
                if TargetSum.ValidDigest digest then
                  resume digest (state.addPending epoch digest)
                else resume digest state] ≤
          ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                State.pendingRisk state +
                if TargetSum.ValidDigest digest then
                  (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
                    apply Finset.sum_le_sum
                    intro digest _hdigest
                    apply mul_le_mul_right
                    by_cases hvalid : TargetSum.ValidDigest digest
                    · simp only [hvalid, ↓reduceIte]
                      calc
                        Pr[(· = true) |
                            resume digest (state.addPending epoch digest)] ≤
                          (fuel : ℝ≥0∞) *
                              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                            State.pendingRisk (state.addPending epoch digest) :=
                              hresume digest (state.addPending epoch digest)
                        _ ≤ (fuel : ℝ≥0∞) *
                              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                            (State.pendingRisk state +
                              (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by
                                gcongr
                                exact State.pendingRisk_addPending_le state epoch digest
                        _ = _ := by ac_rfl
                    · simpa only [hvalid, ↓reduceIte, add_zero] using
                        hresume digest state
        _ = ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
              State.pendingRisk state) +
            (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.sum_mul, ← Finset.sum_mul]
              have hmass : ∑ digest : Digest, Pr[= digest | $ᵗ Digest] = 1 :=
                sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp)
              rw [hmass, one_mul, uniformDigest_valid_bonus_sum_eq, one_mul]
        _ = (fuel.succ : ℝ≥0∞) *
              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
            State.pendingRisk state := by
              rw [Nat.cast_succ, add_mul, one_mul]
              ac_rfl

noncomputable def applyBoundedSignMonitor
    (attempts : Nat) (epoch : Epoch)
    (resume : Option Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool :=
  match state.signed epoch with
  | some _ => pure false
  | none => do
      let accepted ← TargetSum.boundedValidDigest attempts
      match accepted with
      | none => resume none (state.install epoch 0)
      | some digest =>
          if digest ∈ state.pending epoch then pure true
          else resume (some digest) (state.install epoch digest)

theorem applyBoundedSignMonitor_true_probability_le
    (attempts : Nat) (epoch : Epoch)
    (resume : Option Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ result nextState,
      Pr[(· = true) | resume result nextState] ≤
        (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk nextState) :
    Pr[(· = true) | applyBoundedSignMonitor attempts epoch resume state] ≤
      (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        State.pendingRisk state := by
  cases hsigned : state.signed epoch with
  | some target =>
      unfold applyBoundedSignMonitor
      rw [hsigned, probEvent_pure]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact zero_le
  | none =>
      unfold applyBoundedSignMonitor
      rw [hsigned]
      refine (probEvent_bind_le_probEvent_add
        (p := fun accepted : Option Digest =>
          ∃ digest ∈ state.pending epoch, accepted = some digest)
        (ε := (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk (state.install epoch 0)) ?_).trans ?_
      · intro accepted _haccepted hmiss
        cases accepted with
        | none => exact hresume none (state.install epoch 0)
        | some digest =>
            by_cases hmem : digest ∈ state.pending epoch
            · exact (hmiss ⟨digest, hmem, rfl⟩).elim
            · have hrisk : State.pendingRisk (state.install epoch digest) =
                  State.pendingRisk (state.install epoch 0) := by
                unfold State.pendingRisk
                rw [EncodingMonitor.State.pendingCount_install_eq state epoch digest 0]
              simp only [hmem, ↓reduceIte]
              calc
                _ ≤ (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                    State.pendingRisk (state.install epoch digest) :=
                  hresume (some digest) (state.install epoch digest)
                _ = _ := by rw [hrisk]
      · calc
          Pr[fun accepted : Option Digest =>
              ∃ digest ∈ state.pending epoch, accepted = some digest |
              TargetSum.boundedValidDigest attempts] +
                ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                  State.pendingRisk (state.install epoch 0)) ≤
            ((state.pending epoch).card : ℝ≥0∞) *
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ +
              ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                State.pendingRisk (state.install epoch 0)) := by
                  gcongr
                  exact TargetSum.boundedValidDigest_hits_finset_le_inv_valid_card
                    attempts (state.pending epoch)
          _ = (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
              State.pendingRisk state := by
                calc
                  _ = (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                      (State.pendingRisk (state.install epoch 0) +
                        ((state.pending epoch).card : ℝ≥0∞) *
                          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by ac_rfl
                  _ = _ := by rw [State.pendingRisk_install_add]

inductive Action where
  | query (epoch : Epoch)
  | sign (epoch : Epoch)

abbrev Spec : OracleSpec Action :=
  Action →ₒ Option Digest

def IsQueryAction : Action → Prop
  | .query _ => True
  | .sign _ => False

noncomputable instance : DecidablePred IsQueryAction :=
  Classical.decPred _

noncomputable def runStructural
    (attempts : Nat) (state : EncodingMonitor.State)
    (computation : OracleComp Spec α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => EncodingMonitor.State → ProbComp Bool)
    (fun _result _state => pure false)
    (fun input _next recursivelyMonitor state =>
      match input with
      | .query epoch =>
          applyUniformQueryMonitor epoch
            (fun digest nextState =>
              recursivelyMonitor (some digest) nextState) state
      | .sign epoch =>
          applyBoundedSignMonitor attempts epoch recursivelyMonitor state)
    computation state

theorem runStructural_true_probability_le
    (attempts : Nat) (state : EncodingMonitor.State)
    (computation : OracleComp Spec α) (queryBound : Nat)
    (hbound : computation.IsQueryBoundP IsQueryAction queryBound) :
    Pr[(· = true) | runStructural attempts state computation] ≤
      (queryBound : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        State.pendingRisk state := by
  induction computation using OracleComp.inductionOn generalizing state queryBound with
  | pure result =>
      rw [runStructural, OracleComp.construct_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | query epoch =>
          cases queryBound with
          | zero => simp [IsQueryAction] at hbound
          | succ queryBound =>
              rw [runStructural, OracleComp.construct_query_bind]
              exact applyUniformQueryMonitor_true_probability_le epoch
                (fun digest nextState =>
                  runStructural attempts nextState (next (some digest)))
                state queryBound
                (fun digest nextState => ih (some digest) nextState queryBound
                  (by simpa [IsQueryAction] using hbound.2 (some digest)))
      | sign epoch =>
          rw [runStructural, OracleComp.construct_query_bind]
          exact applyBoundedSignMonitor_true_probability_le attempts epoch
            (fun result nextState =>
              runStructural attempts nextState (next result))
            state queryBound
            (fun result nextState => ih result nextState queryBound
              (by simpa [IsQueryAction] using hbound.2 result))

theorem runStructural_empty_true_probability_le
    (attempts : Nat) (computation : OracleComp Spec α) (queryBound : Nat)
    (hbound : computation.IsQueryBoundP IsQueryAction queryBound) :
    Pr[(· = true) |
      runStructural attempts EncodingMonitor.State.empty computation] ≤
      (queryBound : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [State.pendingRisk_empty, add_zero] using
    runStructural_true_probability_le attempts EncodingMonitor.State.empty
      computation queryBound hbound

end XmssSecurity.CappedEncodingMonitor
