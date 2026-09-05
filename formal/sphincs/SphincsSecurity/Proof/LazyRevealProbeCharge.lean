import SphincsSecurity.Proof.LazyRevealProbePending
import SphincsSecurity.Proof.AdaptiveRevealProbeCharge

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

def pendingProbeCharge (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) : Nat :=
  if state.values coordinate ≠ none then 0
  else if (coordinate, candidate) ∈ state.pending then 0 else 1

theorem pendingProbeCharge_le_one (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) :
    pendingProbeCharge state coordinate candidate ≤ 1 := by
  unfold pendingProbeCharge
  split_ifs <;> omega

theorem pendingProbeCharge_eq_zero_of_materialized (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) (hvalue : state.values coordinate ≠ none) :
    pendingProbeCharge state coordinate candidate = 0 := by
  simp only [pendingProbeCharge, if_pos hvalue]

theorem State.unmaterializedPending_card_addPending_eq_charge (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    (state.addPending coordinate candidate).unmaterializedPending.card =
      state.unmaterializedPending.card + pendingProbeCharge state coordinate candidate := by
  by_cases hvalue : state.values coordinate = none
  · have hset : (state.addPending coordinate candidate).unmaterializedPending =
        insert (coordinate, candidate) state.unmaterializedPending := by
      simp [unmaterializedPending, addPending, Finset.filter_insert, hvalue]
    rw [hset]
    by_cases hmem : (coordinate, candidate) ∈ state.pending
    · have hfresh : (coordinate, candidate) ∈ state.unmaterializedPending := by
        simp [unmaterializedPending, hmem, hvalue]
      simp [Finset.insert_eq_of_mem hfresh, pendingProbeCharge, hvalue, hmem]
    · have hfresh : (coordinate, candidate) ∉ state.unmaterializedPending := by
        simp [unmaterializedPending, hmem]
      simp [Finset.card_insert_of_notMem hfresh, pendingProbeCharge, hvalue, hmem]
  · have hset : (state.addPending coordinate candidate).unmaterializedPending = state.unmaterializedPending := by
      simp [unmaterializedPending, addPending, Finset.filter_insert, hvalue]
    rw [hset, pendingProbeCharge_eq_zero_of_materialized state coordinate candidate hvalue, Nat.add_zero]

noncomputable def expectedProbeCharge {α : Type}
    (computation : OracleComp (World Coordinate) α) : State Coordinate → Nat → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ _ => 0)
    (fun input _ next state fuel =>
      match input with
      | .uniform n => ∑' output, Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] * next output state fuel
      | .hashOutput => ∑' output, Pr[= output | sampleHashOutput] * next output state fuel
      | .ensure coordinate => next () (state.ensure coordinate) fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => 0
          | remaining + 1 =>
              if coordinate ∈ state.revealed then next () state remaining
              else (pendingProbeCharge state coordinate candidate : ℝ≥0∞) +
                next () (state.addPending coordinate candidate) remaining
      | .peek coordinate => next (state.values coordinate) state fuel
      | .publish coordinate => next () (state.publish coordinate) fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => next output state fuel
          | none => ∑' output, Pr[= output | sampleHashOutput] *
              if state.hitAt coordinate output then 0
              else next output (state.materialize coordinate output) fuel)
    computation

theorem expectedProbeCharge_query_bind {α : Type}
    (input : (World Coordinate).Domain)
    (next : (World Coordinate).Range input → OracleComp (World Coordinate) α)
    (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge ((liftM (OracleSpec.query input) : OracleComp (World Coordinate) _) >>= next) state fuel =
      match input with
      | .uniform n => ∑' output, Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] *
          expectedProbeCharge (next output) state fuel
      | .hashOutput => ∑' output, Pr[= output | sampleHashOutput] * expectedProbeCharge (next output) state fuel
      | .ensure coordinate => expectedProbeCharge (next ()) (state.ensure coordinate) fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => 0
          | remaining + 1 =>
              if coordinate ∈ state.revealed then expectedProbeCharge (next ()) state remaining
              else (pendingProbeCharge state coordinate candidate : ℝ≥0∞) +
                expectedProbeCharge (next ()) (state.addPending coordinate candidate) remaining
      | .peek coordinate => expectedProbeCharge (next (state.values coordinate)) state fuel
      | .publish coordinate => expectedProbeCharge (next ()) (state.publish coordinate) fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => expectedProbeCharge (next output) state fuel
          | none => ∑' output, Pr[= output | sampleHashOutput] *
              if state.hitAt coordinate output then 0
              else expectedProbeCharge (next output) (state.materialize coordinate output) fuel := by
  cases input <;> rfl

theorem materialize_probability_le_charge (state : State Coordinate) (coordinate : Coordinate) (hvalue : state.values coordinate = none)
    (resume : HashOutput → State Coordinate → ProbComp Bool) (charge : HashOutput → ℝ≥0∞)
    (hresume : ∀ output,
      Pr[fun hit : Bool => hit = true | resume output (state.materialize coordinate output)] ≤
        (charge output + ((state.materialize coordinate output).unmaterializedPending.card : ℝ≥0∞)) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun hit : Bool => hit = true | do
      let output ← sampleHashOutput
      if state.hitAt coordinate output then pure true else resume output (state.materialize coordinate output)] ≤
      ((∑' output, Pr[= output | sampleHashOutput] *
          if state.hitAt coordinate output then 0 else charge output) + (state.unmaterializedPending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let eps := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  let remaining := (state.clearPending coordinate).unmaterializedPending.card
  calc
    _ ≤ ∑' output, Pr[= output | sampleHashOutput] *
        ((if state.hitAt coordinate output then 1 else 0) +
          (if state.hitAt coordinate output then 0 else charge output) * eps +
          (remaining : ℝ≥0∞) * eps) := by
      rw [probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      by_cases hhit : state.hitAt coordinate output
      · simp only [hhit, ↓reduceIte, probEvent_pure, zero_mul, add_zero]
        exact le_add_right le_rfl
      · simp only [hhit, ↓reduceIte, zero_add]
        exact (hresume output).trans_eq (by rw [state.unmaterializedPending_materialize, add_mul])
    _ = Pr[state.hitAt coordinate | sampleHashOutput] +
        (∑' output, Pr[= output | sampleHashOutput] *
          if state.hitAt coordinate output then 0 else charge output) * eps +
        (remaining : ℝ≥0∞) * eps := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
      congr 1
      · congr 1
        · rw [probEvent_eq_tsum_ite]
          apply tsum_congr
          intro output
          split_ifs <;> simp
        · simp_rw [← mul_assoc]
          rw [ENNReal.tsum_mul_right]
    _ ≤ ((state.pendingAt coordinate).card : ℝ≥0∞) * eps +
        (∑' output, Pr[= output | sampleHashOutput] *
          if state.hitAt coordinate output then 0 else charge output) * eps +
        (remaining : ℝ≥0∞) * eps :=
      add_le_add (add_le_add (probEvent_sampleHashOutput_hitAt_le state coordinate) le_rfl) le_rfl
    _ ≤ _ := by
      have hcard : ((state.pendingAt coordinate).card : ℝ≥0∞) + remaining ≤ state.unmaterializedPending.card := by
        exact_mod_cast (Nat.add_comm _ _ ▸ state.unmaterializedPending_card_split_le coordinate hvalue)
      calc
        _ = ((∑' output, Pr[= output | sampleHashOutput] *
            if state.hitAt coordinate output then 0 else charge output) +
              (((state.pendingAt coordinate).card : ℝ≥0∞) + remaining)) * eps := by ring
        _ ≤ _ := mul_le_mul' (add_le_add le_rfl hcard) le_rfl

set_option maxRecDepth 100000 in
theorem experiment_probability_le_expectedProbeCharge_unmaterialized {α : Type}
    (state : State Coordinate) (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun hit : Bool => hit = true | experiment state fuel computation] ≤
      (expectedProbeCharge computation state fuel + (state.unmaterializedPending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      change Pr[_ | finalize state] ≤ (0 + _) * _
      rw [zero_add]
      exact finalize_probability_le_unmaterializedPending state
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n =>
          rw [experiment_uniform_query_bind]
          exact AdaptiveRevealProbe.probEvent_bind_le_expectedCharge _ _ _ _ _ fun output => ih output state fuel
      | hashOutput =>
          rw [experiment_hashOutput_query_bind]
          exact AdaptiveRevealProbe.probEvent_bind_le_expectedCharge _ _ _ _ _ fun output => ih output state fuel
      | ensure coordinate =>
          rw [experiment_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [experiment_probe_query_bind]
          cases fuel with
          | zero => simpa only [zero_add] using finalize_probability_le_unmaterializedPending state
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                apply (ih () (state.addPending coordinate candidate) remaining).trans_eq
                rw [state.unmaterializedPending_card_addPending_eq_charge, Nat.cast_add]
                congr 1
                ac_rfl
      | peek coordinate =>
          rw [experiment_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [experiment_publish_query_bind]
          exact ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [experiment_reveal_query_bind]
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              exact materialize_probability_le_charge state coordinate hvalue
                (fun output nextState => experiment nextState fuel (next output)) _
                (fun output => ih output (state.materialize coordinate output) fuel)

theorem experiment_probability_le_expectedProbeCharge {α : Type}
    (state : State Coordinate) (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun hit : Bool => hit = true | experiment state fuel computation] ≤
      (expectedProbeCharge computation state fuel + (state.pending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  (experiment_probability_le_expectedProbeCharge_unmaterialized state fuel computation).trans
    (mul_le_mul' (add_le_add le_rfl (Nat.cast_le.mpr state.unmaterializedPending_card_le)) le_rfl)

theorem experiment_empty_probability_le_expectedProbeCharge {α : Type}
    (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun hit : Bool => hit = true | experiment (State.empty : State Coordinate) fuel computation] ≤
      expectedProbeCharge computation State.empty fuel * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa only [State.empty, Finset.card_empty, Nat.cast_zero, add_zero] using
    experiment_probability_le_expectedProbeCharge State.empty fuel computation

theorem expectedProbeCharge_le_fuel {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge computation state fuel ≤ fuel := by
  have havg {β : Type} (source : ProbComp β) (charge : β → ℝ≥0∞) (cap : ℝ≥0∞)
      (hcharge : ∀ value, charge value ≤ cap) :
      (∑' value, Pr[= value | source] * charge value) ≤ cap := by
    calc
      _ ≤ ∑' value, Pr[= value | source] * cap :=
        ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hcharge value)
      _ ≤ cap := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => exact bot_le
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n => exact havg _ _ _ fun output => ih output state fuel
      | hashOutput => exact havg _ _ _ fun output => ih output state fuel
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [Nat.cast_zero, le_refl]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact (ih () state remaining).trans (Nat.cast_le.mpr (Nat.le_succ remaining))
              · simp only [hrevealed, ↓reduceIte]
                calc
                  _ ≤ 1 + (remaining : ℝ≥0∞) :=
                    add_le_add (by exact_mod_cast pendingProbeCharge_le_one state coordinate candidate)
                      (ih () (state.addPending coordinate candidate) remaining)
                  _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_comm]
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              apply havg
              intro output
              split_ifs
              · exact bot_le
              · exact ih output (state.materialize coordinate output) fuel

theorem expectedProbeCharge_le_queryBound {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel bound : Nat)
    (hbound : computation.IsQueryBoundP IsProbe bound) : expectedProbeCharge computation state fuel ≤ bound := by
  have havg {β : Type} (source : ProbComp β) (charge : β → ℝ≥0∞) (cap : ℝ≥0∞)
      (hcharge : ∀ value, charge value ≤ cap) : (∑' value, Pr[= value | source] * charge value) ≤ cap := by
    apply le_trans (ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hcharge value))
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
  induction computation using OracleComp.inductionOn generalizing state fuel bound with
  | pure value => exact bot_le
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n => exact havg _ _ _ fun output => ih output state fuel bound (by simpa [IsProbe] using hbound.2 output)
      | hashOutput => exact havg _ _ _ fun output => ih output state fuel bound (by simpa [IsProbe] using hbound.2 output)
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel bound (by simpa [IsProbe] using hbound.2 ())
      | peek coordinate => exact ih (state.values coordinate) state fuel bound (by simpa [IsProbe] using hbound.2 _)
      | publish coordinate => exact ih () (state.publish coordinate) fuel bound (by simpa [IsProbe] using hbound.2 ())
      | probe coordinate candidate =>
          have hpositive : 0 < bound := by simpa [IsProbe] using hbound.1
          have hnext : (next ()).IsQueryBoundP IsProbe (bound - 1) := by simpa [IsProbe] using hbound.2 ()
          cases fuel with
          | zero => exact bot_le
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact (ih () state remaining (bound - 1) hnext).trans (Nat.cast_le.mpr (Nat.sub_le _ _))
              · simp only [hrevealed, ↓reduceIte]
                calc
                  _ ≤ (1 : ℝ≥0∞) + (bound - 1 : Nat) :=
                    add_le_add (by exact_mod_cast pendingProbeCharge_le_one state coordinate candidate)
                      (ih () (state.addPending coordinate candidate) remaining (bound - 1) hnext)
                  _ = _ := by
                    rw [← Nat.cast_one, ← Nat.cast_add]
                    congr 1
                    omega
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel bound (by simpa [IsProbe] using hbound.2 output)
          | none =>
              apply havg
              intro output
              split_ifs
              · exact bot_le
              · exact ih output (state.materialize coordinate output) fuel bound (by simpa [IsProbe] using hbound.2 output)

end SphincsSecurity.LazyRevealProbe
