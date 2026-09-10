import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbe

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

def pendingProbeCharge (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) : Nat :=
  if candidate ∈ state.pending coordinate then 0 else 1

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem pendingProbeCharge_le_one (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) :
    pendingProbeCharge state coordinate candidate ≤ 1 := by
  unfold pendingProbeCharge
  split_ifs <;> omega

omit [Fintype Coordinate] in
theorem State.addPending_eq_self_of_mem (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) (hmem : candidate ∈ state.pending coordinate) :
    state.addPending coordinate candidate = state := by
  unfold State.addPending
  rw [Finset.insert_eq_of_mem hmem, Function.update_eq_self]

theorem State.pendingCount_addPending_le_charge (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    (state.addPending coordinate candidate).pendingCount ≤
      state.pendingCount + pendingProbeCharge state coordinate candidate := by
  by_cases hmem : candidate ∈ state.pending coordinate
  · rw [state.addPending_eq_self_of_mem coordinate candidate hmem]
    simp only [pendingProbeCharge, if_pos hmem, Nat.add_zero, le_refl]
  · simpa only [pendingProbeCharge, if_neg hmem] using state.pendingCount_addPending_le coordinate candidate

noncomputable def expectedProbeCharge {α : Type}
    (computation : OracleComp (World Coordinate) α) : State Coordinate → Nat → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ _ => 0)
    (fun input _ next state fuel =>
      match input with
      | .uniform n => ∑' output, Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] *
          next output state fuel
      | .hashOutput => ∑' output, Pr[= output | sampleHashOutput] * next output state fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => 0
          | remaining + 1 =>
              match state.revealed coordinate with
              | some _ => next () state remaining
              | none => (pendingProbeCharge state coordinate candidate : ℝ≥0∞) +
                  next () (state.addPending coordinate candidate) remaining
      | .reveal coordinate =>
          match state.revealed coordinate with
          | some value => next value state fuel
          | none => ∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
              if value ∈ state.pending coordinate then 0
              else next value (state.install coordinate value) fuel)
    computation

omit [Fintype Coordinate] in
theorem expectedProbeCharge_query_bind {α : Type}
    (input : (World Coordinate).Domain)
    (next : (World Coordinate).Range input → OracleComp (World Coordinate) α)
    (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge ((liftM (OracleSpec.query input) : OracleComp (World Coordinate) _) >>= next) state fuel =
      match input with
      | .uniform n => ∑' output, Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] *
          expectedProbeCharge (next output) state fuel
      | .hashOutput => ∑' output, Pr[= output | sampleHashOutput] *
          expectedProbeCharge (next output) state fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => 0
          | remaining + 1 =>
              match state.revealed coordinate with
              | some _ => expectedProbeCharge (next ()) state remaining
              | none => (pendingProbeCharge state coordinate candidate : ℝ≥0∞) +
                  expectedProbeCharge (next ()) (state.addPending coordinate candidate) remaining
      | .reveal coordinate =>
          match state.revealed coordinate with
          | some value => expectedProbeCharge (next value) state fuel
          | none => ∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
              if value ∈ state.pending coordinate then 0
              else expectedProbeCharge (next value) (state.install coordinate value) fuel := by
  cases input <;> rfl

set_option maxRecDepth 100000 in
theorem applyReveal_probability_le_charge (state : State Coordinate) (coordinate : Coordinate)
    (resume : Digest → State Coordinate → ProbComp Bool) (charge : Digest → ℝ≥0∞)
    (hresume : ∀ value,
      Pr[fun hit : Bool => hit = true | resume value (state.install coordinate value)] ≤
        (charge value + ((state.install coordinate value).pendingCount : ℝ≥0∞)) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    Pr[fun hit : Bool => hit = true | applyReveal state coordinate resume] ≤
      ((∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
          if value ∈ state.pending coordinate then 0 else charge value) +
        (state.pendingCount : ℝ≥0∞)) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  let remaining := (state.install coordinate 0).pendingCount
  calc
    _ ≤ ∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
        ((if value ∈ state.pending coordinate then 1 else 0) +
          (if value ∈ state.pending coordinate then 0 else charge value) * eps +
          (remaining : ℝ≥0∞) * eps) := by
      rw [applyReveal, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro value
      simp only [probOutput_uniformSample]
      apply mul_le_mul' le_rfl
      by_cases hhit : value ∈ state.pending coordinate
      · simp only [hhit, ↓reduceIte, probEvent_pure, zero_mul, add_zero]
        exact le_add_right le_rfl
      · simp only [hhit, ↓reduceIte, zero_add]
        exact (hresume value).trans_eq (by rw [add_mul]; rfl)
    _ = Pr[fun value : Digest => value ∈ state.pending coordinate | ($ᵗ Digest : ProbComp Digest)] +
        (∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
          if value ∈ state.pending coordinate then 0 else charge value) * eps +
        (remaining : ℝ≥0∞) * eps := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
      congr 1
      · congr 1
        · rw [probEvent_eq_tsum_ite]
          apply tsum_congr
          intro value
          split_ifs <;> simp
        · simp_rw [← mul_assoc]
          rw [ENNReal.tsum_mul_right]
    _ ≤ ((state.pending coordinate).card : ℝ≥0∞) * eps +
        (∑' value, Pr[= value | ($ᵗ Digest : ProbComp Digest)] *
          if value ∈ state.pending coordinate then 0 else charge value) * eps +
        (remaining : ℝ≥0∞) * eps := by
      have hmem := uniformDigest_mem_finset_le (state.pending coordinate)
      change _ ≤ ((state.pending coordinate).card : ℝ≥0∞) * eps at hmem
      simp only [probEvent_eq_tsum_ite, probOutput_uniformSample] at hmem ⊢
      exact add_le_add_left (add_le_add_left hmem _) _
    _ = _ := by
      have hcount := state.pendingCount_install_add coordinate 0
      have hcast : (remaining : ℝ≥0∞) + ((state.pending coordinate).card : ℝ≥0∞) =
          (state.pendingCount : ℝ≥0∞) := by exact_mod_cast hcount
      rw [← hcast]
      ring

theorem probEvent_bind_le_expectedCharge {β : Type}
    (source : ProbComp β) (resume : β → ProbComp Bool)
    (charge : β → ℝ≥0∞) (pending eps : ℝ≥0∞)
    (hresume : ∀ value, Pr[fun hit : Bool => hit = true | resume value] ≤
      (charge value + pending) * eps) :
    Pr[fun hit : Bool => hit = true | source >>= resume] ≤
      ((∑' value, Pr[= value | source] * charge value) + pending) * eps := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | source] * ((charge value + pending) * eps) :=
      ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hresume value)
    _ = (∑' value, Pr[= value | source] * charge value) * eps +
        (∑' value, Pr[= value | source]) * (pending * eps) := by
      simp_rw [add_mul, mul_add, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
        ENNReal.tsum_mul_right, mul_assoc]
    _ ≤ (∑' value, Pr[= value | source] * charge value) * eps + pending * eps :=
      add_le_add le_rfl (mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one)
    _ = _ := (add_mul ..).symm

set_option maxRecDepth 100000 in
theorem experiment_probability_le_expectedProbeCharge {α : Type} [Nonempty Coordinate]
    (state : State Coordinate) (hvalid : state.Valid)
    (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun hit : Bool => hit = true | experiment state fuel computation] ≤
      (expectedProbeCharge computation state fuel + (state.pendingCount : ℝ≥0∞)) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      change Pr[fun hit : Bool => hit = true |
        (fun base : Coordinate → Digest => tableHits state (extendTable state base)) <$>
          sampleTable] ≤ (0 + _) * _
      rw [zero_add]
      exact finalize_probability_le state hvalid
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n =>
          have hdist :
              evalDist (experiment state fuel
                ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
                  OracleComp (World Coordinate) _) >>= next)) =
              evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                experiment state fuel (next output)) := by
            rw [experiment_uniform_query_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr' (oa' :=
            (liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
              experiment state fuel (next output)) (fun _ _ => Iff.rfl) hdist).le.trans ?_
          exact probEvent_bind_le_expectedCharge _ _ _ _ _ fun output =>
            ih output state hvalid fuel
      | hashOutput =>
          have hdist :
              evalDist (experiment state fuel
                ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
                  OracleComp (World Coordinate) HashOutput) >>= next)) =
              evalDist (sampleHashOutput >>= fun output =>
                experiment state fuel (next output)) := by
            rw [experiment_hashOutput_query_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr' (oa' :=
            sampleHashOutput >>= fun output =>
              experiment state fuel (next output)) (fun _ _ => Iff.rfl) hdist).le.trans ?_
          exact probEvent_bind_le_expectedCharge _ _ _ _ _ fun output =>
            ih output state hvalid fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              rw [experiment_probe_query_bind]
              change Pr[fun hit : Bool => hit = true |
                (fun base : Coordinate → Digest =>
                  tableHits state (extendTable state base)) <$> sampleTable] ≤ (0 + _) * _
              rw [zero_add]
              exact finalize_probability_le state hvalid
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  rw [experiment_probe_query_bind]
                  simp only [hrevealed]
                  exact ih () state hvalid remaining
              | none =>
                  rw [experiment_probe_query_bind]
                  simp only [hrevealed]
                  refine (ih () (state.addPending coordinate candidate)
                    (hvalid.addPending coordinate candidate hrevealed) remaining).trans ?_
                  apply mul_le_mul' _ le_rfl
                  calc
                    _ ≤ expectedProbeCharge (next ()) (state.addPending coordinate candidate) remaining +
                        ((state.pendingCount : ℝ≥0∞) + (pendingProbeCharge state coordinate candidate : ℝ≥0∞)) := by
                      apply add_le_add le_rfl
                      exact_mod_cast state.pendingCount_addPending_le_charge coordinate candidate
                    _ = _ := by ac_rfl
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value =>
              rw [experiment_reveal_query_bind]
              simp only [hrevealed]
              exact ih value state hvalid fuel
          | none =>
              let resume := fun value nextState => experiment nextState fuel (next value)
              have hdist :
                  evalDist (experiment state fuel
                    ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
                      OracleComp (World Coordinate) _) >>= next)) =
                  evalDist (applyReveal state coordinate resume) := by
                rw [experiment_reveal_query_bind]
                simp only [hrevealed]
                simpa [resume, experiment] using
                  evalDist_sample_applyReveal state coordinate hrevealed
                    fun table value nextState =>
                      run table nextState fuel (next value)
              refine (probEvent_congr' (oa' := applyReveal state coordinate resume)
                (fun _ _ => Iff.rfl) hdist).le.trans ?_
              simp only [hrevealed]
              exact applyReveal_probability_le_charge state coordinate resume _ fun value =>
                ih value (state.install coordinate value) (hvalid.install coordinate value) fuel

theorem experiment_empty_probability_le_expectedProbeCharge {α : Type} [Nonempty Coordinate]
    (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun hit : Bool => hit = true | experiment (State.empty : State Coordinate) fuel computation] ≤
      expectedProbeCharge computation State.empty fuel * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [State.pendingCount_empty, Nat.cast_zero, add_zero] using
    experiment_probability_le_expectedProbeCharge State.empty State.valid_empty fuel computation

omit [Fintype Coordinate] in
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
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [Nat.cast_zero, le_refl]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  simp only [hrevealed]
                  exact (ih () state remaining).trans (Nat.cast_le.mpr (Nat.le_succ remaining))
              | none =>
                  simp only [hrevealed]
                  calc
                    _ ≤ 1 + (remaining : ℝ≥0∞) :=
                      add_le_add (by exact_mod_cast pendingProbeCharge_le_one state coordinate candidate)
                        (ih () (state.addPending coordinate candidate) remaining)
                    _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_comm]
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value =>
              simp only [hrevealed]
              exact ih value state fuel
          | none =>
              simp only [hrevealed]
              apply havg
              intro value
              split_ifs
              · exact bot_le
              · exact ih value (state.install coordinate value) fuel

end SphincsSecurity.AdaptiveRevealProbe
