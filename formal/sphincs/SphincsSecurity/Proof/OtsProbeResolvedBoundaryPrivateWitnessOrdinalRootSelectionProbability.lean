import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionHidden

/-!
# Comparison-root prefix probability

An independent comparison root hits a list of at most `q` earlier candidates with probability at
most `q / 2^128`, even after gating on an arbitrary event from the candidate-producing run. A
small absorption lemma turns the resulting self-weighted exceptional branch into a factor two.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp ENNReal

set_option maxRecDepth 100000

theorem probEvent_uniformDigest_mem_list_le (values : List Digest) :
    Pr[fun root : Digest => root ∈ values | ($ᵗ Digest : ProbComp Digest)] ≤
      (values.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      calc
        _ = Pr[fun root : Digest => root = head ∨ root ∈ tail |
            ($ᵗ Digest : ProbComp Digest)] := by
          apply OracleComp.probEvent_congr' (fun root _ => by simp [eq_comm]) rfl
        _ ≤ Pr[fun root : Digest => root = head | ($ᵗ Digest : ProbComp Digest)] +
            Pr[fun root : Digest => root ∈ tail | ($ᵗ Digest : ProbComp Digest)] :=
          probEvent_or_le _ _ _
        _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
            (tail.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          apply add_le_add
          · rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]
            rw [show Fintype.card Digest = 2 ^ digestBits by simp]
          · exact ih
        _ = ((head :: tail).length : ℝ≥0∞) *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          rw [show (((head :: tail).length : Nat) : ℝ≥0∞) =
            1 + (tail.length : ℝ≥0∞) by simp [add_comm]]
          rw [add_mul, one_mul]

theorem probEvent_gate_and_uniformDigest_mem_list_le
    (run : ProbComp α) (gate : α → Prop) (values : α → List Digest) (q : Nat)
    (hlength : ∀ result ∈ support run, gate result → (values result).length ≤ q) :
    Pr[fun result : α × Digest =>
        gate result.1 ∧ result.2 ∈ values result.1 | do
      let result ← run
      let root ← ($ᵗ Digest : ProbComp Digest)
      pure (result, root)] ≤
      Pr[gate | run] *
        ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  apply SphincsSecurity.probEvent_bind_le_gated_mul
      (firstComp := run) (gate := gate)
  · intro result _hresult hgate
    rw [show (do
        let root ← ($ᵗ Digest : ProbComp Digest)
        pure (result, root)) =
      (fun root => (result, root)) <$> ($ᵗ Digest : ProbComp Digest) by
        simp [map_eq_bind_pure_comp], probEvent_map]
    simp [hgate]
  · intro result hresult hgate
    rw [show (do
        let root ← ($ᵗ Digest : ProbComp Digest)
        pure (result, root)) =
      (fun root => (result, root)) <$> ($ᵗ Digest : ProbComp Digest) by
        simp [map_eq_bind_pure_comp], probEvent_map]
    change Pr[fun root : Digest => gate result ∧ root ∈ values result |
      ($ᵗ Digest : ProbComp Digest)] ≤ _
    simp only [hgate, true_and]
    calc
      _ ≤ ((values result).length : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
        probEvent_uniformDigest_mem_list_le (values result)
      _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast hlength result hresult hgate

theorem le_two_mul_of_le_add_mul_inv_two
    (probability epsilon : ℝ≥0∞)
    (hprobability : probability ≤ 1) (hepsilon : epsilon ≠ ∞)
    (hbound : probability ≤ epsilon + probability * (2 : ℝ≥0∞)⁻¹) :
    probability ≤ 2 * epsilon := by
  have hprobabilityFinite : probability ≠ ∞ := by
    exact ne_top_of_le_ne_top (by norm_num) hprobability
  have hhalfFinite : probability * (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by finiteness
  have hsumFinite : epsilon + probability * (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by finiteness
  have hrightFinite : (2 : ℝ≥0∞) * epsilon ≠ ∞ := by finiteness
  have hreal : probability.toReal ≤
      epsilon.toReal + probability.toReal * (2 : ℝ)⁻¹ := by
    have := (ENNReal.toReal_le_toReal hprobabilityFinite hsumFinite).mpr hbound
    simpa [ENNReal.toReal_add hepsilon hhalfFinite, ENNReal.toReal_mul,
      ENNReal.toReal_inv] using this
  apply (ENNReal.toReal_le_toReal hprobabilityFinite hrightFinite).mp
  rw [ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  linarith

end SphincsSecurity.Concrete.OtsProbeSimulation
