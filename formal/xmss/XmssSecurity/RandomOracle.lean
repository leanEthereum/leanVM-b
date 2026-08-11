import XmssSecurity.Scheme
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ hashOutputBits := by
  simp

private def joinDigest (high low : Digest) : HashOutput :=
  (high ++ low).cast hashOutputBits_eq.symm

private def highDigest (output : HashOutput) : Digest :=
  (splitHashOutput output).extractLsb' digestBits digestBits

private def digestFiberEquiv (target : Digest) :
    Digest ≃ {output : HashOutput // truncateHash output = target} where
  toFun high := ⟨joinDigest high target, by
    change BitVec.extractLsb' 0 digestBits (high ++ target) = target
    exact BitVec.extractLsb'_append_eq_right⟩
  invFun output := highDigest output.val
  left_inv high := by
    change BitVec.extractLsb' digestBits digestBits (high ++ target) = high
    exact BitVec.extractLsb'_append_eq_left
  right_inv output := by
    apply Subtype.ext
    calc
      joinDigest (highDigest output.val) target =
          joinDigest (highDigest output.val) (truncateHash output.val) := by
        rw [output.property]
      _ = (splitHashOutput output.val).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output.val))
      _ = output.val := by simp [splitHashOutput]

/-- A 256-bit random-oracle answer is equivalently an independent high half and the 128-bit digest used by XMSS. -/
def hashOutputEquivDigestPair : HashOutput ≃ Digest × Digest where
  toFun output := (highDigest output, truncateHash output)
  invFun halves := joinDigest halves.1 halves.2
  left_inv output := by
    calc
      joinDigest (highDigest output) (truncateHash output) =
          (splitHashOutput output).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output))
      _ = output := by simp [splitHashOutput]
  right_inv halves := by
    apply Prod.ext
    · change BitVec.extractLsb' digestBits digestBits (halves.1 ++ halves.2) = halves.1
      exact BitVec.extractLsb'_append_eq_left
    · change BitVec.extractLsb' 0 digestBits (halves.1 ++ halves.2) = halves.2
      exact BitVec.extractLsb'_append_eq_right

noncomputable def independentDigestHalves : ProbComp (Digest × Digest) := do
  let high ← $ᵗ Digest
  let low ← $ᵗ Digest
  return (high, low)

/-- Splitting a uniform 256-bit answer gives two independent uniform 128-bit halves. -/
theorem evalDist_split_uniformHashOutput_eq_independent :
    𝒟[hashOutputEquivDigestPair <$> ($ᵗ HashOutput)] =
      𝒟[independentDigestHalves] := by
  apply SPMF.ext
  intro target
  change Pr[= target | hashOutputEquivDigestPair <$> ($ᵗ HashOutput)] =
    Pr[= target | independentDigestHalves]
  rw [probOutput_map_bijective_uniform_cross
    (α := HashOutput) (β := Digest × Digest)
    hashOutputEquivDigestPair hashOutputEquivDigestPair.bijective]
  calc
    Pr[= target | $ᵗ (Digest × Digest)] =
        Pr[= target.1 | $ᵗ Digest] * Pr[= target.2 | $ᵗ Digest] := by
      simp [probOutput_uniformSample, Fintype.card_prod, ENNReal.mul_inv]
    _ = Pr[= target | independentDigestHalves] := by
      unfold independentDigestHalves
      symm
      simp

/-- Truncating a uniform 256-bit answer gives a uniform XMSS digest. -/
theorem evalDist_truncate_uniformHashOutput :
    𝒟[truncateHash <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ Digest] := by
  calc
    𝒟[truncateHash <$> ($ᵗ HashOutput)] =
        𝒟[Prod.snd <$> (hashOutputEquivDigestPair <$> ($ᵗ HashOutput))] := by
      simp [Functor.map_map, hashOutputEquivDigestPair]
    _ = 𝒟[Prod.snd <$> independentDigestHalves] := by
      rw [evalDist_map, evalDist_split_uniformHashOutput_eq_independent,
        ← evalDist_map]
    _ = 𝒟[$ᵗ Digest] := by
      unfold independentDigestHalves
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply SPMF.ext
      intro target
      change Pr[= target | do let _ ← $ᵗ Digest; $ᵗ Digest] =
        Pr[= target | $ᵗ Digest]
      rw [probOutput_bind_const, probFailure_uniformSample]
      simp

def matchingOutputs (target : Digest) : Finset HashOutput :=
  Finset.univ.filter (truncateHash · = target)

theorem card_matchingOutputs (target : Digest) :
    (matchingOutputs target).card = 2 ^ digestBits := by
  rw [show matchingOutputs target = Finset.univ.filter (truncateHash · = target) from rfl]
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (digestFiberEquiv target)).symm.trans (by simp)

private theorem truncated_union_budget_eq (q : Nat) :
    (((2 ^ digestBits : Nat) : ℝ≥0∞) *
      ((q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞))) =
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hzero : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ ∞ := by simp
  rw [hashOutputBits_eq, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ digestBits : Nat) : ℝ≥0∞) *
        ((q : ℝ≥0∞) *
          (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) =
        (((2 ^ digestBits : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
          ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

/-- Among `q` random-oracle queries, the chance of sampling one fixed 256-bit output is at most `q / 2^256`. -/
theorem exact_output_hit_le {α : Type} (computation : OracleComp HashSpec α) (q : Nat)
    (hbound : computation.IsTotalQueryBound q) (target : HashOutput) :
    Pr[fun result => ∃ input, result.2 input = some target |
      (simulateQ cachingOracle computation).run ∅] ≤
      (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
  have h := probEvent_cache_has_value_le computation q hbound (fun _ => by
    change Fintype.card HashOutput ≤ Fintype.card HashOutput
    exact le_rfl) target ∅ (by simp)
  simpa [card_hashOutput, div_eq_mul_inv] using h

/-- Starting from a cache without `target`, at most `q` further queries create a new entry with that exact output with probability `q / 2^256`. -/
theorem exact_output_hit_from_cache_le {α : Type} (computation : OracleComp HashSpec α)
    (q : Nat) (hbound : computation.IsTotalQueryBound q) (target : HashOutput)
    (cache : QueryCache HashSpec) (habsent : ∀ input, cache input ≠ some target) :
    Pr[fun result => ∃ input,
        result.2 input = some target ∧ cache input = none |
      (simulateQ cachingOracle computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
  have h := probEvent_cache_has_value_le computation q hbound (fun _ => by
    change Fintype.card HashOutput ≤ Fintype.card HashOutput
    exact le_rfl) target cache (by
      intro input output hcache heq
      cases heq
      exact habsent input hcache)
  simpa [card_hashOutput, div_eq_mul_inv] using h

/-- Starting from a cache without the target digest, at most `q` further queries create a new entry with that truncation with probability `q / 2^128`. -/
theorem truncated_output_hit_from_cache_le {α : Type}
    (computation : OracleComp HashSpec α) (q : Nat)
    (hbound : computation.IsTotalQueryBound q) (target : Digest)
    (cache : QueryCache HashSpec)
    (habsent : ∀ input output, cache input = some output → truncateHash output ≠ target) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output = target |
      (simulateQ cachingOracle computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let experiment := (simulateQ cachingOracle computation).run cache
  have hevent :
      (fun result : α × QueryCache HashSpec => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output = target) =
      (fun result : α × QueryCache HashSpec => ∃ output ∈ matchingOutputs target, ∃ input,
        result.2 input = some output ∧ cache input = none) := by
    funext result
    apply propext
    constructor
    · rintro ⟨input, output, hfinal, hinitial, htruncate⟩
      exact ⟨output, by simp [matchingOutputs, htruncate], input, hfinal, hinitial⟩
    · rintro ⟨output, houtput, input, hfinal, hinitial⟩
      exact ⟨input, output, hfinal, hinitial, (Finset.mem_filter.mp houtput).2⟩
  rw [hevent]
  calc
    Pr[fun result => ∃ output ∈ matchingOutputs target, ∃ input,
          result.2 input = some output ∧ cache input = none | experiment] ≤
        ∑ output ∈ matchingOutputs target,
          Pr[fun result => ∃ input,
            result.2 input = some output ∧ cache input = none | experiment] :=
      probEvent_exists_finset_le_sum (matchingOutputs target) experiment
        (fun output result => ∃ input,
          result.2 input = some output ∧ cache input = none)
    _ ≤ ∑ _output ∈ matchingOutputs target,
          (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro output houtput
      apply exact_output_hit_from_cache_le computation q hbound output cache
      intro input hcache
      exact habsent input output hcache (Finset.mem_filter.mp houtput).2
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_matchingOutputs]
    _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      truncated_union_budget_eq q

/-- A union bound for a finite set of previously absent 128-bit digest targets. -/
theorem truncated_outputs_hit_targets_from_cache_le {α : Type}
    (computation : OracleComp HashSpec α) (q : Nat)
    (hbound : computation.IsTotalQueryBound q) (targets : Finset Digest)
    (cache : QueryCache HashSpec)
    (habsent : ∀ input output, cache input = some output → truncateHash output ∉ targets) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output ∈ targets |
      (simulateQ cachingOracle computation).run cache] ≤
      (targets.card : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  let experiment := (simulateQ cachingOracle computation).run cache
  have hevent :
      (fun result : α × QueryCache HashSpec => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output ∈ targets) =
      (fun result : α × QueryCache HashSpec => ∃ target ∈ targets, ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output = target) := by
    funext result
    apply propext
    constructor
    · rintro ⟨input, output, hfinal, hinitial, htarget⟩
      exact ⟨truncateHash output, htarget, input, output, hfinal, hinitial, rfl⟩
    · rintro ⟨target, htarget, input, output, hfinal, hinitial, htruncate⟩
      exact ⟨input, output, hfinal, hinitial, htruncate ▸ htarget⟩
  rw [hevent]
  calc
    Pr[fun result => ∃ target ∈ targets, ∃ input output,
          result.2 input = some output ∧ cache input = none ∧ truncateHash output = target |
        experiment] ≤
        ∑ target ∈ targets,
          Pr[fun result => ∃ input output,
            result.2 input = some output ∧ cache input = none ∧ truncateHash output = target |
          experiment] :=
      probEvent_exists_finset_le_sum targets experiment
        (fun target result => ∃ input output,
          result.2 input = some output ∧ cache input = none ∧ truncateHash output = target)
    _ ≤ ∑ _target ∈ targets,
          (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro target htarget
      apply truncated_output_hit_from_cache_le computation q hbound target cache
      intro input output hcache heq
      exact habsent input output hcache (heq ▸ htarget)
    _ = (targets.card : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Among `q` random-oracle queries, the chance of sampling an output with one fixed 128-bit truncation is at most `q / 2^128`. -/
theorem truncated_output_hit_le {α : Type} (computation : OracleComp HashSpec α) (q : Nat)
    (hbound : computation.IsTotalQueryBound q) (target : Digest) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ truncateHash output = target |
      (simulateQ cachingOracle computation).run ∅] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa using truncated_output_hit_from_cache_le computation q hbound target ∅ (by simp)

end XmssSecurity.Rom
