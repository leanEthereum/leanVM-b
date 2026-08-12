import XmssSecurity.ConcreteSign
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

theorem uniform_randomness_point_probability (target : Randomness) :
    Pr[= target | $ᵗ Randomness] =
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_randomness]

/-- For fixed public data and message, a serialized encoding input generated with uniform signing randomness hits any chosen input with probability at most `2^-192`. -/
theorem uniform_signingRandomness_encodingInput_probability_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message) (target : HashInput) :
    Pr[fun randomness : Randomness =>
      Concrete.CacheView.encodingInput parameter epoch (message, randomness) = target |
      $ᵗ Randomness] ≤
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  calc
    ((Finset.univ.filter fun randomness : Randomness =>
        Concrete.CacheView.encodingInput parameter epoch (message, randomness) = target).card :
        ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤
      1 * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply mul_le_mul_left
      exact_mod_cast Finset.card_le_one.mpr fun left hleft right hright => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hleft hright
        exact congrArg Prod.snd
          (Concrete.CacheView.encodingInput_injective parameter epoch
            (hleft.trans hright.symm))
    _ = ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := one_mul _

/-- Uniform signing randomness hits a finite set of pre-existing serialized inputs with the expected finite-set loss. -/
theorem uniform_signingRandomness_encodingInput_hits_finset_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (targets : Finset HashInput) :
    Pr[fun randomness : Randomness => ∃ input ∈ targets,
      Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input |
      $ᵗ Randomness] ≤
      (targets.card : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun randomness : Randomness => ∃ input ∈ targets,
        Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input |
        $ᵗ Randomness] ≤
      ∑ input ∈ targets,
        Pr[fun randomness : Randomness =>
          Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input |
          $ᵗ Randomness] :=
      probEvent_exists_finset_le_sum targets ($ᵗ Randomness)
        (fun input randomness =>
          Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input)
    _ ≤ ∑ _input ∈ targets,
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro input _
      exact uniform_signingRandomness_encodingInput_probability_le parameter epoch message input
    _ = (targets.card : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem uniform_signingRandomness_encodingInput_hits_bounded_finset_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (targets : Finset HashInput) (q : Nat) (hcard : targets.card ≤ q) :
    Pr[fun randomness : Randomness => ∃ input ∈ targets,
      Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input |
      $ᵗ Randomness] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  refine (uniform_signingRandomness_encodingInput_hits_finset_le
    parameter epoch message targets).trans ?_
  rw [div_eq_mul_inv]
  apply mul_le_mul
  · exact_mod_cast hcard
  · exact ENNReal.inv_le_inv.mpr (by
      exact_mod_cast (by
        norm_num [digestBits, randomnessBits] : 2 ^ digestBits ≤ 2 ^ randomnessBits))
  · exact zero_le
  · exact zero_le

/-- Uniform signing randomness hits an input already present in a random-oracle cache with probability controlled by the number of live cache entries. -/
theorem uniform_signingRandomness_encodingInput_cacheHit_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      QueryCache.enncard cache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
      some output
  let targets : Finset Randomness := Finset.univ.filter hit
  have hcard : (targets.card : ℝ≥0∞) ≤ QueryCache.enncard cache := by
    let embedding : (targets : Set Randomness) ↪ cache.toSet :=
      ⟨fun randomness =>
          ⟨⟨Concrete.CacheView.encodingInput parameter epoch
                (message, randomness.1),
              Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
            Classical.choose_spec (Finset.mem_filter.mp randomness.2).2⟩,
        fun left right heq => Subtype.ext <| congrArg Prod.snd <|
          Concrete.CacheView.encodingInput_injective parameter epoch <|
            congrArg (fun entry : cache.toSet => entry.1.1) heq⟩
    simpa only [QueryCache.enncard, Set.encard_coe_eq_coe_finsetCard,
      ENat.toENNReal_coe] using ENat.toENNReal_mono embedding.encard_le
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤ _
  exact mul_le_mul' hcard le_rfl

theorem uniform_signingRandomness_encodingInput_cacheHit_bounded_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) (q : Nat)
    (hcard : QueryCache.enncard cache ≤ (q : ℝ≥0∞)) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      (q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞) := by
  refine (uniform_signingRandomness_encodingInput_cacheHit_le
    parameter epoch message cache).trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul' hcard le_rfl

/-- The 192-bit signer-randomness cache-hit loss is below one elementary 128-bit term. -/
theorem uniform_signingRandomness_encodingInput_cacheHit_bounded_digest_le
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) (q : Nat)
    (hcard : QueryCache.enncard cache ≤ (q : ℝ≥0∞)) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  refine (uniform_signingRandomness_encodingInput_cacheHit_bounded_le
    parameter epoch message cache q hcard).trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hpow : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞) := by
    exact_mod_cast (by
      norm_num [digestBits, randomnessBits] : 2 ^ digestBits ≤ 2 ^ randomnessBits)
  gcongr

/-- Union-bounding one 192-bit signer-randomness loss for every possible epoch still fits below one 128-bit elementary term. -/
theorem lifetime_mul_randomness_loss_le_digest_loss (q : Nat) :
    (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞)) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) =
      (q : ℝ≥0∞) *
        ((lifetime : ℝ≥0∞) *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
    _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      have hleft : (lifetime : ℝ≥0∞) *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ =
          (lifetime : ℝ≥0∞) /
            ((2 ^ randomnessBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv]
      have hright : ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
          1 / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, one_mul]
      rw [hleft, hright]
      rw [ENNReal.div_le_iff (by positivity) (by simp)]
      have hrearrange :
          (1 / ((2 ^ digestBits : Nat) : ℝ≥0∞)) *
              ((2 ^ randomnessBits : Nat) : ℝ≥0∞) =
            ((2 ^ randomnessBits : Nat) : ℝ≥0∞) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ac_rfl
      rw [hrearrange, ENNReal.le_div_iff_mul_le (by simp) (by simp)]
      exact_mod_cast (by
        norm_num [lifetime, treeHeight, digestBits, randomnessBits] :
          lifetime * 2 ^ digestBits ≤ 2 ^ randomnessBits)

end XmssSecurity
