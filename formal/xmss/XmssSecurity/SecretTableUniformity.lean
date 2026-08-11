import XmssSecurity.ConcreteKeygen
import XmssSecurity.IndexedHiddenValue
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal

namespace XmssSecurity

noncomputable local instance secretTableSampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance secretTableSampleableEpochDigest :
    SampleableType (Epoch → Digest) :=
  SampleableType.ofFintype (Epoch → Digest)

noncomputable local instance secretTableSampleableFlatSecret :
    SampleableType (Epoch × ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch × ChainIndex → Digest)

noncomputable local instance secretTableSampleableSecret :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

/-- For a fixed WOTS chain, all epoch seeds are jointly uniform and independent. -/
theorem evalDist_sampleSecret_fixedChain_eq_uniform (chain : ChainIndex) :
    𝒟[(fun secret : Epoch → ChainIndex → Digest => fun epoch => secret epoch chain) <$>
      Concrete.sampleSecret] =
      𝒟[$ᵗ (Epoch → Digest)] := by
  let flatten : (Epoch → ChainIndex → Digest) → (Epoch × ChainIndex → Digest) :=
    fun secret address => secret address.1 address.2
  have hflatten : Function.Bijective flatten := by
    constructor
    · intro left right heq
      funext epoch candidateChain
      exact congrFun heq (epoch, candidateChain)
    · intro table
      exact ⟨fun epoch candidateChain => table (epoch, candidateChain), rfl⟩
  let embed : Epoch → Epoch × ChainIndex := fun epoch => (epoch, chain)
  have hembed : Function.Injective embed := by
    intro left right heq
    exact congrArg Prod.fst heq
  unfold Concrete.sampleSecret
  calc
    𝒟[(fun secret : Epoch → ChainIndex → Digest => fun epoch => secret epoch chain) <$>
        ($ᵗ (Epoch → ChainIndex → Digest))] =
      𝒟[(fun table : Epoch × ChainIndex → Digest => table ∘ embed) <$>
        (flatten <$> ($ᵗ (Epoch → ChainIndex → Digest)))] := by
      simp only [Functor.map_map, Function.comp_def, flatten, embed]
    _ = 𝒟[(fun table : Epoch × ChainIndex → Digest => table ∘ embed) <$>
        ($ᵗ (Epoch × ChainIndex → Digest))] := by
      rw [evalDist_map]
      rw [evalDist_map_bijective_uniform_cross
        (α := Epoch → ChainIndex → Digest) (β := Epoch × ChainIndex → Digest)
        flatten hflatten]
      rw [← evalDist_map]
    _ = 𝒟[$ᵗ (Epoch → Digest)] :=
      evalDist_uniformSample_map_comp_injective hembed

theorem sampleSecret_fixedChain_probability (chain : ChainIndex)
    (target : Epoch → Digest) :
    Pr[= target |
      (fun secret : Epoch → ChainIndex → Digest => fun epoch => secret epoch chain) <$>
        Concrete.sampleSecret] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ lifetime) := by
  calc
    Pr[= target |
        (fun secret : Epoch → ChainIndex → Digest => fun epoch => secret epoch chain) <$>
          Concrete.sampleSecret] =
        Pr[= target | $ᵗ (Epoch → Digest)] :=
      probOutput_congr rfl (evalDist_sampleSecret_fixedChain_eq_uniform chain)
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ lifetime) := by
      rw [probOutput_uniformSample, Fintype.card_fun, HiddenValue.card_digest]
      have hcard : Fintype.card Epoch = lifetime := by simp [Epoch]
      rw [hcard, Nat.cast_pow, ENNReal.inv_pow]

theorem sampleSecret_fixed_coordinate_probability (epoch : Epoch) (chain : ChainIndex)
    (target : Digest) :
    Pr[fun secret : Epoch → ChainIndex → Digest => secret epoch chain = target |
      Concrete.sampleSecret] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  let restrict := fun secret : Epoch → ChainIndex → Digest =>
    fun candidateEpoch => secret candidateEpoch chain
  calc
    Pr[fun secret : Epoch → ChainIndex → Digest => secret epoch chain = target |
        Concrete.sampleSecret] =
      Pr[fun table : Epoch → Digest => table epoch = target |
        restrict <$> Concrete.sampleSecret] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun table : Epoch → Digest => table epoch = target |
        $ᵗ (Epoch → Digest)] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sampleSecret_fixedChain_eq_uniform chain)
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      IndexedHiddenValue.uniform_table_coordinate_probability epoch target

noncomputable def fixedChainSecretGuessExperiment (chain : ChainIndex) (queries : Nat)
    (strategy : List Bool → Epoch × Digest) : ProbComp Bool := do
  let secret ← Concrete.sampleSecret
  return IndexedHiddenValue.readMany (fun epoch => secret epoch chain) queries strategy

/-- Before key generation exposes any derived values, adaptive equality probes against all epoch seeds of one chain cost only once per probe. -/
theorem fixedChainSecret_adaptive_guess_le (chain : ChainIndex) (queries : Nat)
    (strategy : List Bool → Epoch × Digest) :
    Pr[(fun hit : Bool => hit = true) |
      fixedChainSecretGuessExperiment chain queries strategy] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let restrict := fun secret : Epoch → ChainIndex → Digest =>
    fun epoch => secret epoch chain
  have hdist : 𝒟[fixedChainSecretGuessExperiment chain queries strategy] =
      𝒟[IndexedHiddenValue.experiment queries strategy] := by
    unfold fixedChainSecretGuessExperiment IndexedHiddenValue.experiment
    simp only [bind_pure_comp]
    calc
      𝒟[(fun secret : Epoch → ChainIndex → Digest =>
          IndexedHiddenValue.readMany (fun epoch => secret epoch chain) queries strategy) <$>
          Concrete.sampleSecret] =
        𝒟[(fun table => IndexedHiddenValue.readMany table queries strategy) <$>
          (restrict <$> Concrete.sampleSecret)] := by
        simp [restrict, Functor.map_map]
      _ = 𝒟[(fun table => IndexedHiddenValue.readMany table queries strategy) <$>
          ($ᵗ (Epoch → Digest))] := by
        rw [evalDist_map]
        rw [evalDist_sampleSecret_fixedChain_eq_uniform chain]
        rw [← evalDist_map]
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (IndexedHiddenValue.adaptive_guess_le queries strategy)

end XmssSecurity
