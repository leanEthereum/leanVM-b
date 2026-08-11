import XmssSecurity.IndexedHiddenValue
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

open OracleComp ENNReal

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

abbrev RevealedIndex (revealed : Finset Index) := {index // index ∈ revealed}

abbrev UnrevealedIndex (revealed : Finset Index) := {index // index ∉ revealed}

noncomputable local instance revealedSampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance revealedSampleableFullTable :
    SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

noncomputable local instance revealedSampleableRevealedTable
    (revealed : Finset Index) :
    SampleableType (RevealedIndex revealed → Digest) :=
  SampleableType.ofFintype (RevealedIndex revealed → Digest)

noncomputable local instance revealedSampleableUnrevealedTable
    (revealed : Finset Index) :
    SampleableType (UnrevealedIndex revealed → Digest) :=
  SampleableType.ofFintype (UnrevealedIndex revealed → Digest)

noncomputable local instance revealedSampleableSplitTable
    (revealed : Finset Index) :
    SampleableType
      ((RevealedIndex revealed → Digest) × (UnrevealedIndex revealed → Digest)) :=
  SampleableType.ofFintype
    ((RevealedIndex revealed → Digest) × (UnrevealedIndex revealed → Digest))

noncomputable def splitTable (revealed : Finset Index) :
    (Index → Digest) ≃
      ((RevealedIndex revealed → Digest) × (UnrevealedIndex revealed → Digest)) where
  toFun table := (fun index => table index, fun index => table index)
  invFun tables index := if hindex : index ∈ revealed then
      tables.1 ⟨index, hindex⟩
    else
      tables.2 ⟨index, hindex⟩
  left_inv table := by
    funext index
    simp only
    split <;> rfl
  right_inv tables := by
    apply Prod.ext
    · funext index
      simp [index.property]
    · funext index
      simp [index.property]

noncomputable def independentSplitTable (revealed : Finset Index) :
    ProbComp
      ((RevealedIndex revealed → Digest) × (UnrevealedIndex revealed → Digest)) := do
  let revealedTable ← $ᵗ (RevealedIndex revealed → Digest)
  let hidden ← $ᵗ (UnrevealedIndex revealed → Digest)
  return (revealedTable, hidden)

theorem evalDist_split_uniformTable_eq_independent (revealed : Finset Index) :
    𝒟[splitTable revealed <$> ($ᵗ (Index → Digest))] =
      𝒟[independentSplitTable revealed] := by
  apply SPMF.ext
  intro target
  change Pr[= target | splitTable revealed <$> ($ᵗ (Index → Digest))] =
    Pr[= target | independentSplitTable revealed]
  rw [probOutput_map_bijective_uniform_cross
    (α := Index → Digest)
    (β := (RevealedIndex revealed → Digest) ×
      (UnrevealedIndex revealed → Digest))
    (splitTable revealed) (splitTable revealed).bijective]
  calc
    Pr[= target | $ᵗ ((RevealedIndex revealed → Digest) ×
        (UnrevealedIndex revealed → Digest))] =
        Pr[= target.1 | $ᵗ (RevealedIndex revealed → Digest)] *
          Pr[= target.2 | $ᵗ (UnrevealedIndex revealed → Digest)] := by
      simp [probOutput_uniformSample, Fintype.card_prod, ENNReal.mul_inv]
    _ = Pr[= target | independentSplitTable revealed] := by
      unfold independentSplitTable
      symm
      simp

noncomputable def revealedGuessExperiment (revealed : Finset Index)
    (queries : Nat)
    (strategy : (RevealedIndex revealed → Digest) →
      List Bool → UnrevealedIndex revealed × Digest) : ProbComp Bool := do
  let table ← $ᵗ (Index → Digest)
  let split := splitTable revealed table
  return readMany split.2 queries (strategy split.1)

/-- Revealing any fixed set of coordinates does not increase the cost of adaptively guessing coordinates outside that set. -/
theorem adaptive_guess_after_reveals_le (revealed : Finset Index)
    (queries : Nat)
    (strategy : (RevealedIndex revealed → Digest) →
      List Bool → UnrevealedIndex revealed × Digest) :
    Pr[(fun hit : Bool => hit = true) |
      revealedGuessExperiment revealed queries strategy] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let strategyGenerator : ProbComp
      (List Bool → UnrevealedIndex revealed × Digest) :=
    strategy <$> ($ᵗ (RevealedIndex revealed → Digest))
  have hdist :
      𝒟[revealedGuessExperiment revealed queries strategy] =
        𝒟[adaptiveGuessExperiment strategyGenerator queries] := by
    unfold revealedGuessExperiment adaptiveGuessExperiment experiment strategyGenerator
    simp only [bind_pure_comp, map_eq_bind_pure_comp]
    calc
      𝒟[(fun table => readMany (splitTable revealed table).2 queries
          (strategy (splitTable revealed table).1)) <$> ($ᵗ (Index → Digest))] =
          𝒟[(fun split => readMany split.2 queries (strategy split.1)) <$>
            (splitTable revealed <$> ($ᵗ (Index → Digest)))] := by
        simp [Functor.map_map]
      _ = 𝒟[(fun split => readMany split.2 queries (strategy split.1)) <$>
            independentSplitTable revealed] := by
        rw [evalDist_map, evalDist_split_uniformTable_eq_independent revealed,
          ← evalDist_map]
      _ = 𝒟[$ᵗ (RevealedIndex revealed → Digest) >>= pure ∘ strategy >>= fun strategy =>
            $ᵗ (UnrevealedIndex revealed → Digest) >>=
              pure ∘ fun table => readMany table queries strategy] := by
        unfold independentSplitTable
        simp [map_eq_bind_pure_comp, bind_assoc]
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (adaptive_guess_after_public_sampling_le strategyGenerator queries)

end XmssSecurity.IndexedHiddenValue
