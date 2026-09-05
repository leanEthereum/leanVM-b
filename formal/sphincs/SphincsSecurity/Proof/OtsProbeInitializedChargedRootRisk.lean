import SphincsSecurity.Proof.OtsProbeChargedRootInitialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedChargedRootCutObservation
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (target : Position)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel ordinal : Nat) (event : HashOutput × Option Digest → Prop) : ProbComp Bool := do
  let result ← runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match result with
  | none => pure true
  | some result =>
      originalChargedRootCutObservation parameter result.value.1 target ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2 ∅ ordinal event

noncomputable def initializedChargedRootCutCandidate
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (target : Position)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel ordinal : Nat) : ProbComp (Option Digest) := do
  let result ← runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match result with
  | none => pure none
  | some result =>
      (fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1) <$>
        runNativeQueryTrace parameter result.value.1 ftsSecret
        (outerHashQueryCutAt (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) ordinal)
        result.context result.remaining table result.value.2

theorem probEvent_initializedChargedRootCut_hit_le_occurrence
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (target : Position)
    (hmem : target ∈ targets) (hroot : IsLayerRoot target) (hne : target ≠ layerRootPosition topLayer rootTree)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel ordinal : Nat) (hbudget : ordinal ≤ 2 ^ 126) :
    Pr[fun b => b = false | initializedChargedRootCutObservation targets adversary parameter target table ftsSecret fuel ordinal
      (fun pair => pair.2 = some (truncateHash pair.1))] ≤
    Pr[fun candidate => candidate ≠ none | initializedChargedRootCutCandidate targets adversary parameter target table ftsSecret fuel ordinal] *
      ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  unfold initializedChargedRootCutObservation initializedChargedRootCutCandidate
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc]
  by_cases hresult : result ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · apply mul_le_mul' le_rfl
    cases result with
    | none => simp
    | some result =>
        dsimp only
        rw [probEvent_map]
        exact probEvent_chargedRootCut_after_keygen_hit_le_trace_occurrence parameter targets target hmem hroot hne ftsSecret
          (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩) fuel table result hresult ordinal hbudget
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
