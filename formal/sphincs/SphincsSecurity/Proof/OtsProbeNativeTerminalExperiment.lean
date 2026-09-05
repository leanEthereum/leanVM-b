import SphincsSecurity.Proof.OtsProbeNativeTerminalReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeTerminalFailureAfterRoot
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool := do
  let trace ← nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
    (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)
  finishResolvedRunIsNone trace.1

theorem probEvent_nativeTerminalFailureAfterRoot_eq_risk
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel] =
      ∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
        (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1 := by
  rw [nativeTerminalFailureAfterRoot, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro trace
  have heq := probEvent_finished_eq_expected_outcomeRisk (pure trace.1)
  simp only [pure_bind, tsum_probOutput_pure_mul] at heq
  rw [heq]

noncomputable def sampledNativeTerminalFailure (adversary : Adversary) (fuel : Nat) : ProbComp Bool := do
  let parameter ← sampleParameter
  let ftsSecret ← sampleFtsSecrets
  let table ← sampleOtsHashTable
  nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel

theorem probEvent_sampledNativeTerminalFailure_eq_risk (adversary : Adversary) (fuel : Nat) :
    Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] = sampledNativeTerminalRisk adversary fuel := by
  simp only [sampledNativeTerminalFailure, probEvent_bind_eq_tsum, probEvent_nativeTerminalFailureAfterRoot_eq_risk,
    sampledNativeTerminalRisk]

theorem probEvent_sampledNativeTerminalFailure_add_rootMatch_le_refinedReserve
    (roots : Finset Position) (hroots : ∀ target ∈ roots, IsLayerRoot target)
    (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary (q + 1)] +
      sampledNativeFinalRootMatchRisk Finset.univ roots adversary (q + 1) ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_add_rootMatch_le_refinedReserve roots hroots hne adversary q hq hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
