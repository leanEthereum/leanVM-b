import SphincsSecurity.Proof.OtsProbeOuterCapRetained
import SphincsSecurity.Proof.OtsProbeCappedHistoryFts

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem probEvent_nativeFtsTrace_le_outerCapped_raw
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] ≤
      Pr[fun result => ∃ value, resolvedPrefixValue result = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedFromTable (ensuredInitialContext ∅) fuel table
          (outerCappedRetainedComputation adversary parameter ftsSecret q)] := by
  classical
  rw [probEvent_nativeFtsTrace_eq_live]
  let event : Option (Nat × Option (RetainedGameResult × SplitHashCache)) → Prop :=
    fun result => ∃ remaining value, result = some (remaining, some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value
  have hp := probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_outerCappedRetained_live adversary q hq parameter hparameter table ftsSecret hfts fuel) (p := event)
  rw [probEvent_map] at hp
  have hevent (result : Option (Nat × (RetainedGameResult × SplitHashCache))) :
      event (someLiveValue result) ↔
        ∃ remaining value, result = some (remaining, value) ∧ UncoveredFtsValueWitness parameter ftsSecret value := by
    cases result with
    | none =>
        constructor <;> rintro ⟨remaining, value, hvalue, _⟩ <;> cases hvalue
    | some result =>
        rcases result with ⟨remaining, value⟩
        simp only [event, someLiveValue, Option.map_some, Option.some.injEq, Prod.mk.injEq]
  have heq := hp.trans (probEvent_congr' (fun result _ => hevent result) rfl)
  rw [← heq]
  exact probEvent_live_option_le_raw _ _ fuel table (UncoveredFtsValueWitness parameter ftsSecret)

noncomputable def outerCappedErasedHistoryFtsWitnessRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ENNReal :=
  Pr[fun entry => ∃ value, historyPrefixValue entry = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
    runResolvedHistoryPrefix
      (eraseProbeQueries (outerCappedRetainedComputation adversary parameter ftsSecret q))
      (ensuredInitialContext ∅) 0 []]

theorem probEvent_sampled_nativeFtsTrace_le_outerCapped_erased_history
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]) ≤
      outerCappedErasedHistoryFtsWitnessRisk adversary parameter ftsSecret q := by
  apply (ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
    (probEvent_nativeFtsTrace_le_outerCapped_raw adversary q hq parameter hparameter table ftsSecret hfts fuel)).trans
  exact probEvent_sampled_resolved_value_le_erased_history ∅ _ fuel
    (fun result => ∃ value, result = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value) (by simp)

noncomputable def sampledOuterCappedErasedHistoryFtsWitnessRisk (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * outerCappedErasedHistoryFtsWitnessRisk adversary parameter ftsSecret q

theorem sampledNativeFtsWitnessRisk_le_outerCapped_erased_history
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNativeFtsWitnessRisk adversary fuel ≤ sampledOuterCappedErasedHistoryFtsWitnessRisk adversary q := by
  unfold sampledNativeFtsWitnessRisk sampledOuterCappedErasedHistoryFtsWitnessRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    exact mul_le_mul' le_rfl (probEvent_sampled_nativeFtsTrace_le_outerCapped_erased_history adversary q hq parameter hparameter
      ftsSecret (FtsProbeSimulation.mem_support_sampleFtsSecrets ftsSecret) fuel)
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

end SphincsSecurity.Concrete.OtsProbeSimulation
