import SphincsSecurity.Proof.OtsProbeLiveValueCap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem probEvent_nativeFtsTrace_eq_live
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] =
      Pr[fun result => ∃ remaining value, result = some (remaining, value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedLiveValue table (ensuredInitialContext ∅) fuel
          ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)] := by
  have hd := nativeRetainedParentTrace_result_projection adversary parameter table ftsSecret fuel
  have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd
    (p := fun result => ∃ value, resolvedPrefixValue result = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value)
  simp only [probEvent_map, Function.comp_def] at hp
  have hevent (trace : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) :
      NativeFtsTraceEvent parameter table ftsSecret trace ↔
        ∃ value, resolvedPrefixValue trace.1 = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value := by
    cases htrace : trace.1 <;> simp [NativeFtsTraceEvent, resolvedPrefixValue, htrace, nativeUncoveredFtsWitness_iff_value]
  rw [probEvent_congr' (fun trace _ => hevent trace) rfl, hp]
  exact (probEvent_live_value_eq_retained _ (ensuredInitialContext ∅) fuel table
    (UncoveredFtsValueWitness parameter ftsSecret) (ensuredInitialContext_valid ∅).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))).symm

theorem liveResolvedProbeBound_fullRetained_of_gameBudget
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    LiveResolvedQueryBound LazyRevealProbe.IsProbe
      ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)
      q (ensuredInitialContext ∅) fuel table := by
  have hbound := liveResolvedProbeBound_nativeRetained_of_gameBudget ∅ adversary q hq parameter hparameter table ftsSecret hfts fuel
  rw [nativeChronologicalRetainedComputation_eq_chronological_projection, liveResolvedQueryBound_map_iff] at hbound
  exact hbound

theorem probEvent_nativeFtsTrace_le_capped_raw
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] ≤
      Pr[fun result => ∃ value, resolvedPrefixValue result = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedFromTable (ensuredInitialContext ∅) fuel table
          (capProbeQueries ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache) q)] := by
  rw [probEvent_nativeFtsTrace_eq_live]
  have hbound := probEvent_live_value_le_capped_raw
    ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)
    (ensuredInitialContext ∅) fuel table q (UncoveredFtsValueWitness parameter ftsSecret)
    (ensuredInitialContext_valid ∅).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))
    (liveResolvedProbeBound_fullRetained_of_gameBudget adversary q hq parameter hparameter table ftsSecret hfts fuel)
  apply hbound.trans_eq
  apply probEvent_congr' _ rfl
  intro result _
  cases result <;> simp [resolvedPrefixValue]

noncomputable def cappedErasedHistoryFtsWitnessRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ENNReal :=
  Pr[fun entry => ∃ value, historyPrefixValue entry = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
    runResolvedHistoryPrefix
      (eraseProbeQueries (capProbeQueries
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache) q))
      (ensuredInitialContext ∅) 0 []]

theorem probEvent_sampled_nativeFtsTrace_le_capped_erased_history
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]) ≤
      cappedErasedHistoryFtsWitnessRisk adversary parameter ftsSecret q := by
  apply (ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
    (probEvent_nativeFtsTrace_le_capped_raw adversary q hq parameter hparameter table ftsSecret hfts fuel)).trans
  exact probEvent_sampled_resolved_value_le_erased_history ∅ _ fuel
    (fun result => ∃ value, result = some (some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value) (by simp)

noncomputable def sampledCappedErasedHistoryFtsWitnessRisk (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * cappedErasedHistoryFtsWitnessRisk adversary parameter ftsSecret q

theorem sampledNativeFtsWitnessRisk_le_capped_erased_history
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNativeFtsWitnessRisk adversary fuel ≤ sampledCappedErasedHistoryFtsWitnessRisk adversary q := by
  unfold sampledNativeFtsWitnessRisk sampledCappedErasedHistoryFtsWitnessRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    exact mul_le_mul' le_rfl (probEvent_sampled_nativeFtsTrace_le_capped_erased_history adversary q hq parameter hparameter
      ftsSecret (FtsProbeSimulation.mem_support_sampleFtsSecrets ftsSecret) fuel)
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem cappedErasedHistoryFtsWitnessRisk_le_uncapped
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    cappedErasedHistoryFtsWitnessRisk adversary parameter ftsSecret q ≤ erasedHistoryFtsWitnessRisk adversary parameter ftsSecret :=
  probEvent_capped_erased_value_le_uncapped _ q (ensuredInitialContext ∅) (UncoveredFtsValueWitness parameter ftsSecret)

theorem sampledCappedErasedHistoryFtsWitnessRisk_le_uncapped (adversary : Adversary) (q : Nat) :
    sampledCappedErasedHistoryFtsWitnessRisk adversary q ≤ sampledErasedHistoryFtsWitnessRisk adversary := by
  unfold sampledCappedErasedHistoryFtsWitnessRisk sampledErasedHistoryFtsWitnessRisk
  exact ENNReal.tsum_le_tsum fun parameter => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun ftsSecret => mul_le_mul' le_rfl
      (cappedErasedHistoryFtsWitnessRisk_le_uncapped adversary parameter ftsSecret q))

end SphincsSecurity.Concrete.OtsProbeSimulation
