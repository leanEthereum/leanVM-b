import SphincsSecurity.Proof.FirstParentJointSecrets
import SphincsSecurity.Proof.OtsProbeErasedRun

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem runResolvedFromTable_map
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (project : α → β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    runResolvedFromTable context fuel table (project <$> computation) =
      (fun result => result.map (fun result =>
        ResolvedRunResult.mk result.context result.remaining (project result.value) result.table)) <$>
          runResolvedFromTable context fuel table computation := by
  rw [map_eq_bind_pure_comp, runResolvedFromTable_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem retainCompletableResult_map
    (project : α → β) (result : Option (ResolvedRunResult α)) :
    retainCompletableResult (result.map (fun result =>
      ResolvedRunResult.mk result.context result.remaining (project result.value) result.table)) =
      (retainCompletableResult result).map (fun result =>
        ResolvedRunResult.mk result.context result.remaining (project result.value) result.table) := by
  cases result with
  | none => rfl
  | some result =>
      simp only [retainCompletableResult, Option.map_some]
      split_ifs <;> rfl

theorem nativeRetainedParentTrace_result_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (Prod.fst <$> nativeRetainedParentTrace adversary parameter table ftsSecret fuel) =
      evalDist (retainCompletableResult <$> runResolvedFromTable (ensuredInitialContext ∅) fuel table
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)) := by
  rw [nativeRetainedParentTrace, maskedChronologicalRetainedGame_eq_root_rest, runResolvedFromTable_bind]
  simp only [map_bind]
  apply evalDist_bind_congr
  intro root hroot
  cases root with
  | none => rfl
  | some root =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext ∅) fuel table root
        (ensuredInitialContext_valid ∅).valuesConsistent
        (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table)) hroot
      have hd := runNativeQueryTrace_result_projection parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining root.table root.value.2 hcore.2.1 (by rw [hcore.1]; exact hcore.2.2)
      have hm := evalDist_map_eq_of_evalDist_eq hd (fun result => result.map (retainedResultWithRoot root.value.1))
      simp only [bind_pure_comp, runResolvedFromTable_map, Functor.map_map] at hm ⊢
      convert hm using 1
      congr 2
      funext result
      exact retainCompletableResult_map (fun value : RetainedRestResult × SplitHashCache =>
        ((root.value.1, value.1), value.2)) result

def UncoveredFtsValueWitness (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (value : RetainedGameResult × SplitHashCache) : Prop :=
  NativeUncoveredFtsWitness parameter (fun _ => 0) ftsSecret
    ⟨ensuredInitialContext ∅, 0, value, fun _ => 0⟩

theorem nativeUncoveredFtsWitness_iff_value
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) :
    NativeUncoveredFtsWitness parameter table ftsSecret result ↔
      UncoveredFtsValueWitness parameter ftsSecret result.value := Iff.rfl

theorem probEvent_nativeFtsTrace_le_raw
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] ≤
      Pr[fun result => ∃ value, resolvedPrefixValue result = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedFromTable (ensuredInitialContext ∅) fuel table
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
  apply probEvent_mono
  intro result _hsupport hevent
  cases result with
  | none => exact hevent
  | some result =>
      simp only [retainCompletableResult] at hevent
      split_ifs at hevent with hcomplete
      · exact hevent
      · simp [resolvedPrefixValue] at hevent

noncomputable def erasedHistoryFtsWitnessRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : ENNReal :=
  Pr[fun entry => ∃ value, historyPrefixValue entry = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value |
    runResolvedHistoryPrefix
      (eraseProbeQueries ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache))
      (ensuredInitialContext ∅) 0 []]

theorem probEvent_sampled_nativeFtsTrace_le_erased_history
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]) ≤
      erasedHistoryFtsWitnessRisk adversary parameter ftsSecret := by
  apply (ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
    (probEvent_nativeFtsTrace_le_raw adversary parameter table ftsSecret fuel)).trans
  exact probEvent_sampled_resolved_value_le_erased_history ∅ _ fuel
    (fun result => ∃ value, result = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value) (by simp)

noncomputable def sampledErasedHistoryFtsWitnessRisk (adversary : Adversary) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * erasedHistoryFtsWitnessRisk adversary parameter ftsSecret

theorem sampledNativeFtsWitnessRisk_le_erased_history (adversary : Adversary) (fuel : Nat) :
    sampledNativeFtsWitnessRisk adversary fuel ≤ sampledErasedHistoryFtsWitnessRisk adversary := by
  unfold sampledNativeFtsWitnessRisk sampledErasedHistoryFtsWitnessRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl (probEvent_sampled_nativeFtsTrace_le_erased_history adversary parameter ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
