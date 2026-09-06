import SphincsSecurity.Proof.OtsProbeCappedHistoryFts
import SphincsSecurity.Proof.OtsProbeOuterCapRetained

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_live_failure_or_value_eq_retained
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (event : α → Prop)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun result => result = none ∨ ∃ remaining value, result = some (remaining, value) ∧ event value |
      runResolvedLiveValue table context fuel computation] =
      Pr[fun result => retainCompletableResult result = none ∨
        ∃ value, resolvedPrefixValue (retainCompletableResult result) = some value ∧ event value |
        runResolvedFromTable context fuel table computation] := by
  unfold runResolvedLiveValue
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable context fuel table computation)
  · cases result with
    | none => simp [retainCompletableResult, resolvedPrefixValue]
    | some result =>
        have htable := (resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult).1
        by_cases hcomplete : DeferredCompletable table result.context <;>
          simp [retainCompletableResult, resolvedPrefixValue, htable, hcomplete]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem probEvent_native_joint_eq_live
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
      nativeRetainedParentTrace adversary parameter table ftsSecret fuel] =
      Pr[fun result => result = none ∨ ∃ remaining value,
        result = some (remaining, value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedLiveValue table (ensuredInitialContext ∅) fuel
          ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)] := by
  have hd := nativeRetainedParentTrace_result_projection adversary parameter table ftsSecret fuel
  have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd
    (p := fun result => result = none ∨
      ∃ value, resolvedPrefixValue result = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value)
  simp only [probEvent_map, Function.comp_def] at hp
  have hevent (trace : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) :
      (trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace) ↔
        trace.1 = none ∨ ∃ value, resolvedPrefixValue trace.1 = some value ∧ UncoveredFtsValueWitness parameter ftsSecret value := by
    cases htrace : trace.1 <;> simp [NativeFtsTraceEvent, resolvedPrefixValue, htrace, nativeUncoveredFtsWitness_iff_value]
  rw [probEvent_congr' (fun trace _ => hevent trace) rfl, hp]
  exact (probEvent_live_failure_or_value_eq_retained _ (ensuredInitialContext ∅) fuel table
    (UncoveredFtsValueWitness parameter ftsSecret) (ensuredInitialContext_valid ∅).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))).symm

theorem probEvent_native_joint_eq_outerCapped_live
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
      nativeRetainedParentTrace adversary parameter table ftsSecret fuel] =
      Pr[fun result => result = none ∨ ∃ remaining value,
        result = some (remaining, some value) ∧ UncoveredFtsValueWitness parameter ftsSecret value |
        runResolvedLiveValue table (ensuredInitialContext ∅) fuel
          (outerCappedRetainedComputation adversary parameter ftsSecret q)] := by
  rw [probEvent_native_joint_eq_live]
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_outerCappedRetained_live adversary q hq parameter hparameter table ftsSecret hfts fuel), probEvent_map]
  apply probEvent_congr' _ rfl
  intro result _
  cases result with
  | none => simp [someLiveValue]
  | some result =>
      rcases result with ⟨remaining, value⟩
      simp only [Function.comp_def, someLiveValue, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, reduceCtorEq, false_or]

end SphincsSecurity.Concrete.OtsProbeSimulation
