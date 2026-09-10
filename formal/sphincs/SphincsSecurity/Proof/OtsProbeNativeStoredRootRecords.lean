import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootTraceOrdinaryCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runNativeStoredRootRecords
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (output : HashOutput) : ProbComp (Option (ResolvedRunResult α × Finset Digest)) :=
  if truncateHash output ∈ initialHistory then pure none else
    observeCompatibleNativeRootTrace parameter target output output <$>
      runNativeQueryTrace parameter root ftsSecret computation (replaceNativePosition target output context) fuel table cache

theorem nativeRootContextRel_replacements
    (target : Position) (before after : HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent)
    (hbefore : ¬context.state.hitAt (.position target) before)
    (hafter : ¬context.state.hitAt (.position target) after) :
    NativeRootContextRel target before after (replaceNativePosition target before context) (replaceNativePosition target after context) := by
  refine ⟨⟨replaceNativePosition_positionValue target before context,
    hconsistent.of_replaceNativePosition target before, hbefore, hafter⟩, ?_⟩
  rw [replaceNativePosition_idem]

theorem probOutput_nativeStoredRootRecords_eq_of_compatible
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (hconsistent : context.ValuesConsistent)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (hcache : ∀ digest, digest ∉ initialHistory → NoEncodingRootGuessCached parameter target digest cache)
    (before after : HashOutput) (record : ResolvedRunResult α × Finset Digest)
    (hbefore : truncateHash before ∉ initialHistory ∪ record.2)
    (hafter : truncateHash after ∉ initialHistory ∪ record.2) :
    Pr[= some record | runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory before] =
      Pr[= some record | runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory after] := by
  have hbeforeInitial : truncateHash before ∉ initialHistory := fun hmem => hbefore (Finset.mem_union_left _ hmem)
  have hafterInitial : truncateHash after ∉ initialHistory := fun hmem => hafter (Finset.mem_union_left _ hmem)
  have hbeforeHistory : truncateHash before ∉ record.2 := fun hmem => hbefore (Finset.mem_union_right _ hmem)
  have hafterHistory : truncateHash after ∉ record.2 := fun hmem => hafter (Finset.mem_union_right _ hmem)
  rw [runNativeStoredRootRecords, if_neg hbeforeInitial, runNativeStoredRootRecords, if_neg hafterInitial]
  apply probOutput_nativeRootTraceRecord_sameCache_eq_of_compatible parameter root target hroot before after ftsSecret computation
    _ _ (nativeRootContextRel_replacements target before after context hconsistent
      (fun hhit => hbeforeInitial (hpending hhit)) (fun hhit => hafterInitial (hpending hhit))) fuel table cache
    (hcache _ hbeforeInitial) (hcache _ hafterInitial) record hbeforeHistory hafterHistory

theorem nativeStoredRootRecords_supported_history
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (output : HashOutput) (bound : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (record : ResolvedRunResult α × Finset Digest)
    (hrecord : some record ∈ support (runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory output)) :
    truncateHash output ∉ initialHistory ∪ record.2 ∧ record.2.card ≤ bound := by
  unfold runNativeStoredRootRecords at hrecord
  by_cases hinitial : truncateHash output ∈ initialHistory
  · rw [if_pos hinitial] at hrecord
    simp at hrecord
  · rw [if_neg hinitial, support_map, Set.mem_image] at hrecord
    obtain ⟨trace, htrace, heq⟩ := hrecord
    rcases trace with ⟨option, history⟩
    cases option with
    | none => simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible] at heq
    | some result =>
        unfold observeCompatibleNativeRootTrace at heq
        split_ifs at heq with hcompatible
        · simp only [normalizeNativeRootResult, Option.map_some, Option.some.injEq] at heq
          have hhistory := congrArg Prod.snd heq
          have hclean : truncateHash output ∉ record.2 := by
            rw [← hhistory]
            exact hcompatible.2.1
          refine ⟨by simpa only [Finset.mem_union, not_or] using And.intro hinitial hclean, ?_⟩
          rw [← hhistory]
          exact runNativeQueryTrace_root_history_card_le parameter root ftsSecret target computation
            (replaceNativePosition target output context) fuel table cache bound hbound (some result, history) htrace

theorem probOutput_nativeStoredRootRecords_eq_zero_of_history_hit
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (output : HashOutput) (bound : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (record : ResolvedRunResult α × Finset Digest)
    (hhit : truncateHash output ∈ initialHistory ∪ record.2) :
    Pr[= some record | runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory output] = 0 := by
  apply probOutput_eq_zero_of_not_mem_support
  intro hrecord
  exact (nativeStoredRootRecords_supported_history parameter root target ftsSecret computation context fuel table cache initialHistory
    output bound hbound record hrecord).1 hhit

end SphincsSecurity.Concrete.OtsProbeSimulation
