import SphincsSecurity.Proof.OtsProbeNativeRootTraceCoupling
import SphincsSecurity.Proof.OtsProbePrivateValueProbeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem observeCompatibleNativeRootTrace_eq_filter
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :
    observeCompatibleNativeRootTrace parameter target before after trace =
      (observeCompatibleNativeRootTrace parameter target before before trace).filter
        (fun record => @decide (truncateHash after ∉ record.2) (Classical.propDecidable _)) := by
  rcases trace with ⟨option, history⟩
  cases option with
  | none => simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible]
  | some result =>
      by_cases hhidden : .position target ∉ result.context.state.revealed <;>
        by_cases hbefore : truncateHash before ∈ nativeRootCandidateHistory parameter target history <;>
        by_cases hafter : truncateHash after ∈ nativeRootCandidateHistory parameter target history <;>
        simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible, hhidden, hbefore, hafter,
          normalizeNativeRootResult, Option.filter]

theorem probOutput_observeCompatibleNativeRootTrace_eq_of_compatible
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (run : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
    (record : ResolvedRunResult α × Finset Digest) (hafter : truncateHash after ∉ record.2) :
    Pr[= some record | observeCompatibleNativeRootTrace parameter target before after <$> run] =
      Pr[= some record | observeCompatibleNativeRootTrace parameter target before before <$> run] := by
  have heq : observeCompatibleNativeRootTrace parameter target before after =
      (fun result => result.filter (fun value => @decide (truncateHash after ∉ value.2) (Classical.propDecidable _))) ∘
        observeCompatibleNativeRootTrace parameter target before before (α := α) :=
    funext (observeCompatibleNativeRootTrace_eq_filter parameter target before after)
  rw [heq]
  simpa only [Functor.map_map, Function.comp_def] using
    (probOutput_filter_some_of_predicate (observeCompatibleNativeRootTrace parameter target before before <$> run)
      (fun value => truncateHash after ∉ value.2) record hafter)

theorem probOutput_nativeRootTraceRecord_eq_of_compatible
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache)
    (record : ResolvedRunResult α × Finset Digest)
    (hbefore : truncateHash before ∉ record.2) (hafter : truncateHash after ∉ record.2) :
    Pr[= some record | observeCompatibleNativeRootTrace parameter target before before <$>
      runNativeQueryTrace parameter root ftsSecret computation left fuel table leftCache] =
    Pr[= some record | observeCompatibleNativeRootTrace parameter target after after <$>
      runNativeQueryTrace parameter root ftsSecret computation right fuel table rightCache] := by
  have hdist := evalDist_nativeRootSwap_compatibleTrace parameter root target hroot before after ftsSecret computation
    left right hcontext fuel table leftCache rightCache hcache
  have hprob := congrArg (fun distribution => distribution (some record)) hdist
  change Pr[= some record | observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation left fuel table leftCache] =
    Pr[= some record | observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret computation right fuel table rightCache] at hprob
  rw [probOutput_observeCompatibleNativeRootTrace_eq_of_compatible parameter target before after _ record hafter] at hprob
  have hswap : observeCompatibleNativeRootTrace parameter target before after (α := α) =
      observeCompatibleNativeRootTrace parameter target after before :=
    funext (observeCompatibleNativeRootTrace_swap parameter target before after)
  rw [hswap, probOutput_observeCompatibleNativeRootTrace_eq_of_compatible parameter target after before _ record hbefore] at hprob
  exact hprob

end SphincsSecurity.Concrete.OtsProbeSimulation
