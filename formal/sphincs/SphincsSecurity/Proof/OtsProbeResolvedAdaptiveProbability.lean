import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveBoundary
import SphincsSecurity.Proof.OtsProbeChronologicalProbability

/-!
# Probability boundary for canonical adaptive one-time probes

The canonical chronological monitor couples directly to the real retained game. Its deterministic
terminal contradiction bounds a real winning hidden opening by canonical completion failure, which
is the event shared with the delayed monitor.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

def CanonicalChronologicalSupported
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) : Prop :=
  some result ∈ support
    (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem not_completionVerifyProbe_of_canonicalReachableResolvedRunRel
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : CanonicalChronologicalSupported adversary parameter table ftsSecret fuel result)
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache))
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table result.context completion)
    (hprobe : VerifyProbeWitness
      (tableAnswer parameter completion (fromCache (ordinaryQueryCache result.value.2)))
      actualCache
      (⟨parameter, actualValue.1,
        fun lay tree leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
        ftsSecret⟩ : SecretKey)
      actualValue.2.1.2 actualValue.2.1.1.message actualValue.2.1.1.signature) : False := by
  rcases hrelation with hclean | hdoomed
  · have hactual' : (result.value.1, actualCache) ∈ support
        (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
      rw [hclean.2.1]
      exact hactual
    have hprobe' : VerifyProbeWitness
        (tableAnswer parameter completion (fromCache (ordinaryQueryCache result.value.2)))
        actualCache
        (⟨parameter, result.value.1.1,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        result.value.1.2.1.2 result.value.1.2.1.1.message
          result.value.1.2.1.1.signature := by
      rw [hclean.2.1]
      exact hprobe
    let fallback : QueryImpl HashSpec Id := fromCache (ordinaryQueryCache result.value.2)
    have hfallback : CacheAgreesWithFnOffTable parameter completion
        (ordinaryQueryCache result.value.2) fallback :=
      CacheAgreesWithFnOffTable.of_agrees
        (agreesWithFn_fromCache (ordinaryQueryCache result.value.2))
    have hagrees : actualCache.AgreesWithFn
        (tableAnswer parameter completion fallback) :=
      hclean.2.2.1.concreteCache_agreesWith_tableAnswer_of_fallback completion hcompletion
        fallback hfallback
    have hlogRuns := successfulSignRuns_of_mem_support_actualRetainedGameAfterTable adversary
      (tableAnswer parameter completion fallback) parameter table ftsSecret result.value.1.1
        result.value.1.2.1.1 result.value.1.2.1.2 result.value.1.2.2 actualCache hactual' hagrees
    unfold CanonicalChronologicalSupported at hresult
    unfold canonicalChronologicalRetainedRunAfterFtsSecrets at hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨rootOption, hroot, hrest⟩ := hresult
    cases rootOption with
    | none => simp at hrest
    | some rootResult =>
        have hrootCore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table
          fuel rootResult hroot
        simp only at hrest
        rw [hrootCore.1, mem_support_bind_iff] at hrest
        obtain ⟨adversaryOption, hadversary, hverifierFinish⟩ := hrest
        cases adversaryOption with
        | none => simp [canonicalVerifierContinuation] at hverifierFinish
        | some adversaryResult =>
            have hadversaryCore :=
              resolvedCore_of_mem_runSynchronizedResolved_canonicalChronological
                parameter rootResult.value.1 table ftsSecret
                (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
                rootResult.context rootResult.remaining rootResult.value.2 adversaryResult
                  hrootCore.2.1 hrootCore.2.2 hadversary
            have hadversaryCompletion :=
              hcompletion.of_mem_canonicalVerifierContinuation parameter rootResult.value.1 table
                adversaryResult result completion hadversaryCore.1 hverifierFinish
                  hadversaryCore.2.1 hadversaryCore.2.2
            have hrootCompletion : DeferredCompletion table rootResult.context completion :=
              hadversaryCompletion.of_mem_runSynchronizedResolved_canonicalChronological
                (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
                rootResult.context rootResult.remaining rootResult.value.2 adversaryResult
                  completion hrootCore.2.1 hrootCore.2.2 hadversary
            obtain ⟨hrootBoundary⟩ := canonicalRootBoundary_of_mem parameter table
              (CoveredChainCoordinate (tableAnswer parameter completion fallback) actualCache
                (⟨parameter, rootResult.value.1,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩ : SecretKey)
                adversaryResult.value.1.2)
              fuel rootResult completion hroot hrootCompletion
            obtain ⟨hadversaryBoundary, _hadversaryFallback⟩ := by
              apply canonicalAdversaryBoundary_of_mem adversary parameter rootResult.value.1 table
                ftsSecret actualCache completion fallback rootResult adversaryResult result
                  hrootBoundary hadversary hadversaryCore.1 hadversaryCompletion hverifierFinish
                    hcompletion hfallback
              exact hlogRuns
            let terminal : CanonicalVerifierTerminal parameter rootResult.value.1 table ftsSecret
                actualCache completion fallback adversaryResult :=
              { result := result
                table_eq := hadversaryCore.1
                mem_support := hverifierFinish
                resultCompletion := hcompletion
                fallbackAgrees := hfallback
                probe := hprobe' }
            exact hadversaryBoundary.contradicts_canonicalVerifierTerminal
              parameter rootResult.value.1 table ftsSecret actualCache completion fallback
                adversaryResult terminal
  · exact hdoomed.2.2.2 ⟨completion, hcompletion⟩

theorem not_resolvedCompletionVerifyProbe_of_canonicalReachableResolvedRunRel
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : CanonicalChronologicalSupported adversary parameter table ftsSecret fuel result)
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache)) :
    ¬ResolvedCompletionVerifyProbe parameter table ftsSecret result actualValue actualCache := by
  rintro ⟨completion, hcompletion, hprobe⟩
  exact not_completionVerifyProbe_of_canonicalReachableResolvedRunRel adversary parameter table
    ftsSecret fuel result actualValue actualCache hresult hactual hrelation completion hcompletion
      hprobe

theorem not_deferredCompletable_of_winningRetainedVerifyProbe_canonical
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actualValue : RetainedGameResult) (actualCache : QueryCache HashSpec)
    (hresult : CanonicalChronologicalSupported adversary parameter table ftsSecret fuel result)
    (hactual : (actualValue, actualCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (actualValue, actualCache))
    (hwitness : WinningRetainedVerifyProbeWitness parameter (extendStartTable table)
      ftsSecret (actualValue, actualCache)) :
    ¬DeferredCompletable table result.context := by
  intro hcompletable
  have hcompletionProbe :=
    resolvedCompletionVerifyProbe_of_winning_of_deferredCompletable adversary parameter table
      ftsSecret result actualValue actualCache hactual hrelation hcompletable hwitness
  exact (not_resolvedCompletionVerifyProbe_of_canonicalReachableResolvedRunRel adversary
    parameter table ftsSecret fuel result actualValue actualCache hresult hactual hrelation)
      hcompletionProbe

theorem probEvent_winningRetainedVerifyProbe_le_canonicalResolvedCompletionFailure
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[ResolvedCompletionFailure table |
        canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret
          fuel] := by
  let canonicalRun := canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table
    ftsSecret fuel
  let actualRun :=
    actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)
  have hrel := relTriple_canonicalChronologicalRetainedRun_actual adversary parameter table
    ftsSecret fuel
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrel
      (fun result => result ∈ support canonicalRun) (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply probEvent_le_of_relTriple (relTriple_symm hboth)
  intro actualResult canonicalResult hrelation hwitness
  cases canonicalResult with
  | none => trivial
  | some result =>
      have hresult : CanonicalChronologicalSupported adversary parameter table ftsSecret fuel
          result := hrelation.1.2
      exact not_deferredCompletable_of_winningRetainedVerifyProbe_canonical adversary parameter
        table ftsSecret fuel result actualResult.1 actualResult.2 hresult hrelation.2
          hrelation.1.1 hwitness

theorem probEvent_winningRetainedVerifyProbe_le_canonicalFinishedResolvedRun_none
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[fun result => result = none |
        canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret
          fuel >>= finishResolvedRun] := by
  apply (probEvent_winningRetainedVerifyProbe_le_canonicalResolvedCompletionFailure adversary
    parameter table ftsSecret fuel).trans
  apply probEvent_resolvedCompletionFailure_le_finishResolvedRun_none table
  intro result hresult
  have hrel := relTriple_canonicalChronologicalRetainedRun_actual adversary parameter table
    ftsSecret fuel
  obtain ⟨actualResult, _hactual, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support hrel hresult
  rcases hrelation with hclean | hdoomed
  · exact hclean.1
  · exact hdoomed.1

end SphincsSecurity.Concrete.OtsProbeSimulation
