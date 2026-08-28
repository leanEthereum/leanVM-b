import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveVerifier

/-!
# Reachable publication boundaries for canonical adaptive one-time probes
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure CanonicalResolvedBoundary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (cache : SplitHashCache)
    (allowed : Coordinate → Prop) where
  concreteCache : QueryCache HashSpec
  invariant : ResolvedContextInvariant parameter table context
    (ordinaryQueryCache cache) concreteCache
  closed : VisibleResolvedComputationsCached parameter table context concreteCache
  published : PublishedValues context.state
  allowed : RevealedChainAllowed allowed context.state

structure CanonicalVerifierTerminal
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache)) where
  result : ResolvedRunResult (RetainedGameResult × SplitHashCache)
  table_eq : adversaryResult.table = table
  mem_support : some result ∈ support
    (canonicalVerifierContinuation parameter root (some adversaryResult))
  resultCompletion : DeferredCompletion table result.context completion
  fallbackAgrees : CacheAgreesWithFnOffTable parameter completion
    (ordinaryQueryCache result.value.2) fallback
  probe : VerifyProbeWitness (tableAnswer parameter completion fallback) targetCache
    (⟨parameter, result.value.1.1,
      fun lay tree leafIdx chainIdx =>
        truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
      ftsSecret⟩ : SecretKey)
    result.value.1.2.1.2 result.value.1.2.1.1.message
      result.value.1.2.1.1.signature

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem canonicalRootBoundary_of_mem
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (allowed : Coordinate → Prop) (fuel : Nat)
    (rootResult : ResolvedRunResult (Digest × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hroot : some rootResult ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hcompletion : DeferredCompletion table rootResult.context completion) :
    Nonempty
      (CanonicalResolvedBoundary parameter table rootResult.context rootResult.value.2
        allowed) := by
  obtain ⟨rootConcreteCache, hrootInvariant, hrootClosed, hrootPublished,
      _hrootConcrete⟩ :=
    concreteSupport_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel
      rootResult completion hroot hcompletion
  have hemptyAllowed : RevealedChainAllowed allowed
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
    intro coordinate _hchain hrevealed
    simp [LazyRevealProbe.State.empty] at hrevealed
  have hrootAllowed : RevealedChainAllowed allowed rootResult.context.state :=
    resolvedPreservesChainPublication_maskedPublishedTreeRoot allowed
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      emptySplitHashCache fuel table rootResult completion
        DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table)
          hemptyAllowed hroot hcompletion
  exact ⟨⟨rootConcreteCache, hrootInvariant, hrootClosed, hrootPublished, hrootAllowed⟩⟩

set_option maxRecDepth 100000 in
theorem canonicalAdversaryBoundary_of_mem
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (rootResult : ResolvedRunResult (Digest × SplitHashCache))
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (hrootBoundary : CanonicalResolvedBoundary parameter table rootResult.context
      rootResult.value.2
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        adversaryResult.value.1.2))
    (hadversary : some adversaryResult ∈ support
      (runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩))
        rootResult.context rootResult.remaining table rootResult.value.2))
    (htable : adversaryResult.table = table)
    (hcompletion : DeferredCompletion table adversaryResult.context completion)
    (hfinish : some result ∈ support
      (canonicalVerifierContinuation parameter root (some adversaryResult)))
    (hfinalCompletion : DeferredCompletion table result.context completion)
    (hfinalFallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ result.value.1.2.1.2 →
        entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, result.value.1.1,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature) :
    ∃ _boundary : CanonicalResolvedBoundary parameter table adversaryResult.context
        adversaryResult.value.2
        (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          adversaryResult.value.1.2),
      CacheAgreesWithFnOffTable parameter completion
        (ordinaryQueryCache adversaryResult.value.2) fallback := by
  obtain ⟨adversaryConcreteCache, hadversaryInvariant, hadversaryClosed,
      hadversaryPublished, _hadversaryConcrete⟩ :=
    concreteSupport_of_mem_runSynchronizedResolved
      (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table
        ftsSecret)
      (signingTraceComputation (adversary.main ⟨root, parameter⟩))
      rootResult.context rootResult.remaining rootResult.value.2 hrootBoundary.concreteCache
        adversaryResult completion hrootBoundary.invariant hrootBoundary.closed
          hrootBoundary.published hadversary hcompletion
  have hadversaryFallback :=
    hfinalFallback.of_mem_canonicalVerifierContinuation parameter root table adversaryResult
      result adversaryConcreteCache completion fallback htable hfinish hadversaryInvariant
        hadversaryClosed hadversaryPublished hfinalCompletion
  have hterminalValue := canonicalVerifierContinuation_value_of_mem_support parameter root
    adversaryResult result hfinish
  have hlogRuns' := hlogRuns
  rw [hterminalValue.1, hterminalValue.2] at hlogRuns'
  have hadversaryAllowed :=
    revealedChainAllowed_runSynchronizedResolved_signingTraceComputation parameter root table
      ftsSecret targetCache adversaryResult.value.1.2 completion fallback hlogRuns'
        (adversary.main ⟨root, parameter⟩) rootResult.context rootResult.remaining
          rootResult.value.2 hrootBoundary.concreteCache adversaryResult
            hrootBoundary.invariant hrootBoundary.closed hrootBoundary.published
              hrootBoundary.allowed (fun entry => id) hadversary hcompletion
                hadversaryFallback
  exact ⟨⟨adversaryConcreteCache, hadversaryInvariant, hadversaryClosed,
    hadversaryPublished, hadversaryAllowed⟩, hadversaryFallback⟩

set_option maxRecDepth 100000 in
theorem CanonicalResolvedBoundary.contradicts_canonicalVerifierTerminal
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (boundary : CanonicalResolvedBoundary parameter table adversaryResult.context
      adversaryResult.value.2
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        adversaryResult.value.1.2))
    (terminal : CanonicalVerifierTerminal parameter root table ftsSecret targetCache
      completion fallback adversaryResult) : False := by
  have hvalue := canonicalVerifierContinuation_value_of_mem_support parameter root
    adversaryResult terminal.result terminal.mem_support
  have hprobe := terminal.probe
  rw [hvalue.1] at hprobe
  apply not_verifyProbe_of_mem_canonicalVerifierContinuation parameter root table ftsSecret
    targetCache completion fallback adversaryResult boundary.concreteCache terminal.result
      terminal.table_eq terminal.mem_support boundary.invariant boundary.closed
        boundary.published boundary.allowed terminal.resultCompletion terminal.fallbackAgrees
  exact hprobe

end SphincsSecurity.Concrete.OtsProbeSimulation
