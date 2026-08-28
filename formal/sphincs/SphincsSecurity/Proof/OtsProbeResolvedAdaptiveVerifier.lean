import SphincsSecurity.Proof.OtsProbeResolvedAdaptivePublication

/-!
# Canonical verifier boundary for adaptive one-time probes
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem canonicalVerifierContinuation_value_of_mem_support
    (parameter : PublicParameter) (root : Digest)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (hresult : some result ∈ support
      (canonicalVerifierContinuation parameter root (some adversaryResult))) :
    result.value.1.1 = root ∧ result.value.1.2.1 = adversaryResult.value.1 := by
  simp only [canonicalVerifierContinuation] at hresult
  unfold canonicalVerifierFinish at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨verifierOption, _hverifier, hfinish⟩ := hresult
  cases verifierOption with
  | none => simp at hfinish
  | some verifierResult =>
      simp [runResolvedFromTable] at hfinish
      subst result
      exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem DeferredCompletion.of_mem_canonicalVerifierContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (htable : adversaryResult.table = table)
    (hresult : some result ∈ support
      (canonicalVerifierContinuation parameter root (some adversaryResult)))
    (hconsistent : adversaryResult.context.ValuesConsistent)
    (hstarts : StartTableAgrees adversaryResult.context.state table)
    (hcompletion : DeferredCompletion table result.context completion) :
    DeferredCompletion table adversaryResult.context completion := by
  simp only [canonicalVerifierContinuation] at hresult
  rw [htable] at hresult
  unfold canonicalVerifierFinish at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨verifierOption, hverifier, hfinish⟩ := hresult
  cases verifierOption with
  | none => simp at hfinish
  | some verifierResult =>
      simp [runResolvedFromTable] at hfinish
      subst result
      exact hcompletion.of_mem_runResolvedFromTable
        ((simulateQ (probingRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩
            adversaryResult.value.1.1.message
              adversaryResult.value.1.1.signature)).run adversaryResult.value.2)
        adversaryResult.context adversaryResult.remaining table verifierResult
          completion hconsistent hstarts hverifier

theorem CacheAgreesWithFnOffTable.of_mem_canonicalVerifierContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (adversaryConcreteCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (htable : adversaryResult.table = table)
    (hresult : some result ∈ support
      (canonicalVerifierContinuation parameter root (some adversaryResult)))
    (hinvariant : ResolvedContextInvariant parameter table adversaryResult.context
      (ordinaryQueryCache adversaryResult.value.2) adversaryConcreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table adversaryResult.context
      adversaryConcreteCache)
    (hpublished : PublishedValues adversaryResult.context.state)
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache adversaryResult.value.2) fallback := by
  have hverifierRel := reachableResolvedCouples_canonicalVerifierFinish parameter root table
    adversaryResult.value.1 adversaryResult.context adversaryResult.remaining
      adversaryResult.value.2 adversaryConcreteCache hinvariant hclosed hpublished
  have hrun : some result ∈ support
      (runResolvedFromTable adversaryResult.context adversaryResult.remaining table
        ((canonicalVerifierFinish parameter root adversaryResult.value.1).run
          adversaryResult.value.2)) := by
    simpa only [canonicalVerifierContinuation, htable] using hresult
  exact CacheAgreesWithFnOffTable.of_reachableRelTriple hverifierRel hinvariant hrun
    hcompletion hfallback (fun value finalCache hright =>
      concreteVerifierFinish_cache_le parameter root adversaryResult.value.1
        adversaryConcreteCache (value, finalCache) hright)

set_option maxRecDepth 100000 in
theorem not_verifyProbe_of_mem_canonicalVerifierContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (adversaryResult : ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))
    (adversaryConcreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (htable : adversaryResult.table = table)
    (hresult : some result ∈ support
      (canonicalVerifierContinuation parameter root (some adversaryResult)))
    (hinvariant : ResolvedContextInvariant parameter table adversaryResult.context
      (ordinaryQueryCache adversaryResult.value.2) adversaryConcreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table adversaryResult.context
      adversaryConcreteCache)
    (hpublished : PublishedValues adversaryResult.context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        adversaryResult.value.1.2)
      adversaryResult.context.state)
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hprobe : VerifyProbeWitness (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, root,
        fun lay tree leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
        ftsSecret⟩ : SecretKey)
      result.value.1.2.1.2 result.value.1.2.1.1.message
        result.value.1.2.1.1.signature) : False := by
  simp only [canonicalVerifierContinuation] at hresult
  rw [htable] at hresult
  unfold canonicalVerifierFinish at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨verifierOption, hverifier, hfinish⟩ := hresult
  cases verifierOption with
  | none => simp at hfinish
  | some verifierResult =>
      simp [runResolvedFromTable] at hfinish
      subst result
      exact not_verifyProbe_of_mem_runResolved_verifier parameter table ftsSecret
        targetCache root adversaryResult.value.1.1 adversaryResult.value.1.2 completion
          fallback adversaryResult.context adversaryResult.remaining adversaryResult.value.2
            adversaryConcreteCache verifierResult hinvariant hclosed hpublished hallowed
              hverifier hcompletion hfallback hprobe

end SphincsSecurity.Concrete.OtsProbeSimulation
