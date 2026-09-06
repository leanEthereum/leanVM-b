import SphincsSecurity.Proof.OtsProbeNativeParentTerminal

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem actualRetainedGameAfterTable_signing_support
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hresult : result ∈ support (actualRetainedGameAfterTable adversary parameter ftsSecret table)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, tableOtsSecret table, ftsSecret⟩
    ∃ initialCache adversaryCache : QueryCache HashSpec,
      (((result.1.2.1.1, result.1.2.1.2), adversaryCache) ∈ support
        ((simulateQ romImpl
          ((simulateQ (forwardOracles + signingOracle scheme secretKey)
            (adversary.main ⟨result.1.1, parameter⟩)).run)).run initialCache)) ∧
      adversaryCache ≤ result.2 := by
  rw [actualRetainedGameAfterTable, mem_support_bind_iff] at hresult
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨restResult, finalCache⟩, hrest, hfinish⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinish
  subst result
  rw [simulateQ_unloggedMapped_retainedGameRestComputation,
    StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, log⟩, adversaryCache⟩, hprefix, hverify⟩ := hrest
  rw [StateT.run_bind, mem_support_bind_iff] at hverify
  obtain ⟨⟨verified, verifyCache⟩, hverify, hreturn⟩ := hverify
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hreturn
  rcases hreturn with ⟨hrestResult, hfinalCache⟩
  subst restResult
  subst finalCache
  refine ⟨rootCache, adversaryCache, ?_, ?_⟩
  · change ((forgery, log), adversaryCache) ∈ support
      ((simulateQ (unloggedMappedAdversaryImpl
        ⟨parameter, root, tableOtsSecret table, ftsSecret⟩)
        (FtsProbeSimulation.signingTraceComputation (adversary.main ⟨root, parameter⟩))).run rootCache) at hprefix
    rw [FtsProbeSimulation.simulateQ_unloggedMapped_signingTraceComputation] at hprefix
    exact hprefix
  · exact simulateQ_romImpl_cache_le _ adversaryCache (verified, verifyCache) hverify

def NativeUncoveredFtsWitness (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache)) : Prop :=
  let cache := ordinaryQueryCache result.value.2
  let root := result.value.1.1
  let forgery := result.value.1.2.1.1
  let log := result.value.1.2.1.2
  let secretKey : SecretKey := ⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest) (tree : FtsTree),
    cache.AgreesWithFn f ∧
      evalWithAnswerFn f (messageDigest parameter root forgery.message forgery.signature.randomness) = digest ∧
      Admissible digest ∧
      ¬FtsProbeSimulation.CoveredByLog f cache secretKey log
        (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree)) ∧
      forgery.signature.ftsSecret tree = ftsSecret (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) ∧
      cache (tweakableHashInput parameter
        (.ftsLeaf (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)))
        (digestBytes (forgery.signature.ftsSecret tree))) ≠ none

theorem nativeUncoveredFtsWitness_of_canonical_relation
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (native : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hactual : actual ∈ support (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hvalue : native.value.1 = actual.1)
    (hinvariant : ResolvedContextInvariant parameter table native.context (ordinaryQueryCache native.value.2) actual.2)
    (hwitness : FtsProbeSimulation.RetainedUncoveredFtsSecretWitness parameter
      (tableOtsSecret (extendStartTable table)) (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) actual) :
    NativeUncoveredFtsWitness parameter table ftsSecret native := by
  rcases hwitness with ⟨f, digest, hf, hdigest, hadmissible, tree, huncovered, hsecret, hcached⟩
  obtain ⟨initialCache, adversaryCache, hprefix, hle⟩ :=
    actualRetainedGameAfterTable_signing_support adversary parameter ftsSecret (extendStartTable table) actual hactual
  have hpartition := hinvariant.2.2.2.2
  have hcacheLe : ordinaryQueryCache native.value.2 ≤ actual.2 := hpartition.1
  unfold NativeUncoveredFtsWitness
  dsimp only
  rw [hvalue]
  refine ⟨f, digest, tree, fun _ _ h => hf (hcacheLe h), hdigest, hadmissible, ?_, hsecret, ?_⟩
  · intro hcovered
    exact huncovered ((hcovered.mono_cache hcacheLe).signedFtsLeaf hprefix hle hf)
  · rw [hpartition.eq_of_stable hinvariant.2.2.2.1 _
      (stableOrdinaryInput_tweakableHashInput parameter _ _ (by trivial) (by simp) (by simp) (by simp))]
    exact hcached

end SphincsSecurity.Concrete.OtsProbeSimulation
