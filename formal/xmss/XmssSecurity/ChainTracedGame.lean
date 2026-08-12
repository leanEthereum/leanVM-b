import XmssSecurity.ChainRevealFiltering

open OracleComp OracleSpec

namespace XmssSecurity

def actionTraceOutcome
    (publicKey : PublicKey) (secretKey : SecretKey)
    (result : (Forgery × Bool) × AttackerActionTrace) : GameOutcome :=
  ⟨publicKey, secretKey, result.1.1, result.2.toSigningLog, result.1.2⟩

noncomputable def detailedGameAfterKeygenWithActionTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp ((GameOutcome × QueryCache HashSpec) × AttackerActionTrace) :=
  (fun result => ((actionTraceOutcome publicKey secretKey result.1, result.2), result.1.2)) <$>
    (simulateQ xmssRomImpl
      (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey)).run initialCache

theorem detailedGameAfterKeygenWithActionTrace_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    Prod.fst <$> detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey initialCache =
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run initialCache := by
  have hsource := sourceActionTracedDetailedGameAfterKeygen_log_projection adversary
    publicKey secretKey
  have hsimulated := congrArg
    (fun computation => (simulateQ xmssRomImpl computation).run initialCache) hsource
  simpa [detailedGameAfterKeygenWithActionTrace, actionTraceOutcome,
    simulateQ_map, StateT.run_map, Functor.map_map, Function.comp_def] using hsimulated

theorem detailedGameAfterKeygenWithActionTrace_support_info
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome × QueryCache HashSpec) × AttackerActionTrace)
    (hresult : result ∈ support
      (detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey initialCache)) :
    result.1.1.publicKey = publicKey ∧
      result.1.1.secretKey = secretKey ∧
      result.1.1.signingLog = result.2.toSigningLog ∧
      (((result.1.1.forgery, result.1.1.verified), result.2), result.1.2) ∈ support
        ((simulateQ xmssRomImpl
          (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey)).run
            initialCache) ∧
      ((result.1.1.forgery, result.1.1.verified), result.2) ∈ support
        (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey) := by
  unfold detailedGameAfterKeygenWithActionTrace at hresult
  rw [support_map] at hresult
  obtain ⟨sourceResult, hsourceRun, rfl⟩ := hresult
  refine ⟨rfl, rfl, rfl, hsourceRun, ?_⟩
  apply support_simulateQ_run'_subset xmssRomImpl
    (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey) initialCache
  rw [StateT.run'_eq, support_map]
  exact ⟨sourceResult, hsourceRun, rfl⟩

noncomputable def detailedGameWithKeygenCacheAndActionTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  let execution ← detailedGameAfterKeygenWithActionTrace adversary keyResult.1.1
    keyResult.1.2 keyResult.2
  pure ((keyResult, execution.1), execution.2)

theorem detailedGameWithKeygenCacheAndActionTrace_projection
    (adversary : Adversary Concrete.scheme) :
    Prod.fst <$> detailedGameWithKeygenCacheAndActionTrace adversary =
      detailedGameWithKeygenCache adversary := by
  unfold detailedGameWithKeygenCacheAndActionTrace detailedGameWithKeygenCache
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← detailedGameAfterKeygenWithActionTrace_projection adversary keyResult.1.1
    keyResult.1.2 keyResult.2]
  simp [Functor.map_map]

theorem detailedGameWithKeygenCacheAndActionTrace_support_info
    (adversary : Adversary Concrete.scheme)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary)) :
    result.1.1 ∈ support ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) ∧
      result.1.2.1.publicKey = result.1.1.1.1 ∧
      result.1.2.1.secretKey = result.1.1.1.2 ∧
      result.1.2.1.signingLog = result.2.toSigningLog ∧
      ((result.1.2.1.forgery, result.1.2.1.verified), result.2) ∈ support
        (sourceActionTracedDetailedGameAfterKeygen adversary result.1.1.1.1
          result.1.1.1.2) := by
  unfold detailedGameWithKeygenCacheAndActionTrace at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeyResult, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨execution, hexecution, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  obtain ⟨hpublic, hsecret, hlog, _hrun, hsource⟩ :=
    detailedGameAfterKeygenWithActionTrace_support_info adversary keyResult.1.1
      keyResult.1.2 keyResult.2 execution hexecution
  exact ⟨hkeyResult, hpublic, hsecret, hlog, hsource⟩

theorem detailedGameWithKeygenCacheAndActionTrace_unrevealedProbes_length_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary))
    (chain : ChainIndex) (encoding : Encoding) :
    (unrevealedChainValueProbes result.1.2.2 result.1.2.1.secretKey
      result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding).length ≤ q := by
  obtain ⟨hkeygen, _hpublic, hsecret, _hlog, hsource⟩ :=
    detailedGameWithKeygenCacheAndActionTrace_support_info adversary result hresult
  have hlength := traced_unrevealedChainValueProbes_length_le q adversary hbound
    result.1.1 hkeygen
    ((result.1.2.1.forgery, result.1.2.1.verified), result.2) hsource
    result.1.2.2 result.1.2.1.signingLog chain encoding
  simpa [hsecret] using hlength

theorem WinningOutcomeChainValueHasKeygenOrigin.readMany_of_mem_actionTracedGame
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary))
    (chain : ChainIndex)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1 chain) :
    ∃ encoding,
      let probe : ChainValueIndex × Digest :=
        ((result.1.2.1.forgery.epoch, encoding chain),
          result.1.2.1.forgery.signature.chainValue chain)
      let probes := unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
        result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding
      IndexedHiddenValue.readMany
          (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain) q
          (IndexedHiddenValue.listStrategy probe probes) = true ∧
        IndexedHiddenValue.AvoidsReveals
          (returnedChainValueReveals result.1.1.2 result.1.2.2 result.1.1.1.2
            result.1.2.1.signingLog chain)
          (IndexedHiddenValue.listStrategy probe probes) := by
  obtain ⟨_hkeygen, _hpublic, hsecret, _hlog, _hsource⟩ :=
    detailedGameWithKeygenCacheAndActionTrace_support_info adversary result hresult
  apply horigin.readMany_unrevealed_eq_true result.1.1.2 result.1.2.2
    result.1.1.1.2 result.1.2.1 chain result.2 q hsecret
  intro encoding
  have hlength := detailedGameWithKeygenCacheAndActionTrace_unrevealedProbes_length_le
    q adversary hbound result hresult chain encoding
  simpa [hsecret] using hlength

end XmssSecurity
