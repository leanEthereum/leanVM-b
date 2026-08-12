import XmssSecurity.CausalInstalledAdversary
import XmssSecurity.ChainRevealFiltering

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def CausalRevealsCovered
    (covered : Set ChainValueIndex) (state : CausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → index ∈ covered

def ChainValueIndicesForwardClosed
    (covered : Set ChainValueIndex) : Prop :=
  ∀ epoch earlier later,
    (epoch, earlier) ∈ covered → earlier ≤ later →
      (epoch, later) ∈ covered

def CausalTraceRevealsCovered
    (covered : Set ChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  ∀ index value,
    RevealProbeOracleSimulation.ObservedAction.reveal index value ∈ trace →
      index ∈ covered

def CausalResultCovered
    (covered : Set ChainValueIndex)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  CausalRevealsCovered covered result.1.2 ∧
    CausalTraceRevealsCovered covered result.2

theorem CausalTraceRevealsCovered.append
    {covered : Set ChainValueIndex}
    {left right : RevealProbeOracleSimulation.ActionTrace ChainValueIndex}
    (hleft : CausalTraceRevealsCovered covered left)
    (hright : CausalTraceRevealsCovered covered right) :
    CausalTraceRevealsCovered covered (left ++ right) := by
  intro index value hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft index value hmem
  · exact hright index value hmem

theorem CausalRevealsCovered.setCache
    {covered : Set ChainValueIndex} {state : CausalHashState}
    (hcovered : CausalRevealsCovered covered state)
    (cache : QueryCache HashSpec) :
    CausalRevealsCovered covered { state with cache := cache } := by
  exact hcovered

theorem CausalRevealsCovered.causalRecordedState
    {covered : Set ChainValueIndex} {state : CausalHashState}
    (hcovered : CausalRevealsCovered covered state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput) :
    CausalRevealsCovered covered
      (causalRecordedState secretKey chain input state) := by
  intro index value hrevealed
  apply hcovered index value
  simpa only [causalRecordedState_revealed] using hrevealed

theorem CausalRevealsCovered.recordReveal
    {covered : Set ChainValueIndex} {state : CausalHashState}
    (hcovered : CausalRevealsCovered covered state)
    (index : ChainValueIndex) (value : Digest) (hindex : index ∈ covered) :
    CausalRevealsCovered covered (state.recordReveal index value) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · simpa [heq] using hindex
  · apply hcovered candidate candidateValue
    simpa [CausalHashState.recordReveal, Function.update_of_ne heq] using
      hrevealed

theorem CausalRevealsCovered.causalRevealResultState
    {covered : Set ChainValueIndex} {state : CausalHashState}
    (hcovered : CausalRevealsCovered covered state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (index : ChainValueIndex) (value : Digest) (output : HashOutput)
    (hindex : index ∈ covered) :
    CausalRevealsCovered covered
      (causalRevealResultState secretKey chain input state index value output) := by
  unfold XmssSecurity.causalRevealResultState
  exact ((hcovered.causalRecordedState secretKey chain input).recordReveal
    index value hindex).setCache _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem returnedChainValueIndices_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    ChainValueIndicesForwardClosed
      (returnedChainValueIndices cache secretKey log chain) := by
  intro epoch earlier later hmem hle
  change (epoch, earlier) ∈
      returnedChainValueIndices cache secretKey log chain at hmem
  change (epoch, later) ∈
    returnedChainValueIndices cache secretKey log chain
  rw [mem_returnedChainValueIndices_iff] at hmem ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit⟩ := hmem
  exact ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit.trans hle⟩

noncomputable def ReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    Set ChainValueIndex :=
  fun index => index ∈ returnedChainValueIndexList cache secretKey log chain

theorem returnedChainValueCovered_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ ReturnedChainValueCovered cache secretKey log chain ↔
      ∃ request signature encoding,
        SigningTranscript.Returned log request signature ∧
          TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter
              request.epoch
              (request.message, signature.randomness)) = some encoding ∧
          index.1 = request.epoch ∧ encoding chain ≤ index.2 := by
  exact mem_returnedChainValueIndexList_iff cache secretKey log chain index

theorem returnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    ChainValueIndicesForwardClosed
      (ReturnedChainValueCovered cache secretKey log chain) := by
  intro epoch earlier later hmem hle
  rw [returnedChainValueCovered_iff] at hmem ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit⟩ := hmem
  exact ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit.trans hle⟩

theorem returnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some encoding) :
    (request.epoch, encoding chain) ∈
      ReturnedChainValueCovered cache secretKey log chain := by
  rw [returnedChainValueCovered_iff]
  exact ⟨request, signature, encoding, hreturned, hdecode, rfl, le_rfl⟩

theorem returnedChainValueCovered_iff_mem_indices
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ ReturnedChainValueCovered cache secretKey log chain ↔
      index ∈ returnedChainValueIndices cache secretKey log chain := by
  rw [returnedChainValueCovered_iff, mem_returnedChainValueIndices_iff]

theorem returnedChainValueCovered_mem_reveals
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex)
    (hindex : index ∈
      ReturnedChainValueCovered finalCache secretKey log chain) :
    index ∈ (returnedChainValueReveals keygenCache finalCache secretKey log
      chain).map Prod.fst := by
  change index ∈ returnedChainValueIndexList finalCache secretKey log chain at hindex
  rw [returnedChainValueReveals, List.map_map]
  change index ∈
    (returnedChainValueIndexList finalCache secretKey log chain).map id
  rw [List.mem_map]
  exact ⟨index, hindex, rfl⟩

theorem causalLeafHashPlan_ne_reveal
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) :
    causalLeafHashPlan secretKey input state ≠ .reveal index := by
  unfold causalLeafHashPlan
  split <;> intro h <;> cases h

theorem causalUncachedAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest))
    (index : ChainValueIndex)
    (hplan : causalUncachedAttackerHashPlan secretKey input state probe =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧ predecessor.2.val + 1 = index.2.val := by
  cases probe with
  | none =>
      exact (causalLeafHashPlan_ne_reveal
        secretKey input state index hplan).elim
  | some probe =>
      obtain ⟨predecessor, target⟩ := probe
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [causalUncachedAttackerHashPlan, hrevealed] at hplan
          exact (causalLeafHashPlan_ne_reveal
            secretKey input state index hplan).elim
      | some value =>
          by_cases htarget : value = target
          · subst target
            by_cases hnext : predecessor.2.val + 1 < chainLength
            · simp only [causalUncachedAttackerHashPlan, hrevealed,
                dif_pos hnext] at hplan
              have hindex :
                  (predecessor.1, ⟨predecessor.2.val + 1, hnext⟩) = index :=
                CausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl⟩
            · simp only [causalUncachedAttackerHashPlan, hrevealed,
                dif_neg hnext] at hplan
              exact (causalLeafHashPlan_ne_reveal
                secretKey input state index hplan).elim
          · simp only [causalUncachedAttackerHashPlan, hrevealed,
              if_neg htarget] at hplan
            exact (causalLeafHashPlan_ne_reveal
              secretKey input state index hplan).elim

theorem causalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧ predecessor.2.val + 1 = index.2.val := by
  have hcache := causalAttackerHashPlan_reveal_cache_none
    secretKey chain input state index hplan
  apply causalUncachedAttackerHashPlan_reveal_has_predecessor
    secretKey input state
      (chainInputProbe? secretKey.parameter chain input) index
  simpa only [causalAttackerHashPlan, hcache] using hplan

theorem causalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (covered : Set ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hepoch, hnext⟩ :=
    causalAttackerHashPlan_reveal_has_predecessor
      secretKey chain input state index hplan
  have hpredecessor := hcovered predecessor value hrevealed
  apply hforward index.1 predecessor.2 index.2
  · rw [← hepoch]
    exact hpredecessor
  · change predecessor.2.val ≤ index.2.val
    omega

theorem causalLazyAttackerHashStep_support_revealsCovered
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyAttackerHashStep secretKey chain input state)) :
    CausalRevealsCovered covered result.1.2 := by
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      simp only [causalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcovered.causalRecordedState secretKey chain input
  | redirect output =>
      simp only [causalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact (hcovered.causalRecordedState secretKey chain input).setCache _
  | fresh =>
      simp only [causalLazyAttackerHashStep, hplan, mem_support_bind_iff]
        at hresult
      obtain ⟨hashResult, _hhashResult, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact (hcovered.causalRecordedState secretKey chain input).setCache _
  | reveal index =>
      have hindex := causalAttackerHashPlan_reveal_mem_of_covered
        secretKey chain input state index covered hplan hcovered hforward
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact hcovered.causalRevealResultState secretKey chain input
            index value output hindex
      | none =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact hcovered.causalRevealResultState secretKey chain input
            index (truncateHash output) output hindex

theorem causalLazyAttackerHashStep_support_resultCovered
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyAttackerHashStep secretKey chain input state)) :
    CausalResultCovered covered result := by
  constructor
  · exact causalLazyAttackerHashStep_support_revealsCovered
      secretKey chain input state covered hcovered hforward result hresult
  · generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
    cases plan with
    | cached output =>
        simp only [causalLazyAttackerHashStep, hplan, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        simp [CausalTraceRevealsCovered]
    | redirect output =>
        simp only [causalLazyAttackerHashStep, hplan, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        simp [CausalTraceRevealsCovered]
    | fresh =>
        simp only [causalLazyAttackerHashStep, hplan, mem_support_bind_iff]
          at hresult
        obtain ⟨hashResult, _hhashResult, hpure⟩ := hresult
        simp only [support_pure, Set.mem_singleton_iff] at hpure
        subst result
        simp [CausalTraceRevealsCovered]
    | reveal index =>
        have hindex := causalAttackerHashPlan_reveal_mem_of_covered
          secretKey chain input state index covered hplan hcovered hforward
        cases hrevealed : state.revealed index with
        | some value =>
            simp only [causalLazyAttackerHashStep, hplan, hrevealed,
              mem_support_bind_iff] at hresult
            obtain ⟨output, _houtput, hpure⟩ := hresult
            simp only [support_pure, Set.mem_singleton_iff] at hpure
            subst result
            intro candidate _value hmem
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact hindex
        | none =>
            simp only [causalLazyAttackerHashStep, hplan, hrevealed,
              mem_support_bind_iff] at hresult
            obtain ⟨output, _houtput, hpure⟩ := hresult
            simp only [support_pure, Set.mem_singleton_iff] at hpure
            subst result
            intro candidate _value hmem
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact hindex

theorem causalLazyAttackerHashStep_support_cache_le
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyAttackerHashStep secretKey chain input state)) :
    state.cache ≤ result.1.2.cache := by
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      simp only [causalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | redirect output =>
      have habsent := causalAttackerHashPlan_noncached_cache_none
        secretKey chain input state (.redirect output) hplan (by simp)
      simp only [causalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa using QueryCache.le_cacheQuery state.cache habsent
  | fresh =>
      have habsent := causalAttackerHashPlan_noncached_cache_none
        secretKey chain input state .fresh hplan (by simp)
      simp only [causalLazyAttackerHashStep, hplan, mem_support_bind_iff]
        at hresult
      obtain ⟨hashResult, hhashResult, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hhashResult' : hashResult ∈ support
          ((uniformSampleImpl.withCaching input).run state.cache) := by
        simpa [randomOracle] using hhashResult
      exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
        hashResult hhashResult'
  | reveal index =>
      have habsent := causalAttackerHashPlan_reveal_cache_none
        secretKey chain input state index hplan
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [causalRevealResultState] using
            QueryCache.le_cacheQuery state.cache habsent
      | none =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [causalRevealResultState] using
            QueryCache.le_cacheQuery state.cache habsent

theorem causalLazyRevealSignatureOption_support_resultCovered
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hdirect : ∀ signature encoding,
      signatureOption = some signature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash state.cache secretKey.parameter
          request.epoch (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyRevealSignatureOption secretKey chain request
        signatureOption state)) :
    CausalResultCovered covered result := by
  cases signatureOption with
  | none =>
      simp only [causalLazyRevealSignatureOption, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | some signature =>
      cases hdecode : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none =>
          simp only [causalLazyRevealSignatureOption, hdecode, support_pure,
            Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
      | some encoding =>
          have hindex : (request.epoch, encoding chain) ∈ covered :=
            hdirect signature encoding rfl hdecode
          cases hrevealed : state.revealed
              (request.epoch, encoding chain) with
          | some value =>
              simp only [causalLazyRevealSignatureOption, hdecode, hrevealed,
                support_pure, Set.mem_singleton_iff] at hresult
              subst result
              constructor
              · exact hcovered.recordReveal _ _ hindex
              · intro candidate _value hmem
                simp only [List.mem_singleton] at hmem
                cases hmem
                exact hindex
          | none =>
              simp only [causalLazyRevealSignatureOption, hdecode, hrevealed,
                mem_support_bind_iff] at hresult
              obtain ⟨value, _hvalue, hpure⟩ := hresult
              simp only [support_pure, Set.mem_singleton_iff] at hpure
              subst result
              constructor
              · exact hcovered.recordReveal _ _ hindex
              · intro candidate _candidateValue hmem
                simp only [List.mem_singleton] at hmem
                cases hmem
                exact hindex

theorem causalLazySigningQuery_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hdirect : ∀ signature resultCache encoding,
      (some signature, resultCache) ∈ support ((simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch
          request.message)).run state.cache) →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazySigningQuery publicKey secretKey chain request state)) :
    CausalResultCovered covered result := by
  unfold causalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  apply causalLazyRevealSignatureOption_support_resultCovered
    secretKey chain request signed.1 { state with cache := signed.2 }
      covered (hcovered.setCache signed.2) _ result hrest
  intro signature encoding hsignature hdecode
  apply hdirect signature signed.2 encoding
  · have heq : (some signature, signed.2) = signed := by
      apply Prod.ext
      · exact hsignature.symm
      · rfl
    rw [heq]
    exact hsigned
  · exact hdecode

theorem encodingHash_eq_of_sign_support_of_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hsigned : (some signature, resultCache) ∈ support ((simulateQ xmssRomImpl
      (Concrete.scheme.sign publicKey secretKey request.epoch
        request.message)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.encodingHash resultCache secretKey.parameter
        request.epoch (request.message, signature.randomness) =
      Concrete.CacheView.encodingHash largerCache secretKey.parameter
        request.epoch (request.message, signature.randomness) := by
  obtain ⟨output, hcached⟩ :=
    Concrete.sign_success_encodingInput_cached
      publicKey secretKey request initialCache resultCache signature hsigned
  have hcachedLarger := hle hcached
  unfold Concrete.CacheView.encodingHash
  rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]

theorem causalLazyRevealSignatureOption_support_some_info
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signature : Signature) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyRevealSignatureOption secretKey chain request
        (some signature) state)) :
    ∃ returnedSignature,
      result.1.1 = some returnedSignature ∧
      returnedSignature.randomness = signature.randomness ∧
      result.1.2.cache = state.cache := by
  cases hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) with
  | none =>
      simp only [causalLazyRevealSignatureOption, hdecode, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨signature, rfl, rfl, rfl⟩
  | some encoding =>
      cases hrevealed : state.revealed (request.epoch, encoding chain) with
      | some value =>
          simp only [causalLazyRevealSignatureOption, hdecode, hrevealed,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨replaceSignatureChainValue signature chain value,
            rfl, rfl, rfl⟩
      | none =>
          simp only [causalLazyRevealSignatureOption, hdecode, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact ⟨replaceSignatureChainValue signature chain value,
            rfl, rfl, rfl⟩

theorem causalLazyRevealSignatureOption_support_cache_eq
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazyRevealSignatureOption secretKey chain request
        signatureOption state)) :
    result.1.2.cache = state.cache := by
  cases signatureOption with
  | none =>
      simp only [causalLazyRevealSignatureOption, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | some signature =>
      obtain ⟨_returnedSignature, _hreturned, _hrandomness, hcache⟩ :=
        causalLazyRevealSignatureOption_support_some_info
          secretKey chain request signature state result hresult
      exact hcache

theorem causalLazySigningQuery_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (causalLazySigningQuery publicKey secretKey chain request state)) :
    state.cache ≤ result.1.2.cache := by
  unfold causalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  have hsignedLe : state.cache ≤ signed.2 :=
    xmssRom_cache_le
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
      state.cache signed hsigned
  have hcache := causalLazyRevealSignatureOption_support_cache_eq
    secretKey chain request signed.1 { state with cache := signed.2 }
      result hrest
  calc
    state.cache ≤ signed.2 := hsignedLe
    _ = result.1.2.cache := by simpa using hcache.symm

set_option maxRecDepth 100000 in
theorem causalLazySigningQuery_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (causalLazySigningQuery publicKey secretKey chain request state)) :
    CausalResultCovered covered result := by
  unfold causalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  have hcovered' : CausalRevealsCovered covered
      { state with cache := signed.2 } := by
    intro index value hrevealed
    exact hcovered index value hrevealed
  have hlocalDirect : ∀ signature encoding,
      signed.1 = some signature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash signed.2 secretKey.parameter
          request.epoch (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered := by
    intro signature encoding hsignature hdecode
    have hsignedSome : (some signature, signed.2) ∈ support ((simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch
          request.message)).run state.cache) := by
      have heq : (some signature, signed.2) = signed := by
        apply Prod.ext
        · exact hsignature.symm
        · rfl
      simpa only [heq] using hsigned
    have hinfo := causalLazyRevealSignatureOption_support_some_info
      secretKey chain request signature { state with cache := signed.2 } result (by
        simpa only [hsignature] using hrest)
    obtain ⟨returnedSignature, hreturnedSignature, hrandomness, hresultCache⟩ := hinfo
    have hsignedCacheLe : signed.2 ≤ finalCache := by
      calc
        signed.2 = result.1.2.cache := by simpa using hresultCache.symm
        _ ≤ finalCache := hcacheLe
    have hstable := encodingHash_eq_of_sign_support_of_cache_le
      publicKey secretKey request state.cache signed.2 finalCache signature
        hsignedSome hsignedCacheLe
    apply hdirect returnedSignature encoding hreturnedSignature
    rw [hrandomness, ← hstable]
    exact hdecode
  exact causalLazyRevealSignatureOption_support_resultCovered
    secretKey chain request signed.1 { state with cache := signed.2 }
      covered hcovered' hlocalDirect result hrest

theorem causalLazyMappedStep_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature resultCache encoding,
      input = .inr request →
      (some signature, resultCache) ∈ support ((simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch
          request.message)).run state.cache) →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (result : ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyMappedStep publicKey secretKey chain input state)) :
    CausalResultCovered covered result := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rw [causalLazyMappedStep_uniform] at hresult
      simp only [support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
    · exact causalLazyAttackerHashStep_support_resultCovered
        secretKey chain hashInput state covered hcovered hforward result hresult
  · apply causalLazySigningQuery_support_resultCovered
      publicKey secretKey chain request state covered hcovered
    · intro signature resultCache encoding hsigned hdecode
      exact hdirect request signature resultCache encoding rfl hsigned hdecode
    · exact hresult

theorem causalLazyActionTracedStep_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature resultCache encoding,
      input = .inr request →
      (some signature, resultCache) ∈ support ((simulateQ xmssRomImpl
        (Concrete.scheme.sign publicKey secretKey request.epoch
          request.message)).run state.cache) →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyActionTracedStep publicKey secretKey chain input state)) :
    CausalResultCovered covered result := by
  unfold causalLazyActionTracedStep at hresult
  rw [support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact causalLazyMappedStep_support_resultCovered
    publicKey secretKey chain input state covered hcovered hforward hdirect
      mapped hmapped

set_option maxRecDepth 100000 in
theorem causalLazyActionTracedStep_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (causalLazyActionTracedStep publicKey secretKey chain input state)) :
    CausalResultCovered covered result := by
  unfold causalLazyActionTracedStep at hresult
  rw [support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · apply causalLazyMappedStep_support_resultCovered
        publicKey secretKey chain (.inl (.inl n)) state covered hcovered
          hforward
      · intro candidateRequest signature resultCache encoding heq
        cases heq
      · exact hmapped
    · apply causalLazyMappedStep_support_resultCovered
        publicKey secretKey chain (.inl (.inr hashInput)) state covered
          hcovered hforward
      · intro candidateRequest signature resultCache encoding heq
        cases heq
      · exact hmapped
  · apply causalLazySigningQuery_support_resultCovered_of_final
      publicKey secretKey chain request state covered finalCache mapped
        hcovered hcacheLe
    · intro returnedSignature encoding hreturned hdecode
      apply hdirect request returnedSignature encoding
      · simpa [attachLazyAttackerAction, hreturned]
      · exact hdecode
    · exact hmapped

theorem causalLazyMappedStep_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyMappedStep publicKey secretKey chain input state)) :
    state.cache ≤ result.1.2.cache := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rw [causalLazyMappedStep_uniform] at hresult
      simp only [support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact le_rfl
    · exact causalLazyAttackerHashStep_support_cache_le
        secretKey chain hashInput state result hresult
  · exact causalLazySigningQuery_support_cache_le
      publicKey secretKey chain request state result hresult

theorem causalLazyActionTracedStep_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyActionTracedStep publicKey secretKey chain input state)) :
    state.cache ≤ result.1.2.cache := by
  unfold causalLazyActionTracedStep at hresult
  rw [support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact causalLazyMappedStep_support_cache_le
    publicKey secretKey chain input state mapped hmapped

end XmssSecurity
