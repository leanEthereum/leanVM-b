import XmssSecurity.CappedGlobalCausalInstalledAdversary
import XmssSecurity.CappedGlobalChainHighRevealCoverage
import XmssSecurity.CappedChain.CausalRevealCoverage

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

theorem GlobalCausalRevealsCovered.globalCausalRevealResultState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered
      (globalCausalRevealResultState secretKey input state index value output) := by
  unfold XmssSecurity.CappedChain.globalCausalRevealResultState
  exact ((hcovered.recordedState secretKey input).recordReveal
    index value hindex).setCache _

theorem globalCausalLeafHashPlan_ne_reveal
    (secretKey : SecretKey) (input : HashInput) (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) :
    globalCausalLeafHashPlan secretKey input state ≠ .reveal index := by
  unfold globalCausalLeafHashPlan
  split <;> intro h <;> cases h

theorem globalCausalUncachedAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (index : GlobalChainValueIndex)
    (hplan : globalCausalUncachedAttackerHashPlan secretKey input state probe =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  cases probe with
  | none =>
      exact (globalCausalLeafHashPlan_ne_reveal
        secretKey input state index hplan).elim
  | some probe =>
      obtain ⟨predecessor, target⟩ := probe
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [globalCausalUncachedAttackerHashPlan, hrevealed] at hplan
          exact (globalCausalLeafHashPlan_ne_reveal
            secretKey input state index hplan).elim
      | some value =>
          by_cases htarget : value = target
          · subst target
            by_cases hnext : predecessor.2.2.val + 1 < chainLength
            · simp only [globalCausalUncachedAttackerHashPlan, hrevealed,
                dif_pos hnext] at hplan
              have hindex :
                  (predecessor.1, predecessor.2.1,
                    ⟨predecessor.2.2.val + 1, hnext⟩) = index :=
                GlobalCausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl, rfl⟩
            · simp only [globalCausalUncachedAttackerHashPlan, hrevealed,
                dif_neg hnext] at hplan
              exact (globalCausalLeafHashPlan_ne_reveal
                secretKey input state index hplan).elim
          · simp only [globalCausalUncachedAttackerHashPlan, hrevealed,
              if_neg htarget] at hplan
            exact (globalCausalLeafHashPlan_ne_reveal
              secretKey input state index hplan).elim

theorem globalCausalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalCausalAttackerHashPlan secretKey input state =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  unfold globalCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | some output =>
      simp only [hcache] at hplan
      cases hplan
  | none =>
      simp only [hcache] at hplan
      exact globalCausalUncachedAttackerHashPlan_reveal_has_predecessor
        secretKey input state
          (globalChainInputProbe? secretKey.parameter input) index hplan

theorem globalCausalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (covered : Set GlobalChainValueIndex)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .reveal index)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hchain, hepoch, hnext⟩ :=
    globalCausalAttackerHashPlan_reveal_has_predecessor secretKey input state
      index hplan
  apply hforward index.1 index.2.1 predecessor.2.2 index.2.2
  · rw [← hchain, ← hepoch]
    exact hcovered predecessor value hrevealed
  · change predecessor.2.2.val ≤ index.2.2.val
    omega

theorem globalCausalLazyAttackerHashStep_support_resultCovered
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyAttackerHashStep secretKey input state)) :
    GlobalCausalResultCovered covered result := by
  generalize hplan : globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      simp only [globalCausalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | redirect output =>
      simp only [globalCausalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨(hcovered.recordedState secretKey input).setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | fresh =>
      simp only [globalCausalLazyAttackerHashStep, hplan,
        mem_support_bind_iff] at hresult
      obtain ⟨hashResult, _hhashResult, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact ⟨(hcovered.recordedState secretKey input).setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | reveal index =>
      have hindex := globalCausalAttackerHashPlan_reveal_mem_of_covered
        secretKey input state index covered hplan hcovered hforward
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          constructor
          · exact hcovered.globalCausalRevealResultState secretKey input
              index value output hindex
          · intro candidate _value hmem
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact hindex
      | none =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          constructor
          · exact hcovered.globalCausalRevealResultState secretKey input
              index (truncateHash output) output hindex
          · intro candidate _value hmem
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact hindex

theorem globalCausalAttackerHashPlan_cache_none_of_noncached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (plan : GlobalCausalHashPlan)
    (hplan : globalCausalAttackerHashPlan secretKey input state = plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  unfold globalCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      simp only [hcache] at hplan
      exact (hnoncached output hplan.symm).elim

theorem globalCausalLazyAttackerHashStep_support_cache_le
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyAttackerHashStep secretKey input state)) :
    state.cache ≤ result.1.2.cache := by
  generalize hplan : globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      simp only [globalCausalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        (le_rfl : state.cache ≤ state.cache)
  | redirect output =>
      have habsent := globalCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.redirect output) hplan (by intro; simp)
      simp only [globalCausalLazyAttackerHashStep, hplan, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        QueryCache.le_cacheQuery state.cache habsent
  | fresh =>
      simp only [globalCausalLazyAttackerHashStep, hplan,
        mem_support_bind_iff] at hresult
      obtain ⟨hashResult, hhashResult, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hhashResult' : hashResult ∈ support
          ((uniformSampleImpl.withCaching input).run
            (globalCausalRecordedState secretKey input state).cache) := by
        simpa [randomOracle] using hhashResult
      simpa only [globalCausalRecordedState_cache] using
        QueryImpl.withCaching_cache_le uniformSampleImpl input
          (globalCausalRecordedState secretKey input state).cache hashResult
            hhashResult'
  | reveal index =>
      have habsent := globalCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.reveal index) hplan (by intro; simp)
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [globalCausalRevealResultState] using
            QueryCache.le_cacheQuery state.cache habsent
      | none =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [globalCausalRevealResultState] using
            QueryCache.le_cacheQuery state.cache habsent

theorem globalCausalLazyRevealSignatureChains_support_covered
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ chain ∈ chains,
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureChains request encoding chains signature
        state)) :
    GlobalCausalResultCovered covered result := by
  induction chains generalizing signature state result with
  | nil =>
      simp only [globalCausalLazyRevealSignatureChains, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      have hindex : index ∈ covered := hindices chain (by simp)
      have htailIndices : ∀ candidate ∈ chains,
          (candidate, request.epoch, encoding candidate) ∈ covered := by
        intro candidate hcandidate
        exact hindices candidate (List.mem_cons_of_mem chain hcandidate)
      cases hrevealed : state.revealed index with
      | some value =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨tail, htail, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          have htailCovered := ih
            (replaceSignatureChainValue signature chain value)
            (state.recordReveal index value)
            (hcovered.recordReveal index value hindex) htailIndices tail htail
          exact ⟨htailCovered.1, by
            intro candidate candidateValue hmem
            simp only [globalPrependRevealTrace, List.mem_cons] at hmem
            rcases hmem with hhead | htailMem
            · cases hhead
              exact hindex
            · exact htailCovered.2 candidate candidateValue htailMem⟩
      | none =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, hrest⟩ := hresult
          rw [mem_support_bind_iff] at hrest
          obtain ⟨tail, htail, hpure⟩ := hrest
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          have htailCovered := ih
            (replaceSignatureChainValue signature chain value)
            (state.recordReveal index value)
            (hcovered.recordReveal index value hindex) htailIndices tail htail
          exact ⟨htailCovered.1, by
            intro candidate candidateValue hmem
            simp only [globalPrependRevealTrace, List.mem_cons] at hmem
            rcases hmem with hhead | htailMem
            · cases hhead
              exact hindex
            · exact htailCovered.2 candidate candidateValue htailMem⟩

theorem globalCausalLazyRevealSignatureChains_support_cache_eq
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureChains request encoding chains signature
        state)) :
    result.1.2.cache = state.cache := by
  induction chains generalizing signature state result with
  | nil =>
      simp only [globalCausalLazyRevealSignatureChains, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      cases hrevealed : state.revealed index with
      | some value =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨tail, htail, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [globalPrependRevealTrace,
            GlobalCausalHashState.recordReveal] using
            ih (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value) tail htail
      | none =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, hrest⟩ := hresult
          rw [mem_support_bind_iff] at hrest
          obtain ⟨tail, htail, hpure⟩ := hrest
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [globalPrependRevealTrace,
            GlobalCausalHashState.recordReveal] using
            ih (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value) tail htail

theorem globalCausalLazyRevealSignatureChains_support_randomness_eq
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureChains request encoding chains signature
        state)) :
    result.1.1.randomness = signature.randomness := by
  induction chains generalizing signature state result with
  | nil =>
      simp only [globalCausalLazyRevealSignatureChains, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      cases hrevealed : state.revealed index with
      | some value =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨tail, htail, hpure⟩ := hresult
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          change tail.1.1.randomness = signature.randomness
          simpa only [replaceSignatureChainValue] using
            ih (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value) tail htail
      | none =>
          rw [globalCausalLazyRevealSignatureChains, hrevealed,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, hrest⟩ := hresult
          rw [mem_support_bind_iff] at hrest
          obtain ⟨tail, htail, hpure⟩ := hrest
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          change tail.1.1.randomness = signature.randomness
          simpa only [replaceSignatureChainValue] using
            ih (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value) tail htail

theorem globalCausalLazyRevealSignatureOption_support_resultCovered
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hdirect : ∀ signature encoding chain,
      signatureOption = some signature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash state.cache secretKey.parameter
          request.epoch (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureOption secretKey request signatureOption
        state)) :
    GlobalCausalResultCovered covered result := by
  cases signatureOption with
  | none =>
      simp only [globalCausalLazyRevealSignatureOption, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | some signature =>
      cases hdecode : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none =>
          simp only [globalCausalLazyRevealSignatureOption, hdecode,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
      | some encoding =>
          simp only [globalCausalLazyRevealSignatureOption, hdecode,
            support_map] at hresult
          obtain ⟨chainsResult, hchains, rfl⟩ := hresult
          exact globalCausalLazyRevealSignatureChains_support_covered
            request encoding allChains signature state covered hcovered
              (fun chain _ => hdirect signature encoding chain rfl hdecode)
              chainsResult hchains

theorem globalCausalLazyRevealSignatureOption_support_some_info
    (secretKey : SecretKey) (request : SignRequest)
    (signature : Signature) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureOption secretKey request
        (some signature) state)) :
    ∃ returnedSignature,
      result.1.1 = some returnedSignature ∧
      returnedSignature.randomness = signature.randomness ∧
      result.1.2.cache = state.cache := by
  cases hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) with
  | none =>
      simp only [globalCausalLazyRevealSignatureOption, hdecode, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨signature, rfl, rfl, rfl⟩
  | some encoding =>
      simp only [globalCausalLazyRevealSignatureOption, hdecode,
        support_map] at hresult
      obtain ⟨chainsResult, hchains, rfl⟩ := hresult
      exact ⟨chainsResult.1.1, rfl,
        globalCausalLazyRevealSignatureChains_support_randomness_eq
          request encoding allChains signature state chainsResult hchains,
        globalCausalLazyRevealSignatureChains_support_cache_eq
          request encoding allChains signature state chainsResult hchains⟩

theorem globalCausalLazyRevealSignatureOption_support_cache_eq
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazyRevealSignatureOption secretKey request signatureOption
        state)) :
    result.1.2.cache = state.cache := by
  cases signatureOption with
  | none =>
      simp only [globalCausalLazyRevealSignatureOption, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | some signature =>
      obtain ⟨_returnedSignature, _hreturned, _hrandomness, hcache⟩ :=
        globalCausalLazyRevealSignatureOption_support_some_info
          secretKey request signature state result hresult
      exact hcache

theorem globalCausalLazySigningQuery_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazySigningQuery publicKey secretKey request state)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalCausalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  have hsignedLe : state.cache ≤ signed.2 :=
    xmssRom_cache_le
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
      state.cache signed hsigned
  have hcache := globalCausalLazyRevealSignatureOption_support_cache_eq
    secretKey request signed.1 { state with cache := signed.2 } result hrest
  calc
    state.cache ≤ signed.2 := hsignedLe
    _ = result.1.2.cache := by simpa using hcache.symm

theorem globalCausalLazySigningQuery_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hdirect : ∀ signature resultCache encoding chain,
      (some signature, resultCache) ∈ support
        ((simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache) →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      (globalCausalLazySigningQuery publicKey secretKey request state)) :
    GlobalCausalResultCovered covered result := by
  unfold globalCausalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  apply globalCausalLazyRevealSignatureOption_support_resultCovered
    secretKey request signed.1 { state with cache := signed.2 }
      covered (hcovered.setCache signed.2) _ result hrest
  intro signature encoding chain hsignature hdecode
  apply hdirect signature signed.2 encoding chain
  · have heq : (some signature, signed.2) = signed := by
      apply Prod.ext
      · exact hsignature.symm
      · rfl
    rw [heq]
    exact hsigned
  · exact hdecode

theorem globalCausalLazyMappedStep_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature resultCache encoding chain,
      input = .inr request →
      (some signature, resultCache) ∈ support
        ((simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache) →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalLazyMappedStep publicKey secretKey input state)) :
    GlobalCausalResultCovered covered result := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rw [globalCausalLazyMappedStep_uniform] at hresult
      simp only [support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
    · exact globalCausalLazyAttackerHashStep_support_resultCovered
        secretKey hashInput state covered hcovered hforward result hresult
  · apply globalCausalLazySigningQuery_support_resultCovered
      publicKey secretKey request state covered hcovered
    · intro signature resultCache encoding chain hsigned hdecode
      exact hdirect request signature resultCache encoding chain rfl hsigned
        hdecode
    · exact hresult

set_option maxRecDepth 100000 in
theorem globalCausalLazySigningQuery_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex) (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (globalCausalLazySigningQuery publicKey secretKey request state)) :
    GlobalCausalResultCovered covered result := by
  unfold globalCausalLazySigningQuery at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  have hcovered' : GlobalCausalRevealsCovered covered
      { state with cache := signed.2 } := hcovered.setCache signed.2
  have hlocalDirect : ∀ signature encoding chain,
      signed.1 = some signature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash signed.2 secretKey.parameter
          request.epoch (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered := by
    intro signature encoding chain hsignature hdecode
    have hsignedSome : (some signature, signed.2) ∈ support
        ((simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache) := by
      have heq : (some signature, signed.2) = signed := by
        apply Prod.ext
        · exact hsignature.symm
        · rfl
      simpa only [heq] using hsigned
    have hinfo := globalCausalLazyRevealSignatureOption_support_some_info
      secretKey request signature { state with cache := signed.2 } result (by
        simpa only [hsignature] using hrest)
    obtain ⟨returnedSignature, hreturnedSignature, hrandomness,
      hresultCache⟩ := hinfo
    have hsignedCacheLe : signed.2 ≤ finalCache := by
      calc
        signed.2 = result.1.2.cache := by simpa using hresultCache.symm
        _ ≤ finalCache := hcacheLe
    have hstable := encodingHash_eq_of_sign_support_of_cache_le
      publicKey secretKey request state.cache signed.2 finalCache signature
        hsignedSome hsignedCacheLe
    apply hdirect returnedSignature encoding chain hreturnedSignature
    rw [hrandomness, ← hstable]
    exact hdecode
  exact globalCausalLazyRevealSignatureOption_support_resultCovered
    secretKey request signed.1 { state with cache := signed.2 }
      covered hcovered' hlocalDirect result hrest

theorem globalCausalLazyActionTracedStep_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (globalCausalLazyActionTracedStep publicKey secretKey input state)) :
    GlobalCausalResultCovered covered result := by
  unfold globalCausalLazyActionTracedStep at hresult
  rw [support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rw [globalCausalLazyMappedStep_uniform] at hmapped
      simp only [support_map] at hmapped
      obtain ⟨output, _houtput, rfl⟩ := hmapped
      exact ⟨hcovered, by
        simp [GlobalCausalTraceRevealsCovered,
          globalAttachLazyAttackerAction]⟩
    · have hmappedCovered :=
        globalCausalLazyAttackerHashStep_support_resultCovered
          secretKey hashInput state covered hcovered hforward mapped hmapped
      change GlobalCausalRevealsCovered covered mapped.1.2 ∧
        GlobalCausalTraceRevealsCovered covered mapped.2
      exact hmappedCovered
  · have hmappedCovered :=
      globalCausalLazySigningQuery_support_resultCovered_of_final
        publicKey secretKey request state covered finalCache mapped hcovered
          hcacheLe (by
            intro returnedSignature encoding chain hreturned hdecode
            apply hdirect request returnedSignature encoding chain
            · simpa [globalAttachLazyAttackerAction, hreturned]
            · exact hdecode) hmapped
    change GlobalCausalRevealsCovered covered mapped.1.2 ∧
      GlobalCausalTraceRevealsCovered covered mapped.2
    exact hmappedCovered

theorem globalCausalLazyMappedStep_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalLazyMappedStep publicKey secretKey input state)) :
    state.cache ≤ result.1.2.cache := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rw [globalCausalLazyMappedStep_uniform] at hresult
      simp only [support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact le_rfl
    · exact globalCausalLazyAttackerHashStep_support_cache_le
        secretKey hashInput state result hresult
  · exact globalCausalLazySigningQuery_support_cache_le
      publicKey secretKey request state result hresult

theorem globalCausalLazyActionTracedStep_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalLazyActionTracedStep publicKey secretKey input state)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalCausalLazyActionTracedStep at hresult
  rw [support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact globalCausalLazyMappedStep_support_cache_le
    publicKey secretKey input state mapped hmapped

end XmssSecurity.CappedChain
