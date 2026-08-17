import XmssSecurity.CappedGlobalChainHighWholeGame

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def GlobalCausalRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → index ∈ covered

def GlobalCausalTraceRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  ∀ index value,
    RevealProbeOracleSimulation.ObservedAction.reveal index value ∈ trace →
      index ∈ covered

def GlobalCausalResultCovered
    (covered : Set GlobalChainValueIndex)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) : Prop :=
  GlobalCausalRevealsCovered covered result.1.2 ∧
    GlobalCausalTraceRevealsCovered covered result.2

def GlobalChainValueIndicesForwardClosed
    (covered : Set GlobalChainValueIndex) : Prop :=
  ∀ chain epoch earlier later,
    (chain, epoch, earlier) ∈ covered → earlier ≤ later →
      (chain, epoch, later) ∈ covered

theorem GlobalCausalTraceRevealsCovered.append
    {covered : Set GlobalChainValueIndex}
    {left right : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex}
    (hleft : GlobalCausalTraceRevealsCovered covered left)
    (hright : GlobalCausalTraceRevealsCovered covered right) :
    GlobalCausalTraceRevealsCovered covered (left ++ right) := by
  intro index value hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft index value hmem
  · exact hright index value hmem

theorem GlobalCausalRevealsCovered.setCache
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (cache : QueryCache HashSpec) :
    GlobalCausalRevealsCovered covered { state with cache := cache } := by
  exact hcovered

theorem GlobalCausalRevealsCovered.recordedState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalRevealsCovered covered
      (globalCausalRecordedState secretKey input state) := by
  intro index value hrevealed
  apply hcovered index value
  simpa only [globalCausalRecordedState_revealed] using hrevealed

theorem GlobalCausalRevealsCovered.recordReveal
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (index : GlobalChainValueIndex) (value : Digest)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered (state.recordReveal index value) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · simpa [heq] using hindex
  · apply hcovered candidate candidateValue
    simpa [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] using hrevealed

theorem GlobalCausalRevealsCovered.revealResultState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered
      (globalFilteredCausalRevealResultState secretKey input state index value
        output) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · subst candidate
    exact hindex
  · apply hcovered candidate candidateValue
    simpa [globalFilteredCausalRevealResultState,
      Function.update_of_ne heq] using hrevealed

noncomputable def GlobalReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Set GlobalChainValueIndex :=
  fun index =>
    index.2 ∈ ReturnedChainValueCovered cache secretKey log index.1

theorem globalReturnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) :
    GlobalChainValueIndicesForwardClosed
      (GlobalReturnedChainValueCovered cache secretKey log) := by
  intro chain epoch earlier later hmem hle
  exact returnedChainValueCovered_forwardClosed cache secretKey log chain
    epoch earlier later hmem hle

theorem globalReturnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (request : SignRequest)
    (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some encoding)
    (chain : ChainIndex) :
    (chain, request.epoch, encoding chain) ∈
      GlobalReturnedChainValueCovered cache secretKey log := by
  exact returnedChainValueCovered_contains_returned cache secretKey log chain
    request signature encoding hreturned hdecode

theorem globalReturnedChainValueCovered_mem_reveals
    (keygenCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey) (log : QueryLog SigningSpec)
    (index : GlobalChainValueIndex)
    (hindex : index ∈
      GlobalReturnedChainValueCovered finalCache secretKey log) :
    index ∈ (globalReturnedChainValueReveals keygenCache finalCache
      secretKey log).map Prod.fst := by
  rw [mem_globalReturnedChainValueReveals_fst_iff]
  exact returnedChainValueCovered_mem_reveals keygenCache finalCache secretKey
    log index.1 index.2 hindex

theorem globalReturnedChainValueCovered_of_comparableCaches
    (parameter : PublicParameter)
    (leftCache rightCache : QueryCache HashSpec)
    (leftSecret rightSecret : SecretKey)
    (leftLog rightLog : QueryLog SigningSpec)
    (hleftParameter : leftSecret.parameter = parameter)
    (hrightParameter : rightSecret.parameter = parameter)
    (hlogs : rightLog = leftLog)
    (hcaches : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (index : GlobalChainValueIndex)
    (hindex : index ∈
      GlobalReturnedChainValueCovered rightCache rightSecret rightLog) :
    index ∈ GlobalReturnedChainValueCovered leftCache leftSecret
      leftLog := by
  change index.2 ∈ ReturnedChainValueCovered rightCache rightSecret
    rightLog index.1 at hindex
  change index.2 ∈ ReturnedChainValueCovered leftCache leftSecret
    leftLog index.1
  rw [returnedChainValueCovered_iff] at hindex ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode, hepoch,
    hdigit⟩ := hindex
  have hhash :
      Concrete.CacheView.encodingHash leftCache leftSecret.parameter
          request.epoch (request.message, signature.randomness) =
        Concrete.CacheView.encodingHash rightCache rightSecret.parameter
          request.epoch (request.message, signature.randomness) := by
    rw [hleftParameter, hrightParameter]
    unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
    rw [hcaches _ ⟨request.epoch, request.message, signature.randomness,
      rfl⟩]
  refine ⟨request, signature, encoding, ?_, ?_, hepoch, hdigit⟩
  · simpa [hlogs] using hreturned
  · rw [hhash]
    exact hdecode

theorem globalFilteredCausalLeafHashPlan_ne_reveal
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    globalFilteredCausalLeafHashPlan secretKey input state ≠ .reveal index := by
  unfold globalFilteredCausalLeafHashPlan
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> intro h <;> cases h

theorem globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalUncachedAttackerHashPlan secretKey input state
      probe = .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  cases probe with
  | none =>
      exact (globalFilteredCausalLeafHashPlan_ne_reveal secretKey input state
        index hplan).elim
  | some probe =>
      obtain ⟨predecessor, target⟩ := probe
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [globalFilteredCausalUncachedAttackerHashPlan,
            hrevealed] at hplan
          split at hplan <;> cases hplan
      | some value =>
          by_cases htarget : value = target
          · subst target
            by_cases hnext : predecessor.2.2.val + 1 < chainLength
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dif_pos hnext] at hplan
              have hindex :
                  (predecessor.1, predecessor.2.1,
                    ⟨predecessor.2.2.val + 1, hnext⟩) = index :=
                GlobalFilteredCausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl, rfl⟩
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dif_neg hnext] at hplan
              cases hplan
          · simp only [globalFilteredCausalUncachedAttackerHashPlan,
              hrevealed, if_neg htarget] at hplan
            cases hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | some output => simp only [hcache] at hplan; cases hplan
  | none =>
      simp only [hcache] at hplan
      exact globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
        secretKey input state
          (globalChainInputProbe? secretKey.parameter input) index hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (covered : Set GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hchain, hepoch, hnext⟩ :=
    globalFilteredCausalAttackerHashPlan_reveal_has_predecessor secretKey input
      state index hplan
  apply hforward index.1 index.2.1 predecessor.2.2 index.2.2
  · rw [← hchain, ← hepoch]
    exact hcovered predecessor value hrevealed
  · change predecessor.2.2.val ≤ index.2.2.val
    omega

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_covered
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | reveal index =>
      have hindex :=
        globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered secretKey
          input state index covered hplan hcovered hforward
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      constructor
      · exact hcovered.revealResultState secretKey input index (table index)
          _ hindex
      · intro candidate value hmem
        simp only [List.mem_singleton,
          RevealProbeOracleSimulation.ObservedAction.reveal.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hindex
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩


end XmssSecurity.CappedChain
