import XmssSecurity.CappedChain.CausalEagerHighVerifierCoverage
import XmssSecurity.CappedChain.CausalEagerHighVerifierRevealCoverage
import XmssSecurity.EncodingEventProbability

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

namespace RevealProbeOracleSimulation

open XmssSecurity.RevealProbeOracleSimulation

theorem runObserved_eq_true_of_probe_mem_of_no_reveal
    (table : ChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State ChainValueIndex)
    (trace : ActionTrace ChainValueIndex)
    (index : ChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hprobe : ObservedAction.probe index target ∈ trace)
    (hhit : table index = target)
    (hnoreveal : ∀ value, ObservedAction.reveal index value ∉ trace) :
    runObserved table state trace = true := by
  induction trace generalizing state with
  | nil => simp at hprobe
  | cons action trace ih =>
      cases action with
      | probe candidate candidateTarget =>
          rw [List.mem_cons] at hprobe
          rcases hprobe with heq | htail
          · cases heq
            exact runObserved_probe_hit_hidden table state index target trace
              hhidden hhit
          · simp only [runObserved]
            cases hrevealed : state.revealed candidate with
            | some value =>
                apply ih state hhidden htail
                intro revealValue hmem
                exact hnoreveal revealValue (by simp [hmem])
            | none =>
                apply ih (state.addPending candidate candidateTarget)
                · exact hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])
      | reveal candidate value =>
          have hne : candidate ≠ index := by
            intro heq
            subst candidate
            exact hnoreveal value (by simp)
          have htail : ObservedAction.probe index target ∈ trace := by
            simpa using hprobe
          simp only [runObserved]
          cases hrevealed : state.revealed candidate with
          | some previous =>
              apply ih state hhidden htail
              intro revealValue hmem
              exact hnoreveal revealValue (by simp [hmem])
          | none =>
              by_cases hearly : table candidate ∈ state.pending candidate
              · simp [hearly]
              · rw [if_neg hearly]
                apply ih (state.install candidate (table candidate))
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne (Ne.symm hne)] using hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])

end RevealProbeOracleSimulation

namespace IndexedHiddenValue

open XmssSecurity.IndexedHiddenValue

theorem listStrategy_eq_default_or_mem
    (default : Index × Digest) (probes : List (Index × Digest))
    (history : List Bool) :
    listStrategy default probes history = default ∨
      listStrategy default probes history ∈ probes := by
  unfold listStrategy
  by_cases hlength : history.length < probes.length
  · right
    rw [List.getD_eq_getElem probes default hlength]
    exact List.getElem_mem _
  · left
    exact List.getD_eq_default _ _ (Nat.le_of_not_gt hlength)

end IndexedHiddenValue

@[simp]
theorem chainInputProbe?_encodingInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (input : Message × Randomness) :
    chainInputProbe? parameter selected
      (Concrete.CacheView.encodingInput parameter epoch input) = none := by
  unfold chainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hchain : AtHashAddress parameter
        (.chain data.1 selected data.2.1)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      rw [hdata]
      simp [Concrete.CacheView.chainInput]
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter
      (.chain data.1 selected data.2.1) (.encoding epoch)
      (Concrete.CacheView.encodingInput parameter epoch input) hchain
        hencoding
    simp at hdomain
  · rfl

@[simp]
theorem leafInputProbe?_encodingInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (input : Message × Randomness) :
    leafInputProbe? parameter selected
      (Concrete.CacheView.encodingInput parameter epoch input) = none := by
  unfold leafInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hleaf : AtHashAddress parameter (.leaf data.1)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      rw [hdata]
      simp [Concrete.CacheView.leafInput]
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter (.leaf data.1)
      (.encoding epoch) (Concrete.CacheView.encodingInput parameter epoch input)
        hleaf hencoding
    simp at hdomain
  · rfl

theorem encodingInput_not_treeRetained
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (input : Message × Randomness) :
    ¬ TreeRetainedHashInput parameter selected
      (Concrete.CacheView.encodingInput parameter epoch input) := by
  rintro (houtside | hmerkle)
  · obtain ⟨otherEpoch, candidate, step, _hne, hchain⟩ := houtside
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter
      (.chain otherEpoch candidate step) (.encoding epoch)
      (Concrete.CacheView.encodingInput parameter epoch input) hchain hencoding
    simp at hdomain
  · obtain ⟨level, node, hmerkle⟩ := hmerkle
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter (.merkle level node)
      (.encoding epoch) (Concrete.CacheView.encodingInput parameter epoch input)
        hmerkle hencoding
    simp at hdomain

theorem filteredTreeHashComputation_support_cache_value_of_no_probes
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (hretained : ¬ TreeRetainedHashInput secretKey.parameter selected input)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    result.1.2.cache input = some result.1.1 := by
  by_cases hcached : ∃ output, state.cache input = some output
  · obtain ⟨output, houtput⟩ := hcached
    have hplan :=
      filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_cached
        high secretKey selected input state output hchain hleaf houtput
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hplan.eq] at hresult
    rw [FilteredTreeHashProgram.computation, houtput] at hresult
    simp only [filteredTreePureHashComputation, simulateQ_pure,
      WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact houtput
  · have hnone : state.cache input = none := by
      cases hvalue : state.cache input with
      | none => rfl
      | some output => exact (hcached ⟨output, hvalue⟩).elim
    have hplan :=
      filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
        high secretKey selected input state hchain hleaf hnone
          (Or.inl hretained)
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hplan.eq] at hresult
    change result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalHashQuery input).run state)).run) at hresult
    rw [simulate_eagerTrace_causalHashQuery, support_map] at hresult
    obtain ⟨sample, hsample, rfl⟩ := hresult
    exact Concrete.CacheReplay.randomOracle_query_caches input state.cache
      sample.1 sample.2 hsample

attribute [local irreducible]
  FilteredTreeHashProgram.computation
  filteredTreeChainHashComputation
  filteredTreePureHashComputation
  filteredTreeFreshHashComputation
  filteredTreeProbeThenFreshHashComputation

theorem filteredHighVerifierRunSupport_encodingHash_eq
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (epoch : Epoch) (message : Message)
    (randomness : Randomness)
    (state : CausalHashState)
    (result : (((Digest × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.encodingHash keyHigh.1.secretKey.parameter epoch message
        randomness) state result) :
    Concrete.CacheView.encodingHash result.1.2.cache
      keyHigh.1.secretKey.parameter epoch (message, randomness) =
        result.1.1.1 := by
  unfold Concrete.encodingHash at hresult
  unfold FilteredHighVerifierRunSupport EagerTraceSupport at hresult
  unfold Concrete.CacheView.encodingHash
  rw [simulate_eagerTrace_filteredHighHashTracedVerifier_tweakableHash_eq_map,
    support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  change (HashOutput × CausalHashState) ×
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex at raw
  rw [filteredHighHashOnlyVerifierImpl_run_eq] at hraw
  have hcachedAtRawInput :=
    filteredTreeHashComputation_support_cache_value_of_no_probes
      table (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        (tweakableHashInput keyHigh.1.secretKey.parameter (.encoding epoch)
          (Concrete.encodingPayload message randomness)) state
        (by
          change chainInputProbe? keyHigh.1.secretKey.parameter selected
            (Concrete.CacheView.encodingInput keyHigh.1.secretKey.parameter
              epoch (message, randomness)) = none
          exact chainInputProbe?_encodingInput
            keyHigh.1.secretKey.parameter selected epoch (message, randomness))
        (by
          change leafInputProbe? keyHigh.1.secretKey.parameter selected
            (Concrete.CacheView.encodingInput keyHigh.1.secretKey.parameter
              epoch (message, randomness)) = none
          exact leafInputProbe?_encodingInput
            keyHigh.1.secretKey.parameter selected epoch (message, randomness))
        (by
          change ¬ TreeRetainedHashInput keyHigh.1.secretKey.parameter selected
            (Concrete.CacheView.encodingInput keyHigh.1.secretKey.parameter
              epoch (message, randomness))
          exact encodingInput_not_treeRetained
            keyHigh.1.secretKey.parameter selected epoch (message, randomness))
        raw hraw
  have hcached : raw.1.2.cache
      (Concrete.CacheView.encodingInput keyHigh.1.secretKey.parameter epoch
        (message, randomness)) = some raw.1.1 := by
    simpa only [Concrete.CacheView.encodingInput] using hcachedAtRawInput
  rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached]

theorem filteredHighVerifierRunSupport_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α)
    (state : CausalHashState)
    (result : (((α × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      computation state result) :
    state.cache ≤ result.1.2.cache := by
  have hmapped : eraseVerifierHashTrace result ∈ support
      (eraseVerifierHashTrace <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((simulateQ (filteredHighHashTracedVerifierImpl keyHigh selected)
            computation).run).run state)).run) := by
    rw [support_map]
    refine ⟨result, ?_, rfl⟩
    assumption
  rw [map_filteredHighHashTracedVerifier_eager_projection table keyHigh
    selected computation state] at hmapped
  exact simulate_filteredHighHashOnlyVerifier_support_cache_le table keyHigh
    selected computation state (eraseVerifierHashTrace result) hmapped

set_option maxHeartbeats 2000000 in
theorem filteredHighVerifierRunSupport_verify_true_primaryProbe_from_finalCache
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (hparameter : publicKey.parameter = keyHigh.1.secretKey.parameter)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (((Bool × VerifierHashInputTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighVerifierRunSupport table keyHigh selected
      (Concrete.verify publicKey epoch message signature) state result)
    (hverified : result.1.1.1 = true) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache publicKey.parameter
          epoch (message, signature.randomness)) = some encoding ∧
      (result.1.2.revealed (epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (epoch, encoding selected) (signature.chainValue selected) ∈
            result.2) := by
  unfold Concrete.verify at hresult
  let digestComputation : OracleComp HashSpec Digest :=
    Concrete.encodingHash publicKey.parameter epoch message signature.randomness
  let afterDigest : Digest → OracleComp HashSpec Bool := fun digest =>
    match TargetSum.decodeDigest digest with
    | none => pure false
    | some encoding => do
        let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch
          encoding signature
        let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
        Concrete.verifyAfterLeaf publicKey epoch signature leaf
  change FilteredHighVerifierRunSupport table keyHigh selected
    (digestComputation >>= afterDigest) state result at hresult
  obtain ⟨digestResult, rest, hdigest, hrest, heq⟩ := by
    apply filteredHighVerifierRunSupport_bind (β := Digest) (α := Bool)
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (first := digestComputation) (next := afterDigest)
      (state := state) (result := result)
    exact hresult
  dsimp [afterDigest] at hrest
  cases hdecode : TargetSum.decodeDigest digestResult.1.1.1 with
  | none =>
      have hrestEq := filteredHighVerifierRunSupport_pure table keyHigh selected
        false digestResult.1.2 rest (by simpa [hdecode] using hrest)
      rw [heq, hrestEq] at hverified
      change false = true at hverified
      exact (Bool.false_ne_true hverified).elim
  | some encoding =>
      have hdigest' : FilteredHighVerifierRunSupport table keyHigh selected
          (Concrete.encodingHash keyHigh.1.secretKey.parameter epoch message
            signature.randomness) state digestResult := by
        dsimp only [digestComputation] at hdigest
        rw [hparameter] at hdigest
        exact hdigest
      have hencodingDigestSecret :=
        filteredHighVerifierRunSupport_encodingHash_eq table keyHigh selected
          epoch message signature.randomness state digestResult hdigest'
      have hencodingDigest :
          Concrete.CacheView.encodingHash digestResult.1.2.cache
            publicKey.parameter epoch (message, signature.randomness) =
              digestResult.1.1.1 := by
        rw [hparameter]
        exact hencodingDigestSecret
      have hdecodeDigestCache : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash digestResult.1.2.cache
            publicKey.parameter epoch (message, signature.randomness)) =
            some encoding := by
        rw [hencodingDigest]
        exact hdecode
      obtain ⟨output, hcached⟩ :=
        Concrete.CacheView.encodingInput_cached_of_decode_some
          digestResult.1.2.cache publicKey.parameter epoch message
            signature.randomness encoding hdecodeDigestCache
      have hcacheLe := filteredHighVerifierRunSupport_cache_le table keyHigh
        selected (afterDigest digestResult.1.1.1) digestResult.1.2 rest hrest
      have hcachedRest := hcacheLe hcached
      have hencodingRest :
          Concrete.CacheView.encodingHash rest.1.2.cache publicKey.parameter
            epoch (message, signature.randomness) = digestResult.1.1.1 := by
        unfold Concrete.CacheView.encodingHash
        rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedRest]
        rw [Concrete.CacheView.encodingHash,
          Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached] at hencodingDigest
        exact hencodingDigest
      have hprimary :=
        filteredHighVerifierRunSupport_afterEncoding_primaryProbe table keyHigh
          selected publicKey epoch encoding signature digestResult.1.2 rest
            (by simpa [hdecode] using hrest)
      obtain ⟨input, hinput, hprobe⟩ := hprimary
      have hinvariant :=
        simulate_filteredHighHashTracedVerifier_support_invariant table keyHigh
          selected (Concrete.verify publicKey epoch message signature) state
            result hresult
      refine ⟨encoding, ?_, ?_⟩
      · rw [heq]
        simp only
        rw [hencodingRest]
        exact hdecode
      · intro hhidden
        apply hinvariant.2 input
        · rw [heq]
          exact List.mem_append_right digestResult.1.1.2 hinput
        · simpa [← hparameter] using hprobe
        · exact hhidden

set_option maxHeartbeats 2000000 in
theorem filteredHighVerifier_support_verify_true_primaryProbe_from_finalCache
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (publicKey : PublicKey)
    (hparameter : publicKey.parameter = keyHigh.1.secretKey.parameter)
    (epoch : Epoch) (message : Message) (signature : Signature)
    (state : CausalHashState)
    (result : (Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredHighVerifierImpl keyHigh selected)
          (Concrete.cappedScheme.verify publicKey epoch message signature)).run
            state)).run))
    (hverified : result.1.1 = true) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache publicKey.parameter
          epoch (message, signature.randomness)) = some encoding ∧
      (result.1.2.revealed (epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (epoch, encoding selected) (signature.chainValue selected) ∈
            result.2) := by
  unfold Concrete.cappedScheme at hresult
  rw [simulate_filteredHighVerifier_liftM_eq_hashOnly] at hresult
  obtain ⟨tracedResult, htracedResult, heq⟩ :=
    filteredHighVerifierRunSupport_lift
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (computation := Concrete.verify publicKey epoch message signature)
      (state := state) (result := result) hresult
  subst result
  exact filteredHighVerifierRunSupport_verify_true_primaryProbe_from_finalCache
    table keyHigh selected publicKey hparameter epoch message signature state
      tracedResult htracedResult hverified

set_option maxHeartbeats 2000000 in
theorem filteredHighDetailedRunSupport_verified_primaryProbe_from_finalCache
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.cappedScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (hparameter : keyHigh.1.publicKey.parameter =
      keyHigh.1.secretKey.parameter)
    (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result)
    (hverified : result.1.1.1.2 = true) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache
          keyHigh.1.secretKey.parameter result.1.1.1.1.epoch
          (result.1.1.1.1.message,
            result.1.1.1.1.signature.randomness)) = some encoding ∧
      (result.1.2.revealed
          (result.1.1.1.1.epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (result.1.1.1.1.epoch, encoding selected)
          (result.1.1.1.1.signature.chainValue selected) ∈ result.2) := by
  obtain ⟨handled, verifier, _hhandled, hverifier, heq⟩ :=
    filteredHighDetailedRunSupport_decompose table adversary keyHigh selected
      state result hresult
  rw [heq] at hverified ⊢
  obtain ⟨encoding, hdecode, hprimary⟩ :=
    filteredHighVerifier_support_verify_true_primaryProbe_from_finalCache
      table keyHigh selected keyHigh.1.publicKey hparameter
        handled.1.1.1.epoch handled.1.1.1.message
          handled.1.1.1.signature handled.1.2 verifier hverifier hverified
  refine ⟨encoding, ?_, ?_⟩
  · simpa only [hparameter] using hdecode
  · intro hhidden
    exact List.mem_append_right handled.2 (hprimary hhidden)

set_option maxHeartbeats 2000000 in
theorem filteredHighMonitoredDetailedExecution_support_verified_primaryProbe_from_finalCache
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.cappedScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (hparameter : keyHigh.1.publicKey.parameter =
      keyHigh.1.secretKey.parameter)
    (result : (Forgery × Bool) × MonitoredTracedState)
    (hresult : result ∈ support
      (filteredHighMonitoredDetailedExecution adversary keyHigh selected
        table))
    (hverified : result.1.2 = true) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.2.1.causal.cache
          keyHigh.1.secretKey.parameter result.1.1.epoch
          (result.1.1.message, result.1.1.signature.randomness)) =
            some encoding ∧
      (result.2.1.causal.revealed
          (result.1.1.epoch, encoding selected) = none →
        RevealProbeOracleSimulation.ObservedAction.probe
          (result.1.1.epoch, encoding selected)
          (result.1.1.signature.chainValue selected) ∈
            result.2.1.trace) := by
  let projected :=
    ((((result.1, result.2.2), result.2.1.causal), result.2.1.trace))
  have hprojected : FilteredHighDetailedRunSupport table adversary keyHigh
      selected (filteredCausalKeygenState selected keyHigh.1) projected :=
    filteredHighMonitoredDetailedExecution_support_action_projection table
      adversary keyHigh selected result hresult
  simpa [projected] using
    (filteredHighDetailedRunSupport_verified_primaryProbe_from_finalCache
      table adversary keyHigh selected hparameter
        (filteredCausalKeygenState selected keyHigh.1) projected hprojected
          hverified)

theorem listStrategy_unrevealedChainValueProbes_eq_primary_or_attacker
    (finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (selected : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) (history : List Bool) :
    let primary : ChainValueIndex × Digest :=
      ((forgery.epoch, encoding selected),
        forgery.signature.chainValue selected)
    let probes := unrevealedChainValueProbes finalCache secretKey log selected
      trace forgery encoding
    IndexedHiddenValue.listStrategy primary probes history = primary ∨
      IndexedHiddenValue.listStrategy primary probes history ∈
        trace.chainInputProbes secretKey.parameter selected := by
  dsimp only
  rcases IndexedHiddenValue.listStrategy_eq_default_or_mem
      ((forgery.epoch, encoding selected),
        forgery.signature.chainValue selected)
      (unrevealedChainValueProbes finalCache secretKey log selected trace
        forgery encoding) history with hprimary | hmem
  · exact Or.inl hprimary
  · have hchain := (List.mem_filter.mp hmem).1
    unfold chainValueProbes at hchain
    rw [List.mem_append] at hchain
    rcases hchain with hattacker | hprimary
    · exact Or.inr hattacker
    · exact Or.inl (by simpa using hprimary)

theorem sourceDirectTracedProgram_support_keygen
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex)
    (result : SourceDirectTracedProgramResult)
    (hresult : result ∈ support
      (sourceDirectTracedProgram adversary selected)) :
    result.1 ∈ support (programmedWarmedFixedChainKeygen selected) := by
  unfold sourceDirectTracedProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem returnedChainValueCovered_of_signingComparableCaches
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftCache rightCache : QueryCache HashSpec)
    (leftSecret rightSecret : SecretKey)
    (leftLog rightLog : QueryLog SigningSpec)
    (hleftParameter : leftSecret.parameter = parameter)
    (hrightParameter : rightSecret.parameter = parameter)
    (hlogs : rightLog = leftLog)
    (hcaches : HashCachesAgreeOn
      (SigningComparableHashInput parameter selected) leftCache rightCache)
    (index : ChainValueIndex)
    (hindex : index ∈
      ReturnedChainValueCovered rightCache rightSecret rightLog selected) :
    index ∈ ReturnedChainValueCovered leftCache leftSecret leftLog
      selected := by
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
    rw [hcaches _ (Or.inr ⟨request.epoch, request.message,
      signature.randomness, rfl⟩)]
  refine ⟨request, signature, encoding, ?_, ?_, hepoch, hdigit⟩
  · simpa [hlogs] using hreturned
  · rw [hhash]
    exact hdecode

theorem sourceFilteredHighMonitoredProgramRelation_hit_implies_observedHit
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (selected : ChainIndex)
    (left : SourceDirectTracedProgramResult)
    (right : FilteredHighMonitoredProgramResult)
    (hleftKeySupport : left.1 ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightKeySupport : right.1.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (hrightExecutionSupport : right.2 ∈ support
      (filteredHighMonitoredDetailedExecution adversary
        (right.1.1.1, right.1.2) selected right.1.1.2))
    (hrel : SourceFilteredHighMonitoredProgramRelation selected left right)
    (hhit : ActionTracedChainProbeHit queries selected
      (eraseFixedChainKeygenView (sourceDirectProgramResult left))) :
    RevealProbeOracleSimulation.ObservedHit
      (filteredHighMonitoredProgramProjection right) := by
  rcases hrel with ⟨hkeyRel, hgoodOrBad, hconsistent⟩
  rcases hgoodOrBad with hgood | hbad
  · unfold ActionTracedChainProbeHit at hhit
    dsimp [eraseFixedChainKeygenView, sourceDirectProgramResult,
      sourceDirectExecutionResult, actionTraceOutcome] at hhit
    rcases hhit with ⟨hverified, encoding, hdecode, hread, havoid⟩
    guard_target = RevealProbeOracleSimulation.ObservedHit
      (filteredHighMonitoredProgramProjection right)
    rcases hgood with ⟨hexecution, htraced⟩
    rcases htraced with ⟨hmonitored, htrace⟩
    obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hfiltered⟩ :=
      hmonitored
    have hleftKeyResult := programmedWarmedFixedChainKeygen_support_keyResult
      selected left.1 hleftKeySupport
    have hrightKeyResult := actualFixedChainKeygen_support_keyResult selected
      right.1.1.1 hrightKeySupport
    have hrightPublicParameter : right.1.1.1.publicKey.parameter =
        right.1.1.1.secretKey.parameter :=
      right.1.1.1.parameter_eq hrightKeyResult
    have hsecretParameter : right.1.1.1.secretKey.parameter =
        left.1.secretKey.parameter :=
      hkeyRel.parameter_eq selected left.1 right.1 hleftKeySupport
        hrightKeySupport
    have hrightVerified : right.2.1.2 = true := by
      rw [← hexecution]
      exact hverified
    obtain ⟨rightEncoding, hrightDecode, hprimaryCovered⟩ :=
      filteredHighMonitoredDetailedExecution_support_verified_primaryProbe_from_finalCache
        right.1.1.2 adversary (right.1.1.1, right.1.2) selected
          hrightPublicParameter right.2 hrightExecutionSupport hrightVerified
    rw [← hexecution] at hrightDecode hprimaryCovered
    rw [hsecretParameter] at hrightDecode
    have hencodingHash :
        Concrete.CacheView.encodingHash left.2.2.1 left.1.secretKey.parameter
            left.2.1.1.epoch
            (left.2.1.1.message, left.2.1.1.signature.randomness) =
          Concrete.CacheView.encodingHash right.2.2.1.causal.cache
            left.1.secretKey.parameter left.2.1.1.epoch
            (left.2.1.1.message,
              left.2.1.1.signature.randomness) := by
      unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
      rw [hfiltered.1 _ (Or.inr ⟨left.2.1.1.epoch,
        left.2.1.1.message, left.2.1.1.signature.randomness, rfl⟩)]
    have hrightDecodeAtLeft : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash left.2.2.1
          left.1.secretKey.parameter left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness)) =
          some rightEncoding := by
      rw [hencodingHash]
      exact hrightDecode
    have hencodingEq : rightEncoding = encoding := by
      have hdecodeAtErasedKey : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash left.2.2.1
            left.1.secretKey.parameter left.2.1.1.epoch
            (left.2.1.1.message, left.2.1.1.signature.randomness)) =
            some encoding := by
        simpa [Concrete.materializePrecomputation,
          Concrete.precomputedSecretKey] using hdecode
      rw [hdecodeAtErasedKey] at hrightDecodeAtLeft
      exact (Option.some.inj hrightDecodeAtLeft).symm
    subst rightEncoding
    obtain ⟨_digest, _coveredEncoding, _hcoveredDecode, hchainCovered,
        _hcoveredPrimary⟩ :=
      filteredHighMonitoredDetailedExecution_support_verified_coverage
        right.1.1.2 adversary (right.1.1.1, right.1.2) selected
          hrightPublicParameter right.2 hrightExecutionSupport hrightVerified
    have hcovered :=
      filteredHighMonitoredDetailedExecution_support_returnedCovered
        right.1.1.2 adversary (right.1.1.1, right.1.2) selected right.2
          hrightExecutionSupport
    have htableMaterialized : keygenChainValueTable left.1.cache
        (Concrete.materializePrecomputation left.1.cache left.1.secretKey)
          selected = keygenChainValueTable left.1.cache left.1.secretKey
            selected := rfl
    have hprobesMaterialized : unrevealedChainValueProbes left.2.2.1
        (Concrete.materializePrecomputation left.1.cache left.1.secretKey)
          left.2.2.2.toSigningLog selected left.2.2.2 left.2.1.1 encoding =
        unrevealedChainValueProbes left.2.2.1 left.1.secretKey
          left.2.2.2.toSigningLog selected left.2.2.2 left.2.1.1 encoding := rfl
    rw [htableMaterialized, hprobesMaterialized,
      IndexedHiddenValue.readMany_true_iff] at hread
    obtain ⟨round, hround, hvalue⟩ := hread
    let history := List.replicate round false
    let primary : ChainValueIndex × Digest :=
      ((left.2.1.1.epoch, encoding selected),
        left.2.1.1.signature.chainValue selected)
    let probes := unrevealedChainValueProbes left.2.2.1 left.1.secretKey
      left.2.2.2.toSigningLog selected left.2.2.2 left.2.1.1 encoding
    let candidate := IndexedHiddenValue.listStrategy primary probes history
    have hcandidateValue : right.1.1.2 candidate.1 = candidate.2 := by
      have htable := programmedWarmedFixedChainKeygen_support_table selected
        left.1 hleftKeySupport
      have htableRight : keygenChainValueTable left.1.cache left.1.secretKey
          selected = right.1.1.2 := htable.trans hkeyRel.base.base.1.1
      rw [← htableRight]
      simpa only [candidate, history, primary, probes] using hvalue
    have hcandidateClass : candidate = primary ∨
        candidate ∈ left.2.2.2.chainInputProbes
          left.1.secretKey.parameter selected := by
      simpa only [candidate, history, primary, probes] using
        (listStrategy_unrevealedChainValueProbes_eq_primary_or_attacker
          left.2.2.1 left.1.secretKey left.2.2.2.toSigningLog selected
            left.2.2.2 left.2.1.1 encoding history)
    have hnotLeftCovered : candidate.1 ∉
        ReturnedChainValueCovered left.2.2.1 left.1.secretKey
          left.2.2.2.toSigningLog selected := by
      intro hmem
      exact havoid history
        (returnedChainValueCovered_mem_reveals left.1.cache left.2.2.1
          left.1.secretKey left.2.2.2.toSigningLog selected candidate.1 hmem)
    have hnotRightCovered : candidate.1 ∉
        ReturnedChainValueCovered right.2.2.1.causal.cache
          right.1.1.1.secretKey right.2.2.2.toSigningLog selected := by
      intro hmem
      apply hnotLeftCovered
      apply returnedChainValueCovered_of_signingComparableCaches
        left.1.secretKey.parameter selected left.2.2.1
          right.2.2.1.causal.cache left.1.secretKey
            right.1.1.1.secretKey left.2.2.2.toSigningLog
              right.2.2.2.toSigningLog
      · rfl
      · exact hsecretParameter
      · exact congrArg AttackerActionTrace.toSigningLog htrace.symm
      · exact hfiltered.1
      · exact hmem
    have hhidden : right.2.2.1.causal.revealed candidate.1 = none := by
      cases hrevealedValue : right.2.2.1.causal.revealed candidate.1 with
      | none => rfl
      | some value =>
          exact (hnotRightCovered
            (hcovered.1 candidate.1 value hrevealedValue)).elim
    have hnoreveal : ∀ value,
        RevealProbeOracleSimulation.ObservedAction.reveal candidate.1 value ∉
          right.2.2.1.trace := by
      intro value hmem
      exact hnotRightCovered (hcovered.2 candidate.1 value hmem)
    have hprobe : RevealProbeOracleSimulation.ObservedAction.probe candidate.1
        candidate.2 ∈ right.2.2.1.trace := by
      rcases hcandidateClass with hprimary | hattacker
      · rw [hprimary] at hhidden ⊢
        exact hprimaryCovered hhidden
      · apply hchainCovered candidate
        · rw [hsecretParameter, ← htrace]
          exact hattacker
        · exact hhidden
    unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [filteredHighMonitoredProgramProjection]
    apply RevealProbeOracleSimulation.runObserved_eq_true_of_probe_mem_of_no_reveal
      right.1.1.2 AdaptiveRevealMonitor.State.empty right.2.2.1.trace
        candidate.1 candidate.2
    · rfl
    · exact hprobe
    · exact hcandidateValue
    · exact hnoreveal
  · exact sourceFilteredHighMonitoredProgramRelation_bad_implies_observedHit
      selected left right ⟨hkeyRel, Or.inr hbad, hconsistent⟩ hbad

end XmssSecurity.CappedChain
