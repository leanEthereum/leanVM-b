import XmssSecurity.Proof.CappedGlobalChainKeygenGameCoupling
import XmssSecurity.Proof.CappedGlobalChainOrigin
import XmssSecurity.Proof.CappedChain.ChainRevealFiltering
import XmssSecurity.Proof.CappedChain.SignatureChainValue
import XmssSecurity.Proof.RevealProbeOracleSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

structure GlobalCausalHashState where
  cache : QueryCache HashSpec
  keygenCache : QueryCache HashSpec
  revealed : GlobalChainValueIndex → Option Digest
  probes : List (GlobalChainValueIndex × Digest)

def GlobalCausalHashState.empty : GlobalCausalHashState :=
  ⟨∅, ∅, fun _ => none, []⟩

def GlobalCausalHashState.finishKeygen
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  { state with keygenCache := state.cache }

def GlobalCausalHashState.recordProbe
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalHashState :=
  { state with probes :=
      match probe with
      | none => state.probes
      | some value => state.probes ++ [value] }

@[simp]
theorem GlobalCausalHashState.recordProbe_cache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).cache = state.cache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_keygenCache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).keygenCache = state.keygenCache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_revealed
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).revealed = state.revealed := rfl

def GlobalCausalHashState.recordReveal
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) : GlobalCausalHashState :=
  { state with revealed := Function.update state.revealed index (some value) }

def GlobalCausalHashState.setCache
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    GlobalCausalHashState :=
  { state with cache := cache }

@[simp]
theorem GlobalCausalHashState.setCache_revealed
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    (state.setCache cache).revealed = state.revealed := rfl

noncomputable def globalCausalHashQuery
    (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  (fun result : HashOutput × QueryCache HashSpec =>
    (result.1, state.setCache result.2)) <$>
      RevealProbeOracleSimulation.liftProbComp
        ((randomOracle input).run state.cache)

theorem globalCausalHashQuery_run
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state =
      (fun result : HashOutput × QueryCache HashSpec =>
        (result.1, state.setCache result.2)) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache) := rfl

inductive GlobalCausalHashPlan where
  | cached (output : HashOutput)
  | reveal (index : GlobalChainValueIndex)
  | redirect (output : HashOutput)
  | fresh

noncomputable def globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  state.recordProbe (globalChainInputProbe? secretKey.parameter input)

@[simp]
theorem globalCausalRecordedState_cache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).cache = state.cache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_cache state _

@[simp]
theorem globalCausalRecordedState_keygenCache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).keygenCache =
      state.keygenCache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_keygenCache state _

@[simp]
theorem globalCausalRecordedState_revealed
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).revealed =
      state.revealed := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_revealed state _

def globalCausalUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun n => liftM (RevealProbeOracleSimulation.uniformQuery
    (Index := GlobalChainValueIndex) n)

noncomputable def revealGlobalSignatureChains
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature →
      StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex)) Signature
  | [], signature => pure signature
  | chain :: chains, signature => fun state => do
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      let value ← RevealProbeOracleSimulation.revealQuery index
      (revealGlobalSignatureChains request encoding chains
        (replaceSignatureChainValue signature chain value)).run
          (state.recordReveal index value)

def globalSignatureRevealResult
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature → GlobalCausalHashState →
      Signature × GlobalCausalHashState
  | [], signature, state => (signature, state)
  | chain :: chains, signature, state =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      globalSignatureRevealResult table request encoding chains
        (replaceSignatureChainValue signature chain (table index))
        (state.recordReveal index (table index))

def globalSignatureRevealTrace
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex →
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex
  | [] => []
  | chain :: chains =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      .reveal index (table index) ::
        globalSignatureRevealTrace table request encoding chains

theorem simulate_eagerImpl_revealGlobalSignatureChains
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((revealGlobalSignatureChains request encoding chains signature).run
          state) =
      pure (globalSignatureRevealResult table request encoding chains
        signature state) := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains, globalSignatureRevealResult]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      change simulateQ (RevealProbeOracleSimulation.eagerImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery
            (chain, request.epoch, encoding chain)
          (revealGlobalSignatureChains request encoding chains
            (replaceSignatureChainValue signature chain value)).run
              (state.recordReveal
                (chain, request.epoch, encoding chain) value)) = _
      simp only [simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery, pure_bind]
      exact ih _ _

theorem simulate_eagerTrace_revealGlobalSignatureChains
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureChains request encoding chains signature).run
          state)).run =
      pure (globalSignatureRevealResult table request encoding chains
          signature state,
        globalSignatureRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      simp [revealGlobalSignatureChains, globalSignatureRevealResult,
        globalSignatureRevealTrace]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      change (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery
            (chain, request.epoch, encoding chain)
          (revealGlobalSignatureChains request encoding chains
            (replaceSignatureChainValue signature chain value)).run
              (state.recordReveal
                (chain, request.epoch, encoding chain) value))).run = _
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      simp only [pure_bind]
      rw [ih]
      simp [globalSignatureRevealResult, globalSignatureRevealTrace]

theorem globalSignatureRevealResult_chainValue_of_not_mem
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) (candidate : ChainIndex)
    (hnotmem : candidate ∉ chains) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.chainValue candidate = signature.chainValue candidate := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      rw [globalSignatureRevealResult]
      rw [ih _ _ hnotmem.2]
      exact replaceSignatureChainValue_other signature chain candidate
        (table (chain, request.epoch, encoding chain))
        hnotmem.1

theorem globalSignatureRevealResult_chainValue_of_mem
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) (candidate : ChainIndex)
    (hnodup : chains.Nodup) (hmem : candidate ∈ chains) :
    (globalSignatureRevealResult table request encoding chains signature
      state).1.chainValue candidate =
        table (candidate, request.epoch, encoding candidate) := by
  induction chains generalizing signature state with
  | nil => simp at hmem
  | cons chain chains ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst candidate
        rw [globalSignatureRevealResult,
          globalSignatureRevealResult_chainValue_of_not_mem]
        · exact replaceSignatureChainValue_same signature chain _
        · exact hnodup.1
      · rw [globalSignatureRevealResult]
        exact ih _ _ hnodup.2 hmem

theorem globalSignatureRevealResult_allChains_chainValue
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (signature : Signature) (state : GlobalCausalHashState)
    (chain : ChainIndex) :
    (globalSignatureRevealResult table request encoding allChains signature
      state).1.chainValue chain =
        table (chain, request.epoch, encoding chain) := by
  apply globalSignatureRevealResult_chainValue_of_mem
  · exact allChains_nodup
  · simp [allChains]

theorem globalCausalHashQuery_run_isProbeQueryBoundP
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

theorem revealGlobalSignatureChains_run_isProbeQueryBoundP
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (revealGlobalSignatureChains request encoding chains signature).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      exact ih (replaceSignatureChainValue signature chain value)
        (state.recordReveal index value)

end XmssSecurity.CappedChain
