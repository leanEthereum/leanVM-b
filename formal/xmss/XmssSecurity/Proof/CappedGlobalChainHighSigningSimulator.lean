import XmssSecurity.Proof.CappedGlobalChainHighHashCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem Concrete.keygen_signWithEncoding_eq_base
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        epoch randomness encoding =
      Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
        epoch randomness encoding := by
  unfold Concrete.CacheReplay.signWithEncoding
  congr 1
  · funext chain
    calc
      Concrete.CacheReplay.signedChainValues largerCache keyResult.1.2
          epoch encoding chain =
        keygenChainValueTable keyResult.2 keyResult.1.2 chain
          (epoch, encoding chain) :=
        Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult largerCache hle epoch randomness encoding chain
      _ = Concrete.CacheReplay.signedChainValues keyResult.2 keyResult.1.2
          epoch encoding chain :=
        (Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult keyResult.2 le_rfl epoch randomness encoding
            chain).symm
  · exact (TreeCacheStable.authenticationPath_eq keyResult.1.2 keyResult.2
      hstable largerCache hle epoch).symm

noncomputable def globalFilteredCausalSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash keyView.secretKey.parameter request.epoch
        request.message randomness)).run state.cache)
  let encodedState := { state with cache := encoded.2 }
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encodedState)
  | some encoding => do
      let result ← (revealGlobalSignatureChains request encoding allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)).run encodedState
      pure (some result.1, result.2)

noncomputable def globalFilteredCausalSignBoundedAttempts : Nat →
    ProgrammedGlobalChainKeygenView → SignRequest → GlobalCausalHashState →
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState)
  | 0, _keyView, _request, state => pure (none, state)
  | attempts + 1, keyView, request, state => do
      let result ← globalFilteredCausalSigningAttempt keyView request state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.2

noncomputable def globalFilteredCausalSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) :=
  globalFilteredCausalSignBoundedAttempts signingAttemptLimit keyView request
    state

noncomputable def globalFilteredCausalSignTraceContinuation
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match result.1.1 with
  | some _signature => pure result
  | none =>
      (fun rest => (rest.1, result.2 ++ rest.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.1.2)).run

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalFilteredCausalSignBoundedAttempts (attempts + 1) keyView request
        state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run >>=
          globalFilteredCausalSignTraceContinuation attempts table keyView
            request := by
  rw [globalFilteredCausalSignBoundedAttempts, simulateQ_bind,
    WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨⟨signatureOption, resultState⟩, trace⟩
  cases signatureOption with
  | none =>
      simp only [globalFilteredCausalSignTraceContinuation]
      congr 1
  | some signature =>
      simp [globalFilteredCausalSignTraceContinuation]

def GlobalFilteredSigningResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

def GlobalFilteredSigningAttemptResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredSigningResultRelation left right leftResult rightResult ∧
    (leftResult.1 = none → rightResult.2 = [])

theorem relTriple_programmed_globalFilteredCausalSigningAttempt
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningAttempt right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningAttemptResultRelation left right.1) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  rw [Concrete.sign_run_eq]
  unfold globalFilteredCausalSigningAttempt
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← Concrete.signingRandomness_eq]
  apply relTriple_bind (relTriple_refl Concrete.signingRandomness)
  intro leftRandomness rightRandomness hrandomness
  subst rightRandomness
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_globalEncodingHash_run_filtered
      left.secretKey.parameter left.cache leftCache rightState.cache
        hstate.1 hstate.2.1 request.epoch request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.output_eq
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      refine ⟨⟨rfl, hencoded.caches_agree, hencoded.filtered,
        hstate.2.2.1.trans hencoded.left_le, hstate.2.2.2.1, ?_⟩,
        fun _ => rfl⟩
      exact hstate.2.2.2.2.setCache rightEncoded.2
  | some encoding =>
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey request.epoch
              leftRandomness encoding)).run leftEncoded.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftEncoded.2
              left.secretKey request.epoch leftRandomness encoding,
                leftEncoded.2) := by
        simpa [ProgrammedGlobalChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.1.toStable.2.1 leftEncoded.2
            (hstate.2.2.1.trans hencoded.left_le) request.epoch
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply, simulateQ_pure,
        StateT.run_pure]
      rw [simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains]
      simp [Prod.map]
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      let encodedState : GlobalCausalHashState :=
        { rightState with cache := rightEncoded.2 }
      let rightSignature := Concrete.CacheReplay.signWithEncoding
        right.1.1.cache right.1.1.secretKey request.epoch leftRandomness
          encoding
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.1.toStable.2.1 leftEncoded.2
          (hstate.2.2.1.trans hencoded.left_le) request.epoch
            leftRandomness encoding
      have hbase := keygenViews_signWithEncoding_eq_globalReveal
        left right.1 hrel.1.toStable hleftSupport hrightSupport left.cache
          right.1.1.cache le_rfl le_rfl request leftRandomness encoding
            encodedState
      have hsignature :
          Concrete.CacheReplay.signWithEncoding leftEncoded.2 left.secretKey
              request.epoch leftRandomness encoding =
            (globalSignatureRevealResult right.1.2 request encoding allChains
              rightSignature encodedState).1 := hleftStable.trans hbase
      have hcachesFinal : HashCachesAgreeOn
          (GlobalSigningComparableHashInput left.secretKey.parameter)
          leftEncoded.2
          (globalSignatureRevealResult right.1.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.caches_agree
      have hfilteredFinal : FilteredCacheExtensionRelation left.cache
          leftEncoded.2
          (globalSignatureRevealResult right.1.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.filtered
      refine ⟨⟨congrArg some hsignature, hcachesFinal,
        hfilteredFinal,
        hstate.2.2.1.trans hencoded.left_le, ?_, ?_⟩, ?_⟩
      · rw [globalSignatureRevealResult_keygenCache]
        exact hstate.2.2.2.1
      · have hagrees := hstate.2.2.2.2.setCache rightEncoded.2
        exact hagrees.globalSignatureRevealResult request encoding allChains
          rightSignature
      · intro hnone
        simp at hnone

theorem relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    (attempts : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.signBoundedAttempts attempts left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSignBoundedAttempts attempts right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right.1) := by
  induction attempts generalizing leftCache rightState with
  | zero =>
      simp only [Concrete.signBoundedAttempts,
        globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, hstate⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sign_bind attempts
        left.publicKey left.secretKey request.epoch request.message leftCache]
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ]
      apply relTriple_bind
        (relTriple_programmed_globalFilteredCausalSigningAttempt left right
          hrel hleftSupport hrightSupport leftCache rightState hstate request)
      intro leftAttempt rightAttempt hattempt
      rcases hattempt with ⟨hresult, hnil⟩
      rcases hresult with ⟨hoption, hstate'⟩
      cases hleft : leftAttempt.1 with
      | none =>
          have hright : rightAttempt.1.1 = none := by
            rw [← hoption, hleft]
          have htrace : rightAttempt.2 = [] := hnil hleft
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright, htrace]
          simpa using ih leftAttempt.2 rightAttempt.1.2 hstate'
      | some signature =>
          have hright : rightAttempt.1.1 = some signature := by
            rw [← hoption, hleft]
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright]
          apply relTriple_pure_pure
          exact ⟨hright.symm, hstate'⟩

theorem relTriple_programmed_globalFilteredCausalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningQuery right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right.1) := by
  simp only [Concrete.scheme, globalFilteredCausalSigningQuery]
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  apply relTriple_of_evalDist_eq_left
    (Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
      left.keyResult hleftKey hrel.1.2.1 leftCache hstate.2.2.1
        request.epoch request.message)
  rw [Concrete.cappedSign_eq]
  exact relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    signingAttemptLimit left right hrel hleftSupport hrightSupport leftCache
      rightState hstate request

end XmssSecurity.CappedChain
