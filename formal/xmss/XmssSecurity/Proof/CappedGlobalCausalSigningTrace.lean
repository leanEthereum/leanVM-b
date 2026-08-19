import XmssSecurity.Proof.CappedGlobalCausalSigningProjection

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

theorem revealGlobalSignatureOption_run
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState) :
    (revealGlobalSignatureOption secretKey request signatureOption).run state =
      (match signatureOption with
      | none => pure (none, state)
      | some signature =>
          match TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash state.cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none => pure (some signature, state)
          | some encoding => do
              let revealed ← (revealGlobalSignatureChains request encoding
                allChains signature).run state
              pure (some revealed.1, revealed.2)) := by
  cases signatureOption <;> rfl

theorem simulate_eagerTrace_revealGlobalSignatureOption_some_of_decode
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (request : SignRequest)
    (signature : Signature) (state : GlobalCausalHashState)
    (encoding : ChainIndex → Digit)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((revealGlobalSignatureOption secretKey request (some signature)).run
        state)).run =
      pure (((some (globalSignatureRevealResult table request encoding
        allChains signature state).1,
          (globalSignatureRevealResult table request encoding
            allChains signature state).2),
        globalSignatureRevealTrace table request encoding allChains)) := by
  rw [revealGlobalSignatureOption_run]
  simp only [hdecode]
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_revealGlobalSignatureChains]
  simp

theorem simulate_eagerTrace_globalCausalSigningQueryAfterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalSigningQueryAfterRealRom
        publicKey secretKey request state)).run =
    ((simulateQ xmssRomImpl
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache >>= fun signed =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureOption secretKey request signed.1).run
          { state with cache := signed.2 })).run) := by
  unfold globalCausalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex => trace)) = id from rfl, Function.comp_id]
  simp

end XmssSecurity.CappedChain
