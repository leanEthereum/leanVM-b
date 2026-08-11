import XmssSecurity.OutcomeClassification

open OracleComp OracleSpec

namespace XmssSecurity

theorem xmssRom_lift_probComp_cache_eq {α : Type} (computation : ProbComp α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ xmssRomImpl (liftM computation)).run initialCache)) :
    result.2 = initialCache := by
  have hsupport := roSim.run_liftM_support
    (hashSpec := HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
    computation initialCache
  rw [show support ((simulateQ xmssRomImpl (liftM computation)).run initialCache) =
      (fun output => (output, initialCache)) '' support computation by
    simpa [xmssRomImpl] using hsupport] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem xmssRom_cache_le {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ xmssRomImpl computation).run initialCache)) :
    initialCache ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : initialCache ≤ middleCache := by
        cases input with
        | inl uniformInput =>
            change unifSpec.Range uniformInput at output
            have hrun :
                (unifFwdImpl HashSpec uniformInput).run initialCache =
                  (fun sample => (sample, initialCache)) <$>
                    (liftM (unifSpec.query uniformInput) : ProbComp _) := by
              simpa [simulateQ_query] using
                (unifFwdImpl.simulateQ_run
                  (hashSpec := HashSpec)
                  (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
            simp only [simulateQ_spec_query, xmssRomImpl, QueryImpl.add_apply] at hquery
            have hquery' : (output, middleCache) ∈
                support ((unifFwdImpl HashSpec uniformInput).run initialCache) := hquery
            rw [hrun, support_map] at hquery'
            obtain ⟨sample, _hsample, heq⟩ := hquery'
            exact le_of_eq (congrArg Prod.snd heq)
        | inr hashInput =>
            rw [show simulateQ xmssRomImpl
                (liftM (OracleWorld.query (Sum.inr hashInput))) =
                (randomOracle : QueryImpl HashSpec
                  (StateT (QueryCache HashSpec) ProbComp)) hashInput by
              simp [xmssRomImpl]] at hquery
            exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
              (output, middleCache) hquery
      exact hmiddle.trans (ih output middleCache result (by simpa using hrest))

theorem detailed_execution_verification_consistent
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.verified = Concrete.verifyFromCache execution.2 execution.1.publicKey
      execution.1.forgery.epoch execution.1.forgery.message execution.1.forgery.signature := by
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hout⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst execution
  simp only
  have hroute :
      simulateQ xmssRomImpl
          (Concrete.scheme.verify publicKey forgery.epoch forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, xmssRomImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  exact (Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey forgery.epoch
    forgery.message forgery.signature adversaryCache finalCache verified hverify).symm

set_option linter.constructorNameAsVariable false in
theorem detailed_execution_key_components_consistent
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey.parameter = execution.1.secretKey.parameter ∧
      execution.1.publicKey.root = Concrete.CacheReplay.treeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.chainStart treeHeight
        Concrete.rootNode := by
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, hkeygen, hrest⟩ := hmem
  have hkeyCacheLe : keyCache ≤ execution.2 :=
    xmssRom_cache_le _ keyCache execution hrest
  simp only [Concrete.scheme] at hkeygen
  unfold Concrete.keygen at hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨parameter, parameterCache⟩, _hparameter, hafterParameter⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, _hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨root, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  cases hout
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only
  have hroute :
      simulateQ xmssRomImpl
          (liftM (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [xmssRomImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [hroute] at hroot
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) secretCache keyCache finalCache root hroot hkeyCacheLe
  rw [Concrete.CacheReplay.eval_treeNode] at heval
  exact ⟨True.intro, heval.symm⟩

theorem detailed_execution_key_consistent
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey =
      Concrete.CacheReplay.publicKeyFromCache execution.2 execution.1.secretKey := by
  obtain ⟨hparameter, hroot⟩ :=
    detailed_execution_key_components_consistent adversary execution hmem
  cases hpublicKey : execution.1.publicKey with
  | mk root parameter =>
      cases hsecretKey : execution.1.secretKey with
      | mk secretParameter chainStart =>
          simp only [hpublicKey, hsecretKey] at hparameter hroot ⊢
          subst parameter
          exact Concrete.CacheReplay.publicKey_eq_publicKeyFromCache execution.2
            ⟨secretParameter, chainStart⟩ root hroot

set_option linter.constructorNameAsVariable false in
theorem concrete_sign_support_replay (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.epoch signature.randomness encoding := by
  unfold Concrete.sign at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨randomness, randomnessCache⟩, _hrandomness, hattempt⟩ := hmem
  have hroute :
      simulateQ xmssRomImpl
          (liftM (Concrete.signAttempt secretKey request.epoch request.message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.signAttempt secretKey request.epoch request.message randomness :
            OracleComp HashSpec (Option Signature)) := by
    simp only [xmssRomImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey request.epoch request.message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute] at hattempt
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.signAttempt secretKey request.epoch request.message randomness :
      OracleComp HashSpec (Option Signature)) randomnessCache resultCache largerCache
      (some signature) hattempt hle
  rw [Concrete.CacheReplay.eval_signAttempt] at heval
  unfold Concrete.CacheReplay.signAttempt at heval
  split at heval
  · rename_i hdecode
    simp at heval
  · rename_i _ encoding hdecode
    simp only [Option.some.injEq] at heval
    have hrandomness : randomness = signature.randomness := by
      simpa only [Concrete.CacheReplay.signWithEncoding] using
        congrArg Signature.randomness heval
    refine ⟨encoding, ?_, ?_⟩
    · rw [← hrandomness]
      exact hdecode
    · rw [← hrandomness]
      exact heval.symm

theorem detailed_execution_consistent_of_signing
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (hsigning : ∀ request signature,
      SigningTranscript.Returned execution.1.signingLog request signature →
      ∃ encoding,
        TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            request.epoch (request.message, signature.randomness)) = some encoding ∧
        signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          request.epoch signature.randomness encoding) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  ⟨detailed_execution_key_consistent adversary execution hmem,
    detailed_execution_verification_consistent adversary execution hmem, hsigning⟩

end XmssSecurity
