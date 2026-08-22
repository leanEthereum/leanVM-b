import XmssSecurity.Proof.OutcomeClassification
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec

namespace XmssSecurity

theorem capped_detailed_execution_verification_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.verified = Concrete.verifyFromCache execution.2 execution.1.publicKey
      execution.1.forgery.epoch execution.1.forgery.message execution.1.forgery.signature := by
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hout⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst execution
  simp only
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.epoch forgery.message
            forgery.signature) =
        simulateQ randomOracle
          (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  exact (Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey forgery.epoch
    forgery.message forgery.signature adversaryCache finalCache verified hverify).symm

set_option linter.constructorNameAsVariable false in
theorem capped_detailed_execution_key_components_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
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
  unfold Concrete.precomputedKeygen at hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨parameter, parameterCache⟩, _hparameter, hafterParameter⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, _hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨treeResult, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  cases hout
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest).withQueryLog) =
        simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest).withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog
  rw [hroute] at hroot
  have hroot' : (treeResult.1, keyCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run secretCache) := by
    rw [← withQueryLog_cache_projection]
    rw [support_map]
    exact ⟨(treeResult, keyCache), hroot, rfl⟩
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) secretCache keyCache finalCache treeResult.1 hroot'
        hkeyCacheLe
  rw [Concrete.CacheReplay.eval_treeNode] at heval
  exact ⟨rfl, heval.symm⟩

theorem capped_detailed_execution_key_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey =
      Concrete.CacheReplay.publicKeyFromCache execution.2 execution.1.secretKey := by
  obtain ⟨hparameter, hroot⟩ :=
    capped_detailed_execution_key_components_consistent adversary execution hmem
  cases hpublicKey : execution.1.publicKey with
  | mk root parameter =>
      cases hsecretKey : execution.1.secretKey with
      | mk secretParameter chainStart chainValue treeValue =>
          simp only [hpublicKey, hsecretKey] at hparameter hroot ⊢
          subst parameter
          exact Concrete.CacheReplay.publicKey_eq_publicKeyFromCache execution.2
            ⟨secretParameter, chainStart, chainValue, treeValue⟩ root hroot

theorem capped_detailed_execution_consistent_of_signing
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary))
    (hsigning : ∀ request signature,
      SigningTranscript.Returned execution.1.signingLog request signature →
      ∃ encoding,
        TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            request.epoch (request.message, signature.randomness)) = some encoding ∧
        signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          request.epoch signature.randomness encoding) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  ⟨capped_detailed_execution_key_consistent adversary execution hmem,
    capped_detailed_execution_verification_consistent adversary execution hmem, hsigning⟩

end XmssSecurity
