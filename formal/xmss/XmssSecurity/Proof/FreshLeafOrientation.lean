import XmssSecurity.Proof.ConcreteEventProbability
import XmssSecurity.Proof.DetailedQueryPresence

open OracleComp OracleSpec

namespace XmssSecurity

/-- Map a leaf input to the honest leaf input fixed by key generation at the same epoch. -/
noncomputable def keygenLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ epoch endpoints,
      input = Concrete.CacheView.leafInput secretKey.parameter epoch endpoints then
    Concrete.CacheView.leafInput secretKey.parameter h.choose
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart h.choose)
  else input

@[simp]
theorem keygenLeafTargetInput_leafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (epoch : Epoch) (endpoints : ChainIndex → Digest) :
    keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints) =
      Concrete.CacheView.leafInput secretKey.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
          secretKey.chainStart epoch) := by
  unfold keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨chosenEndpoints, hinput⟩ := h.choose_spec
    have hepoch : h.choose = epoch := by
      have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
        (hinput.trans rfl)
      simp only [HashDomain.leaf.injEq] at hdomain
      exact hdomain.symm
    rw [hepoch]
  · rename_i h
    exfalso
    exact h ⟨epoch, endpoints, rfl⟩

attribute [irreducible] keygenLeafTargetInput

theorem detailedGameAfterKeygen_keys_eq
    (adversary : Adversary Concrete.singleAttemptScheme) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary publicKey secretKey)).run
          initialCache)) :
    execution.1.publicKey = publicKey ∧ execution.1.secretKey = secretKey := by
  unfold detailedGameAfterKeygen at hmem
  simp only at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  exact ⟨rfl, rfl⟩

/-- Cache facts for one leaf collision assemble into the adaptive fresh-collision predicate. -/
theorem adaptiveFreshDigestCollisionWith_of_leafCollision
    (secretKey : SecretKey) (initialCache finalCache : QueryCache HashSpec)
    (epoch : Epoch) (forgedEndpoints : ChainIndex → Digest)
    (forgedOutput honestOutput : HashOutput)
    (hforgedFinal : finalCache
      (Concrete.CacheView.leafInput secretKey.parameter epoch forgedEndpoints) =
        some forgedOutput)
    (hforgedInitial : initialCache
      (Concrete.CacheView.leafInput secretKey.parameter epoch forgedEndpoints) = none)
    (hhonestInitial : initialCache
      (Concrete.CacheView.leafInput secretKey.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
          secretKey.chainStart epoch)) = some honestOutput)
    (hhonestFinal : finalCache
      (Concrete.CacheView.leafInput secretKey.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
          secretKey.chainStart epoch)) = some honestOutput)
    (hstable : Concrete.CacheReplay.oneTimePublicKey finalCache secretKey.parameter
        secretKey.chainStart epoch =
      Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
        secretKey.chainStart epoch)
    (hleafEquality : Concrete.CacheView.leafHash finalCache secretKey.parameter epoch
        forgedEndpoints =
      Concrete.CacheView.leafHash finalCache secretKey.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey finalCache secretKey.parameter
          secretKey.chainStart epoch)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenLeafTargetInput secretKey initialCache) := by
  let forgedInput := Concrete.CacheView.leafInput secretKey.parameter epoch forgedEndpoints
  refine ⟨forgedInput, forgedOutput, honestOutput, hforgedFinal, hforgedInitial, ?_, ?_⟩
  · rw [show forgedInput = Concrete.CacheView.leafInput secretKey.parameter epoch
      forgedEndpoints by rfl]
    rw [keygenLeafTargetInput_leafInput]
    exact hhonestInitial
  · rw [show forgedInput = Concrete.CacheView.leafInput secretKey.parameter epoch
      forgedEndpoints by rfl]
    rw [keygenLeafTargetInput_leafInput]
    rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedFinal,
      Concrete.CacheView.digestAt_eq_of_cache_eq_some hhonestFinal]
    unfold Concrete.CacheView.leafHash at hleafEquality
    rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedFinal] at hleafEquality
    rw [hstable, Concrete.CacheView.digestAt_eq_of_cache_eq_some hhonestFinal] at hleafEquality
    exact hleafEquality

/-- A final-cache leaf collision against the honest WOTS public key is fresh after key generation. -/
theorem leafCollision_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (epoch : Epoch) (forgedEndpoints : ChainIndex → Digest) (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.leafInput secretKey.parameter epoch forgedEndpoints) =
        some forgedOutput)
    (hleafCollision : Wots.HasLeafCollision
      (Concrete.CacheView.leafHash execution.2 secretKey.parameter epoch)
      forgedEndpoints
      (Concrete.CacheReplay.oneTimePublicKey execution.2 secretKey.parameter
        secretKey.chainStart epoch)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have honeTimeStable := (Concrete.keygen_oneTimePublicKey_eq_of_cache_le keyResult
    hkeygen execution.2 hafterCacheLe epoch).symm
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.keygen_cache_has_leafInput keyResult hkeygen epoch
  have hforgedInitial : keyResult.2
      (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch forgedEndpoints) = none := by
    apply Concrete.keygen_cache_leafInput_eq_none_of_ne keyResult hkeygen epoch forgedEndpoints
    intro heq
    apply hleafCollision.1
    exact heq.trans honeTimeStable.symm
  exact adaptiveFreshDigestCollisionWith_of_leafCollision keyResult.1.2 keyResult.2
    execution.2 epoch forgedEndpoints forgedOutput honestOutput hforgedCached hforgedInitial
    hhonestCached (hafterCacheLe hhonestCached) honeTimeStable hleafCollision.2

/-- The leaf branch of a concrete fresh-epoch event is exactly a collision with the honest WOTS public key. -/
theorem fresh_leaf_badEvent_is_collision
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (epoch : Epoch)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (honestPath : Nat → Digest) (hforgedValid : TargetSum.Valid forgedEncoding)
    (hevent : Concrete.FreshEpochBadEventOccurs cache secretKey.parameter epoch
      forgedEncoding forgedSignature (secretKey.chainStart epoch) honestPath
      hforgedValid .leaf) :
    Wots.HasLeafCollision
      (Concrete.CacheView.leafHash cache secretKey.parameter epoch)
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
        forgedEncoding forgedSignature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart epoch) := by
  change Wots.HasLeafCollision
    (Concrete.CacheView.leafHash cache secretKey.parameter epoch)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
      forgedEncoding forgedSignature.chainValue)
    (fun chain => Wots.walk
      (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain) 0
      (chainLength - 1) (secretKey.chainStart epoch chain))
  simpa [Concrete.FreshEpochBadEventOccurs, XmssSecurity.FreshEpochBadEventOccurs,
    Wots.publicChain] using hevent

/-- A successful detailed execution caches the forged leaf for its uniquely decoded encoding. -/
theorem detailed_execution_verified_leaf_cached_as
    (adversary : Adversary Concrete.singleAttemptScheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache Concrete.singleAttemptScheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding) :
    ∃ output, execution.2
      (Concrete.CacheView.leafInput execution.1.secretKey.parameter execution.1.forgery.epoch
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.epoch chain)
          encoding execution.1.forgery.signature.chainValue)) = some output := by
  obtain ⟨actualEncoding, output, hactualDecode, hcached⟩ :=
    detailed_execution_verified_leaf_cached adversary execution hgame hverified
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact ⟨output, hcached⟩

/-- A supported fresh leaf witness supplies both the verifier query and its concrete leaf collision. -/
theorem detailed_execution_fresh_leaf_cached_collision
    (adversary : Adversary Concrete.singleAttemptScheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache Concrete.singleAttemptScheme adversary))
    (forgedEncoding : Encoding) (hforgedValid : TargetSum.Valid forgedEncoding)
    (hverified : execution.1.verified = true)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hleafEvent : Concrete.FreshEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.epoch forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
      hforgedValid .leaf) :
    ∃ forgedOutput,
      execution.2
        (Concrete.CacheView.leafInput execution.1.secretKey.parameter
          execution.1.forgery.epoch
          (recoveredEndpoints
            (fun chain => Concrete.CacheView.chainStep execution.2
              execution.1.secretKey.parameter execution.1.forgery.epoch chain)
            forgedEncoding execution.1.forgery.signature.chainValue)) = some forgedOutput ∧
      Wots.HasLeafCollision
        (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch)
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.epoch chain)
          forgedEncoding execution.1.forgery.signature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey execution.2
          execution.1.secretKey.parameter execution.1.secretKey.chainStart
          execution.1.forgery.epoch) := by
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_leaf_cached_as adversary execution hgame forgedEncoding
      hverified hforgedDecode
  exact ⟨forgedOutput, hforgedCached,
    fresh_leaf_badEvent_is_collision execution.2 execution.1.secretKey
      execution.1.forgery.epoch forgedEncoding execution.1.forgery.signature
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
      hforgedValid hleafEvent⟩

/-- One decoded fresh-epoch leaf witness is oriented against the leaf fixed by key generation. -/
theorem fresh_leaf_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (forgedEncoding : Encoding) (hforgedValid : TargetSum.Valid forgedEncoding)
    (hverified : execution.1.verified = true)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hleafEvent : Concrete.FreshEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.epoch forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
      hforgedValid .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hgame : execution ∈ support (detailedGameWithCache Concrete.singleAttemptScheme adversary) := by
    unfold detailedGameWithCache detailedGameCore
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨keyResult, hkeygen, hafter⟩
  obtain ⟨forgedOutput, hforgedCached, hleafEvent'⟩ :=
    detailed_execution_fresh_leaf_cached_collision adversary execution hgame forgedEncoding
      hforgedValid hverified hforgedDecode hleafEvent
  let forgedEndpoints := recoveredEndpoints
    (fun chain => Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch chain)
    forgedEncoding execution.1.forgery.signature.chainValue
  apply leafCollision_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    execution.1.secretKey hkeys.2 execution.1.forgery.epoch forgedEndpoints forgedOutput
  · simpa [forgedEndpoints] using hforgedCached
  · exact hleafEvent'

/-- A fresh-epoch leaf event is a collision against the honest leaf fixed at key generation. -/
theorem fresh_leaf_event_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 .leaf)
    (hfresh : ∃ forgedEncoding,
      ∃ hforgedValid : TargetSum.Valid forgedEncoding,
      (¬ ∃ request signature,
        SigningTranscript.Returned execution.1.signingLog request signature ∧
          request.epoch = execution.1.forgery.epoch) ∧
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch
          (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding ∧
      Concrete.FreshEpochBadEventOccurs execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch forgedEncoding execution.1.forgery.signature
        (execution.1.secretKey.chainStart execution.1.forgery.epoch)
        (Concrete.signaturePath
          (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
            execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
        hforgedValid .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hleafEvent⟩ := hfresh
  exact fresh_leaf_witness_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter forgedEncoding hforgedValid hevent.1 hforgedDecode hleafEvent

end XmssSecurity
