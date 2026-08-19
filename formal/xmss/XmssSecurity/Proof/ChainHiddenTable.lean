import XmssSecurity.Proof.ChainInputTrace
import XmssSecurity.Proof.ChainOriginProbability
import XmssSecurity.Proof.ChainTrajectoryComposition

open OracleSpec

namespace XmssSecurity

abbrev ChainValueIndex := Epoch × Digit

def Concrete.fixedChainValues
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) : OracleComp HashSpec (ChainValueIndex → Digest) := do
  let values ← Concrete.sequenceFin fun epoch =>
    Concrete.sequenceFin fun digit =>
      Concrete.chainWalk parameter epoch chain 0 digit.val (secret epoch chain)
  return fun index => values index.1 index.2

def Concrete.treeAndFixedChainValues
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) :
    OracleComp HashSpec (Digest × (ChainValueIndex → Digest)) := do
  let root ← Concrete.treeNode parameter secret treeHeight Concrete.rootNode
  let values ← Concrete.fixedChainValues parameter secret chain
  return (root, values)

def Concrete.fixedChainTrajectoryValues
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) : OracleComp HashSpec (ChainValueIndex → Digest) := do
  let values ← Concrete.sequenceFin fun epoch =>
    Concrete.chainTrajectory parameter epoch chain 0 (chainLength - 1)
      (secret epoch chain)
  return fun index => (values index.1)[index.2.val]'(by
    have hdigit := index.2.isLt
    omega)

def chainStepDigit (step : ChainStep) : Digit :=
  ⟨step.val, step.isLt.trans (by decide)⟩

theorem Concrete.CacheView.chainInput_eq_iff
    (parameter : PublicParameter)
    (leftEpoch rightEpoch : Epoch) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftValue rightValue : Digest) :
    Concrete.CacheView.chainInput parameter leftEpoch leftChain leftStep leftValue =
        Concrete.CacheView.chainInput parameter rightEpoch rightChain rightStep rightValue ↔
      leftEpoch = rightEpoch ∧ leftChain = rightChain ∧
        leftStep = rightStep ∧ leftValue = rightValue := by
  constructor
  · intro heq
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    simp only [HashDomain.chain.injEq] at hdomain
    obtain ⟨hepoch, hchain, hstep⟩ := hdomain
    subst rightEpoch
    subst rightChain
    subst rightStep
    refine ⟨rfl, rfl, rfl, ?_⟩
    exact Concrete.CacheView.chainInput_injective parameter leftEpoch leftChain
      leftStep heq
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

noncomputable def chainInputProbe?
    (parameter : PublicParameter) (chain : ChainIndex)
    (input : HashInput) : Option (ChainValueIndex × Digest) :=
  if h : ∃ data : Epoch × ChainStep × Digest,
      input = Concrete.CacheView.chainInput parameter data.1 chain data.2.1 data.2.2 then
    let data := h.choose
    some ((data.1, chainStepDigit data.2.1), data.2.2)
  else
    none

@[simp]
theorem chainInputProbe?_chainInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    chainInputProbe? parameter chain
      (Concrete.CacheView.chainInput parameter epoch chain step value) =
      some ((epoch, chainStepDigit step), value) := by
  unfold chainInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have heq := (Concrete.CacheView.chainInput_eq_iff parameter
      chosen.1 epoch chain chain chosen.2.1 step chosen.2.2 value).mp
        hchosen.symm
    obtain ⟨hepoch, _hchain, hstep, hvalue⟩ := heq
    simp only
    rw [hepoch, hstep, hvalue]
  · rename_i h
    exact (h ⟨(epoch, step, value), rfl⟩).elim

noncomputable def AttackerActionTrace.chainInputProbes
    (parameter : PublicParameter) (chain : ChainIndex)
    (trace : AttackerActionTrace) : List (ChainValueIndex × Digest) :=
  trace.hashInputs.filterMap (chainInputProbe? parameter chain)

theorem AttackerActionTrace.chainInputProbes_length_le
    (parameter : PublicParameter) (chain : ChainIndex)
    (trace : AttackerActionTrace) :
    (trace.chainInputProbes parameter chain).length ≤ trace.hashInputs.length := by
  exact List.length_filterMap_le _ _

noncomputable def chainValueProbes
    (parameter : PublicParameter) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) : List (ChainValueIndex × Digest) :=
  trace.chainInputProbes parameter chain ++
    [((forgery.epoch, encoding chain), forgery.signature.chainValue chain)]

theorem chainValueProbes_length_le
    (parameter : PublicParameter) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) :
    (chainValueProbes parameter chain trace forgery encoding).length ≤
      trace.hashInputs.length + 1 := by
  unfold chainValueProbes
  simp only [List.length_append, List.length_singleton]
  exact Nat.add_le_add_right
    (trace.chainInputProbes_length_le parameter chain) 1

noncomputable def keygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : ChainValueIndex → Digest := fun index =>
  Wots.walk
    (Concrete.CacheView.chainStep keygenCache secretKey.parameter index.1 chain)
    0 index.2.val (secretKey.chainStart index.1 chain)

@[simp]
theorem Concrete.CacheReplay.eval_fixedChainValues
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.fixedChainValues parameter secret chain) =
      keygenChainValueTable cache (SecretKey.withoutPrecomputation parameter secret) chain := by
  funext index
  simp [Concrete.fixedChainValues, keygenChainValueTable,
    SecretKey.withoutPrecomputation]

@[simp]
theorem Concrete.CacheReplay.eval_treeAndFixedChainValues
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.treeAndFixedChainValues parameter secret chain) =
      (Concrete.CacheReplay.treeNode cache parameter secret treeHeight
        Concrete.rootNode, keygenChainValueTable cache (SecretKey.withoutPrecomputation parameter secret) chain) := by
  simp [Concrete.treeAndFixedChainValues]

@[simp]
theorem Concrete.CacheReplay.eval_fixedChainTrajectoryValues
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.fixedChainTrajectoryValues parameter secret chain) =
      keygenChainValueTable cache (SecretKey.withoutPrecomputation parameter secret) chain := by
  funext index
  simp only [Concrete.fixedChainTrajectoryValues, evalWithAnswerFn_bind,
    Concrete.CacheReplay.eval_sequenceFin, evalWithAnswerFn_pure]
  rw [Concrete.chainTrajectory_getElem]
  rfl

theorem outcomeChainValueHasKeygenOrigin_eq_table
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex)
    (horigin : OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey
      outcome chain) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some encoding ∧
      outcome.forgery.signature.chainValue chain =
        keygenChainValueTable keygenCache secretKey chain
          (outcome.forgery.epoch, encoding chain) := by
  obtain ⟨_verified, encoding, hdecode, hzero | hpositive⟩ := horigin
  · obtain ⟨hdigit, hvalue⟩ := hzero
    refine ⟨encoding, hdecode, ?_⟩
    rw [hvalue, keygenChainValueTable]
    simp [hdigit]
  · obtain ⟨previous, output, hprevious, hcached, houtput⟩ := hpositive
    refine ⟨encoding, hdecode, ?_⟩
    rw [keygenChainValueTable, ← hprevious]
    simp only [Wots.walk, zero_add]
    rw [Concrete.CacheView.chainStep_eq]
    · rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached]
      exact houtput.symm
    · exact previous.isLt

theorem winningOutcomeChainValueHasKeygenOrigin_eq_table
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
      secretKey outcome chain) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some encoding ∧
      outcome.forgery.signature.chainValue chain =
        keygenChainValueTable keygenCache secretKey chain
          (outcome.forgery.epoch, encoding chain) :=
  outcomeChainValueHasKeygenOrigin_eq_table keygenCache finalCache secretKey
    outcome chain horigin.2

theorem winningOutcomeChainValueHasKeygenOrigin_has_probe
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex)
    (trace : AttackerActionTrace)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
      secretKey outcome chain) :
    ∃ encoding, ∃ probe ∈
        chainValueProbes secretKey.parameter chain trace outcome.forgery encoding,
      keygenChainValueTable keygenCache secretKey chain probe.1 = probe.2 := by
  obtain ⟨encoding, _hdecode, hvalue⟩ :=
    winningOutcomeChainValueHasKeygenOrigin_eq_table keygenCache finalCache
      secretKey outcome chain horigin
  let probe : ChainValueIndex × Digest :=
    ((outcome.forgery.epoch, encoding chain),
      outcome.forgery.signature.chainValue chain)
  refine ⟨encoding, probe, ?_, ?_⟩
  · simp [chainValueProbes, probe]
  · exact hvalue.symm

theorem traced_chainValueProbes_length_le
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (result : ((Forgery × Bool) × AttackerActionTrace))
    (hresult : result ∈ support
      (sourceActionTracedDetailedGameAfterKeygen adversary keyResult.1.1
        keyResult.1.2))
    (chain : ChainIndex) (encoding : Encoding) :
    (chainValueProbes keyResult.1.2.parameter chain result.2 result.1.1
      encoding).length ≤ q := by
  have htrace := sourceActionTracedDetailedGameAfterKeygen_hashInputs_length_lt
    q adversary hbound keyResult hkeyResult result hresult
  exact (chainValueProbes_length_le keyResult.1.2.parameter chain result.2
    result.1.1 encoding).trans (by omega)

/-- The chain coordinate used by a winning chain event precedes the coordinate returned by every successful signature at the forged epoch. -/
theorem WinningOutcomeBadEventOccurs.chain_coordinate_lt_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding)
    (request : SignRequest) (signature : Signature) (signedEncoding : Encoding)
    (hreturned : SigningTranscript.Returned outcome.signingLog request signature)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some signedEncoding)
    (hepoch : request.epoch = outcome.forgery.epoch) :
    forgedEncoding chain < signedEncoding chain := by
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨eventRequest, eventSignature, eventSignedEncoding, eventForgedEncoding,
      heventSignedDecode, heventForgedDecode, heventReturned, heventEpoch,
      hchain⟩ := hsame
    have hreturnedEq := SigningTranscript.returned_eq_of_same_epoch
      hevent.signingTranscript_valid heventReturned hreturned
      (heventEpoch.trans hepoch.symm)
    obtain ⟨hrequest, hsignature⟩ := hreturnedEq
    subst request
    subst signature
    have hsignedEncoding : eventSignedEncoding = signedEncoding := by
      rw [heventSignedDecode] at hsignedDecode
      exact Option.some.inj hsignedDecode
    have hforgedEncoding : eventForgedEncoding = forgedEncoding := by
      rw [heventEpoch] at heventForgedDecode
      rw [heventForgedDecode] at hforgedDecode
      exact Option.some.inj hforgedDecode
    change Wots.IsBackwardWitnessAt
      (fun candidateChain => Concrete.CacheView.chainStep cache
        outcome.secretKey.parameter eventRequest.epoch candidateChain)
      eventSignedEncoding eventForgedEncoding eventSignature.chainValue
      outcome.forgery.signature.chainValue chain at hchain
    rw [← hsignedEncoding, ← hforgedEncoding]
    exact hchain.1
  · obtain ⟨_eventForgedEncoding, _hvalid, hunsigned, _hdecode, _hchain⟩ := hfresh
    exact (hunsigned ⟨request, signature, hreturned, hepoch⟩).elim

theorem WinningOutcomeBadEventOccurs.chain_coordinate_ne_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding)
    (request : SignRequest) (signature : Signature) (signedEncoding : Encoding)
    (hreturned : SigningTranscript.Returned outcome.signingLog request signature)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some signedEncoding)
    (hepoch : request.epoch = outcome.forgery.epoch) :
    signedEncoding chain ≠ forgedEncoding chain := by
  exact ne_of_gt (hevent.chain_coordinate_lt_returned forgedEncoding
    hforgedDecode request signature signedEncoding hreturned hsignedDecode hepoch)

/-- Coordinates sent by the signer, together with every later coordinate that can be derived by walking the chain forward. -/
noncomputable def returnedChainValueIndices
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) : Finset ChainValueIndex := by
  classical
  exact Finset.univ.filter fun index => ∃ request signature encoding,
    SigningTranscript.Returned log request signature ∧
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      index.1 = request.epoch ∧ encoding chain ≤ index.2

@[simp]
theorem mem_returnedChainValueIndices_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) (index : ChainValueIndex) :
    index ∈ returnedChainValueIndices cache secretKey log chain ↔
      ∃ request signature encoding,
        SigningTranscript.Returned log request signature ∧
          TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding ∧
          index.1 = request.epoch ∧ encoding chain ≤ index.2 := by
  classical
  simp only [returnedChainValueIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem returnedChainValueIndices_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some encoding) :
    (request.epoch, encoding chain) ∈
      returnedChainValueIndices cache secretKey log chain := by
  rw [mem_returnedChainValueIndices_iff]
  exact ⟨request, signature, encoding, hreturned, hdecode, rfl, le_rfl⟩

set_option linter.constructorNameAsVariable false in
theorem returnedChainValueIndices_forward_closed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (epoch : Epoch) (digit later : Digit)
    (hmem : (epoch, digit) ∈
      returnedChainValueIndices cache secretKey log chain)
    (hle : digit ≤ later) :
    (epoch, later) ∈ returnedChainValueIndices cache secretKey log chain := by
  rw [mem_returnedChainValueIndices_iff] at hmem ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit⟩ := hmem
  exact ⟨request, signature, encoding, hreturned, hdecode,
    hepoch, hdigit.trans hle⟩

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem WinningOutcomeBadEventOccurs.forged_chain_coordinate_not_mem_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding) :
    (outcome.forgery.epoch, forgedEncoding chain) ∉
      returnedChainValueIndices cache outcome.secretKey outcome.signingLog chain := by
  intro hmem
  rw [mem_returnedChainValueIndices_iff] at hmem
  obtain ⟨request, signature, signedEncoding, hreturned, hsignedDecode,
    hepoch, hdigit⟩ := hmem
  have hepoch : request.epoch = outcome.forgery.epoch := by
    exact hepoch.symm
  have hbackward := hevent.chain_coordinate_lt_returned forgedEncoding
    hforgedDecode request signature signedEncoding hreturned hsignedDecode hepoch
  exact (not_lt_of_ge hdigit) hbackward

/-- Every chain value returned by the signer is the corresponding entry of the table fixed during key generation. -/
theorem returned_chainValue_eq_keygenChainValueTable
    (qAdversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme qAdversary keyResult.1.1
          keyResult.1.2)).run keyResult.2))
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (chain : ChainIndex) :
    signature.chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (request.epoch, encoding chain) := by
  have hgame := afterKeygen_execution_mem_detailedGame qAdversary keyResult hkeygen
    execution hafter
  have hkeys := detailedGameAfterKeygen_keys_eq qAdversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hsignature := detailed_execution_returned_signature_eq qAdversary execution hgame
    request signature encoding hdecode hreturned
  have hcacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.singleAttemptScheme qAdversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen execution.2
    hcacheLe request.epoch chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  rw [hsignature, keygenChainValueTable]
  simp only [Concrete.CacheReplay.signWithEncoding,
    Concrete.CacheReplay.signedChainValues]
  rw [hkeys.2]
  exact hwalk.symm

end XmssSecurity
