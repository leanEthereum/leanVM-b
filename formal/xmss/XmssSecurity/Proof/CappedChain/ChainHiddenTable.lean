import XmssSecurity.Proof.CappedChain.ChainOriginProbability

open OracleSpec

namespace XmssSecurity.CappedChain

abbrev ChainValueIndex := Epoch × Digit

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

noncomputable def keygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : ChainValueIndex → Digest := fun index =>
  Wots.walk
    (Concrete.CacheView.chainStep keygenCache secretKey.parameter index.1 chain)
    0 index.2.val (secretKey.chainStart index.1 chain)

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

end XmssSecurity.CappedChain
