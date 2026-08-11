import XmssSecurity.ChainInputTrace
import XmssSecurity.ChainOriginProbability

open OracleSpec

namespace XmssSecurity

abbrev ChainValueIndex := Epoch × Digit

def chainStepDigit (step : ChainStep) : Digit :=
  ⟨step.val, step.isLt.trans (by native_decide)⟩

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
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
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

end XmssSecurity
