import XmssSecurity.Proof.AdaptiveRevealedHiddenValue
import XmssSecurity.Proof.ChainHiddenTable

namespace XmssSecurity

open OracleSpec
open XmssSecurity.IndexedHiddenValue

noncomputable def chainSuffixValueIndices (epoch : Epoch) (start : Digit) :
    List ChainValueIndex :=
  ((Finset.univ.filter fun later : Digit => start ≤ later).toList.map fun later =>
    (epoch, later))

@[simp]
theorem mem_chainSuffixValueIndices_iff
    (epoch candidateEpoch : Epoch) (start candidate : Digit) :
    (candidateEpoch, candidate) ∈ chainSuffixValueIndices epoch start ↔
      candidateEpoch = epoch ∧ start ≤ candidate := by
  simp [chainSuffixValueIndices, and_comm, eq_comm]

noncomputable def returnedChainValueIndexList
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    List ChainValueIndex :=
  (log.flatMap fun entry =>
    match entry.2 with
    | none => []
    | some signature =>
        match TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter
              entry.1.epoch (entry.1.message, signature.randomness)) with
        | none => []
        | some encoding =>
            chainSuffixValueIndices entry.1.epoch (encoding chain)).dedup

set_option maxRecDepth 100000 in
@[simp]
theorem mem_returnedChainValueIndexList_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ returnedChainValueIndexList cache secretKey log chain ↔
      ∃ request signature encoding,
        SigningTranscript.Returned log request signature ∧
          TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding ∧
          index.1 = request.epoch ∧ encoding chain ≤ index.2 := by
  simp only [returnedChainValueIndexList, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨entry, hentry, hindex⟩
    cases hsignature : entry.2 with
    | none => simp [hsignature] at hindex
    | some signature =>
        cases hdecode : TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter
              entry.1.epoch (entry.1.message, signature.randomness)) with
        | none => simp [hsignature, hdecode] at hindex
        | some encoding =>
            simp only [hsignature, hdecode] at hindex
            have hsuffix := (mem_chainSuffixValueIndices_iff
              entry.1.epoch index.1 (encoding chain) index.2).1 hindex
            exact ⟨entry.1, signature, encoding,
              ⟨entry, hentry, rfl, hsignature⟩, hdecode,
              hsuffix.1, hsuffix.2⟩
  · rintro ⟨request, signature, encoding,
      ⟨entry, hentry, hrequest, hsignature⟩, hdecode, hepoch, hdigit⟩
    subst request
    refine ⟨entry, hentry, ?_⟩
    simp only [hsignature, hdecode]
    exact (mem_chainSuffixValueIndices_iff
      entry.1.epoch index.1 (encoding chain) index.2).2 ⟨hepoch, hdigit⟩

noncomputable def returnedChainValueReveals
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    List (ChainValueIndex × Digest) :=
  (returnedChainValueIndexList finalCache secretKey log chain).map fun index =>
    (index, keygenChainValueTable keygenCache secretKey chain index)

noncomputable def AttackerAction.chainValueReveal?
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : AttackerAction → Option (ChainValueIndex × Digest)
  | .hash _input => none
  | .sign _request none => none
  | .sign request (some signature) =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
            (request.message, signature.randomness)) with
      | none => none
      | some encoding =>
          some ((request.epoch, encoding chain), signature.chainValue chain)

noncomputable def AttackerActionTrace.chainValueReveals
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (trace : AttackerActionTrace) :
    List (ChainValueIndex × Digest) :=
  trace.filterMap (AttackerAction.chainValueReveal? cache secretKey chain)

theorem AttackerActionTrace.sign_mem_toSigningLog
    (trace : AttackerActionTrace) (request : SignRequest) (signature : Signature)
    (hmem : AttackerAction.sign request (some signature) ∈ trace) :
    SigningTranscript.Returned trace.toSigningLog request signature := by
  refine ⟨⟨request, some signature⟩, ?_, rfl, rfl⟩
  exact List.mem_filterMap.mpr ⟨.sign request (some signature), hmem, rfl⟩

theorem mem_chainValueReveals_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (trace : AttackerActionTrace)
    (reveal : ChainValueIndex × Digest) :
    reveal ∈ trace.chainValueReveals cache secretKey chain ↔
      ∃ request signature encoding,
        AttackerAction.sign request (some signature) ∈ trace ∧
          TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding ∧
          reveal = ((request.epoch, encoding chain), signature.chainValue chain) := by
  unfold AttackerActionTrace.chainValueReveals
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨action, haction, hreveal⟩
    cases action with
    | hash input => simp [AttackerAction.chainValueReveal?] at hreveal
    | sign request signatureOption =>
        cases signatureOption with
        | none => simp [AttackerAction.chainValueReveal?] at hreveal
        | some signature =>
            simp only [AttackerAction.chainValueReveal?] at hreveal
            split at hreveal
            · simp at hreveal
            · rename_i encoding hdecode
              simp only [Option.some.injEq] at hreveal
              exact ⟨request, signature, encoding, haction, hdecode, hreveal.symm⟩
  · rintro ⟨request, signature, encoding, haction, hdecode, rfl⟩
    refine ⟨.sign request (some signature), haction, ?_⟩
    simp [AttackerAction.chainValueReveal?, hdecode]

@[simp]
theorem mem_returnedChainValueReveals_fst_iff
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) (index : ChainValueIndex) :
    index ∈ (returnedChainValueReveals keygenCache finalCache secretKey log chain).map Prod.fst ↔
      index ∈ returnedChainValueIndices finalCache secretKey log chain := by
  rw [mem_returnedChainValueIndices_iff,
    ← mem_returnedChainValueIndexList_iff]
  simp [returnedChainValueReveals]

theorem returnedChainValueReveals_fst_nodup
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    ((returnedChainValueReveals keygenCache finalCache secretKey log chain).map
      Prod.fst).Nodup := by
  have hnodup : (returnedChainValueIndexList finalCache secretKey log chain).Nodup := by
    unfold returnedChainValueIndexList
    exact List.nodup_dedup _
  simpa [returnedChainValueReveals, List.map_map, Function.comp_def] using hnodup

theorem install_returnedChainValueReveals_eq_keygenTable
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    IndexedHiddenValue.installReveals
        (keygenChainValueTable keygenCache secretKey chain)
        (returnedChainValueReveals keygenCache finalCache secretKey log chain) =
      keygenChainValueTable keygenCache secretKey chain := by
  apply IndexedHiddenValue.installReveals_eq_self_of_values
  intro reveal hrevealed
  unfold returnedChainValueReveals at hrevealed
  rw [List.mem_map] at hrevealed
  obtain ⟨index, _hindex, rfl⟩ := hrevealed
  rfl

noncomputable def unrevealedChainValueProbes
    (finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) : List (ChainValueIndex × Digest) :=
  (chainValueProbes secretKey.parameter chain trace forgery encoding).filter fun probe =>
    probe.1 ∉ returnedChainValueIndices finalCache secretKey log chain

set_option maxRecDepth 10000 in
theorem forwardDerivedProbe_not_mem_unrevealed
    (finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (forgedEncoding : Encoding) (request : SignRequest)
    (signature : Signature) (signedEncoding : Encoding)
    (later : Digit) (target : Digest)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some signedEncoding)
    (hle : signedEncoding chain ≤ later) :
    ((request.epoch, later), target) ∉
      unrevealedChainValueProbes finalCache secretKey log chain trace forgery
        forgedEncoding := by
  intro hprobe
  have hnotReturned : (request.epoch, later) ∉
      returnedChainValueIndices finalCache secretKey log chain := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hprobe).2
  apply hnotReturned
  rw [mem_returnedChainValueIndices_iff]
  exact ⟨request, signature, signedEncoding, hreturned, hdecode, rfl, hle⟩

theorem unrevealedChainValueProbes_length_le
    (finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) :
    (unrevealedChainValueProbes finalCache secretKey log chain trace forgery
      encoding).length ≤ (chainValueProbes secretKey.parameter chain trace forgery encoding).length := by
  exact List.length_filter_le _ _

theorem unrevealedChainValueProbes_avoid_reveals
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (trace : AttackerActionTrace) (forgery : Forgery)
    (encoding : Encoding) (probe : ChainValueIndex × Digest)
    (hprobe : probe ∈ unrevealedChainValueProbes finalCache secretKey log chain
      trace forgery encoding) :
    probe.1 ∉ (returnedChainValueReveals keygenCache finalCache secretKey log chain).map Prod.fst := by
  rw [mem_returnedChainValueReveals_fst_iff]
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hprobe).2

theorem WinningOutcomeChainValueHasKeygenOrigin.has_unrevealed_probe
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) (trace : AttackerActionTrace)
    (hsecret : outcome.secretKey = secretKey)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey
      outcome chain) :
    ∃ encoding, ∃ probe ∈ unrevealedChainValueProbes finalCache secretKey
        outcome.signingLog chain trace outcome.forgery encoding,
      keygenChainValueTable keygenCache secretKey chain probe.1 = probe.2 := by
  obtain ⟨encoding, hdecode, hvalue⟩ :=
    winningOutcomeChainValueHasKeygenOrigin_eq_table keygenCache finalCache secretKey
      outcome chain horigin
  let probe : ChainValueIndex × Digest :=
    ((outcome.forgery.epoch, encoding chain), outcome.forgery.signature.chainValue chain)
  have hunrevealed : (outcome.forgery.epoch, encoding chain) ∉
      returnedChainValueIndices finalCache secretKey outcome.signingLog chain := by
    rw [← hsecret]
    exact horigin.1.forged_chain_coordinate_not_mem_returned encoding (by simpa [hsecret] using hdecode)
  refine ⟨encoding, probe, ?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨by simp [chainValueProbes, probe], by simpa [probe] using hunrevealed⟩
  · exact hvalue.symm

theorem WinningOutcomeChainValueHasKeygenOrigin.readMany_unrevealed_eq_true
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) (trace : AttackerActionTrace)
    (q : Nat) (hsecret : outcome.secretKey = secretKey)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey
      outcome chain)
    (hlength : ∀ encoding,
      (unrevealedChainValueProbes finalCache secretKey outcome.signingLog chain trace
        outcome.forgery encoding).length ≤ q) :
    ∃ encoding,
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash finalCache secretKey.parameter
            outcome.forgery.epoch
            (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some encoding ∧
      (let probe : ChainValueIndex × Digest :=
          ((outcome.forgery.epoch, encoding chain), outcome.forgery.signature.chainValue chain)
        let probes := unrevealedChainValueProbes finalCache secretKey outcome.signingLog chain
          trace outcome.forgery encoding
        IndexedHiddenValue.readMany (keygenChainValueTable keygenCache secretKey chain) q
            (listStrategy probe probes) = true ∧
          AvoidsReveals
            (returnedChainValueReveals keygenCache finalCache secretKey outcome.signingLog chain)
            (listStrategy probe probes)) := by
  obtain ⟨encoding, hdecode, hvalue⟩ :=
    winningOutcomeChainValueHasKeygenOrigin_eq_table keygenCache finalCache secretKey
      outcome chain horigin
  let probe : ChainValueIndex × Digest :=
    ((outcome.forgery.epoch, encoding chain), outcome.forgery.signature.chainValue chain)
  have hunrevealed : (outcome.forgery.epoch, encoding chain) ∉
      returnedChainValueIndices finalCache secretKey outcome.signingLog chain := by
    rw [← hsecret]
    exact horigin.1.forged_chain_coordinate_not_mem_returned encoding (by simpa [hsecret] using hdecode)
  have hprobe : probe ∈ unrevealedChainValueProbes finalCache secretKey outcome.signingLog
      chain trace outcome.forgery encoding := by
    apply List.mem_filter.mpr
    exact ⟨by simp [chainValueProbes, probe], by simpa [probe] using hunrevealed⟩
  refine ⟨encoding, hdecode, ?_⟩
  constructor
  · exact readMany_listStrategy_eq_true_of_mem
      (keygenChainValueTable keygenCache secretKey chain) q
      (unrevealedChainValueProbes finalCache secretKey outcome.signingLog chain trace
        outcome.forgery encoding)
      probe probe (hlength encoding) hprobe hvalue.symm
  · exact listStrategy_avoids
      (returnedChainValueReveals keygenCache finalCache secretKey outcome.signingLog chain)
      (unrevealedChainValueProbes finalCache secretKey outcome.signingLog chain trace
        outcome.forgery encoding)
      probe
      hprobe (fun candidate hcandidate =>
        unrevealedChainValueProbes_avoid_reveals keygenCache finalCache secretKey
          outcome.signingLog chain trace outcome.forgery encoding candidate hcandidate)

theorem traced_unrevealedChainValueProbes_length_le
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (result : ((Forgery × Bool) × AttackerActionTrace))
    (hresult : result ∈ support
      (sourceActionTracedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2))
    (finalCache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (chain : ChainIndex) (encoding : Encoding) :
    (unrevealedChainValueProbes finalCache keyResult.1.2 log chain result.2
      result.1.1 encoding).length ≤ q := by
  exact (unrevealedChainValueProbes_length_le finalCache keyResult.1.2 log chain
    result.2 result.1.1 encoding).trans
      (traced_chainValueProbes_length_le q adversary hbound keyResult hkeyResult result hresult
        chain encoding)

end XmssSecurity
