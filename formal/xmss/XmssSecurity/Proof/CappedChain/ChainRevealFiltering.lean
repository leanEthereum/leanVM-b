import XmssSecurity.Proof.CappedChain.ChainHiddenTable
import XmssSecurity.Proof.CappedChain.ChainInputTrace

namespace XmssSecurity.CappedChain

open OracleSpec

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

theorem AttackerActionTrace.sign_mem_toSigningLog
    (trace : AttackerActionTrace) (request : SignRequest) (signature : Signature)
    (hmem : AttackerAction.sign request (some signature) ∈ trace) :
    SigningTranscript.Returned trace.toSigningLog request signature := by
  refine ⟨⟨request, some signature⟩, ?_, rfl, rfl⟩
  exact List.mem_filterMap.mpr ⟨.sign request (some signature), hmem, rfl⟩

end XmssSecurity.CappedChain
