import XmssSecurity.Proof.CappedChain.ChainRevealFiltering

open OracleSpec

namespace XmssSecurity.CappedChain

abbrev GlobalChainValueIndex := ChainIndex × ChainValueIndex

noncomputable def globalKeygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey) :
    GlobalChainValueIndex → Digest := fun index =>
  keygenChainValueTable keygenCache secretKey index.1 index.2

noncomputable def globalChainInputProbe?
    (parameter : PublicParameter) (input : HashInput) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ data : Epoch × ChainIndex × ChainStep × Digest,
      input = Concrete.CacheView.chainInput parameter data.1 data.2.1
        data.2.2.1 data.2.2.2 then
    let data := h.choose
    some ((data.2.1, data.1, chainStepDigit data.2.2.1), data.2.2.2)
  else
    none

@[simp]
theorem globalChainInputProbe?_chainInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter epoch chain step value) =
      some ((chain, epoch, chainStepDigit step), value) := by
  unfold globalChainInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have heq := (Concrete.CacheView.chainInput_eq_iff parameter
      chosen.1 epoch chosen.2.1 chain chosen.2.2.1 step
        chosen.2.2.2 value).mp hchosen.symm
    obtain ⟨hepoch, hchain, hstep, hvalue⟩ := heq
    simp only
    rw [hepoch, hchain, hstep, hvalue]
  · rename_i h
    exact (h ⟨(epoch, chain, step, value), rfl⟩).elim

end XmssSecurity.CappedChain
