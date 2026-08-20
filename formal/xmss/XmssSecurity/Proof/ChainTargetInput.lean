import XmssSecurity.Proof.HashInputLemmas
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def keygenChainTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : Epoch × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.chainInput secretKey.parameter address.1
        address.2.1 address.2.2 value then
    let address := h.choose
    Concrete.CacheView.chainInput secretKey.parameter address.1 address.2.1 address.2.2
      (Wots.walk
        (Concrete.CacheView.chainStep cache secretKey.parameter address.1 address.2.1)
        0 address.2.2.val (secretKey.chainStart address.1 address.2.1))
  else input

@[simp]
theorem keygenChainTargetInput_chainInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    keygenChainTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value) =
      Concrete.CacheView.chainInput secretKey.parameter epoch chain step
        (Wots.walk (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
          0 step.val (secretKey.chainStart epoch chain)) := by
  unfold keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨chosenValue, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.chain.injEq] at hdomain
    rcases hdomain with ⟨hepoch, hchain, hstep⟩
    dsimp only
    rw [← hepoch, ← hchain, ← hstep]
  · rename_i h
    exfalso
    exact h ⟨(epoch, chain, step), value, rfl⟩

attribute [irreducible] keygenChainTargetInput

end XmssSecurity

