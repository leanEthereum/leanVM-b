import XmssSecurity.Proof.HashInputLemmas
import XmssSecurity.Proof.StatementLemmas

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

end XmssSecurity

