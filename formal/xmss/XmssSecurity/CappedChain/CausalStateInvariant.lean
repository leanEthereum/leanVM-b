import XmssSecurity.CappedChain.CausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

def CausalRevealsAgree
    (table : ChainValueIndex → Digest) (state : CausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

theorem causalRevealsAgree_empty (table : ChainValueIndex → Digest) :
    CausalRevealsAgree table CausalHashState.empty := by
  intro index value hvalue
  simp [CausalHashState.empty] at hvalue

theorem CausalRevealsAgree.finishKeygen
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state) :
    CausalRevealsAgree table state.finishKeygen := by
  exact hagrees

theorem CausalRevealsAgree.recordProbe
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state)
    (probe : Option (ChainValueIndex × Digest)) :
    CausalRevealsAgree table (state.recordProbe probe) := by
  cases probe <;> exact hagrees

theorem CausalRevealsAgree.causalRecordedState
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput) :
    CausalRevealsAgree table
      (causalRecordedState secretKey chain input state) := by
  unfold XmssSecurity.CappedChain.causalRecordedState
  exact hagrees.recordProbe _

theorem CausalRevealsAgree.setCache
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state)
    (cache : QueryCache HashSpec) :
    CausalRevealsAgree table { state with cache := cache } := by
  exact hagrees

theorem CausalRevealsAgree.recordReveal
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state)
    (index : ChainValueIndex) (value : Digest)
    (hvalue : table index = value) :
    CausalRevealsAgree table (state.recordReveal index value) := by
  intro candidate candidateValue hcand
  by_cases heq : candidate = index
  · subst candidate
    simp [CausalHashState.recordReveal] at hcand
    subst candidateValue
    exact hvalue
  · simp [CausalHashState.recordReveal, Function.update_of_ne heq] at hcand
    exact hagrees candidate candidateValue hcand

theorem CausalRevealsAgree.causalRevealResultState
    {table : ChainValueIndex → Digest} {state : CausalHashState}
    (hagrees : CausalRevealsAgree table state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (index : ChainValueIndex) (value : Digest) (output : HashOutput)
    (hvalue : table index = value) :
    CausalRevealsAgree table
      (causalRevealResultState secretKey chain input state index value output) := by
  unfold XmssSecurity.CappedChain.causalRevealResultState
  exact ((hagrees.causalRecordedState secretKey chain input).recordReveal
    index value hvalue).setCache _

end XmssSecurity.CappedChain
