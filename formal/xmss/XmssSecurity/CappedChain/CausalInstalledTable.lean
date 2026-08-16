import XmssSecurity.CausalActionResampling
import XmssSecurity.CappedChain.CausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

def causalInstalledTable
    (state : CausalHashState) (base : ChainValueIndex → Digest) :
    ChainValueIndex → Digest :=
  fun index => (state.revealed index).getD (base index)

@[simp]
theorem causalInstalledTable_empty
    (base : ChainValueIndex → Digest) :
    causalInstalledTable CausalHashState.empty base = base := by
  funext index
  rfl

theorem causalInstalledTable_of_revealed
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex) (value : Digest)
    (hrevealed : state.revealed index = some value) :
    causalInstalledTable state base index = value := by
  simp [causalInstalledTable, hrevealed]

theorem causalInstalledTable_of_not_revealed
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex)
    (hrevealed : state.revealed index = none) :
    causalInstalledTable state base index = base index := by
  simp [causalInstalledTable, hrevealed]

theorem causalInstalledTable_recordProbe
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (probe : Option (ChainValueIndex × Digest)) :
    causalInstalledTable (state.recordProbe probe) base =
      causalInstalledTable state base := by
  rfl

theorem causalInstalledTable_causalRecordedState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (base : ChainValueIndex → Digest) :
    causalInstalledTable
        (causalRecordedState secretKey chain input state) base =
      causalInstalledTable state base := by
  rw [causalRecordedState]
  exact causalInstalledTable_recordProbe state base _

theorem causalInstalledTable_setCache
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (cache : QueryCache HashSpec) :
    causalInstalledTable { state with cache := cache } base =
      causalInstalledTable state base := by
  rfl

theorem causalInstalledTable_finishKeygen
    (state : CausalHashState) (base : ChainValueIndex → Digest) :
    causalInstalledTable state.finishKeygen base =
      causalInstalledTable state base := by
  rfl

theorem causalInstalledTable_recordReveal
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex) (value : Digest) :
    causalInstalledTable (state.recordReveal index value) base =
      Function.update (causalInstalledTable state base) index value := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [causalInstalledTable, CausalHashState.recordReveal]
  · simp [causalInstalledTable, CausalHashState.recordReveal,
      Function.update_of_ne heq]

theorem causalInstalledTable_update_base_of_revealed
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex) (value replacement : Digest)
    (hrevealed : state.revealed index = some value) :
    causalInstalledTable state (Function.update base index replacement) =
      causalInstalledTable state base := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [causalInstalledTable, hrevealed]
  · simp [causalInstalledTable, Function.update_of_ne heq]

@[simp]
theorem causalRevealResultState_revealed_self
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest)
    (output : HashOutput) :
    (causalRevealResultState secretKey chain input state index value output).revealed
      index = some value := by
  unfold causalRevealResultState CausalHashState.recordReveal
  simp

theorem causalInstalledTable_causalRevealResultState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex) (value : Digest) (output : HashOutput) :
    causalInstalledTable
        (causalRevealResultState secretKey chain input state index value output)
        base =
      Function.update (causalInstalledTable state base) index value := by
  unfold causalRevealResultState
  rw [causalInstalledTable_setCache, causalInstalledTable_recordReveal,
    causalInstalledTable_causalRecordedState]

theorem causalRevealsAgree_causalInstalledTable
    (state : CausalHashState) (base : ChainValueIndex → Digest) :
    CausalRevealsAgree (causalInstalledTable state base) state := by
  intro index value hvalue
  exact causalInstalledTable_of_revealed state base index value hvalue

def CausalRevealsLe (left right : CausalHashState) : Prop :=
  ∀ index value, left.revealed index = some value →
    right.revealed index = some value

theorem CausalRevealsLe.refl (state : CausalHashState) :
    CausalRevealsLe state state := by
  intro index value hvalue
  exact hvalue

theorem CausalRevealsLe.trans
    {left middle right : CausalHashState}
    (hleft : CausalRevealsLe left middle)
    (hright : CausalRevealsLe middle right) :
    CausalRevealsLe left right := by
  intro index value hvalue
  exact hright index value (hleft index value hvalue)

theorem CausalRevealsLe.recordProbe
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    CausalRevealsLe state (state.recordProbe probe) := by
  intro index value hvalue
  exact hvalue

theorem CausalRevealsLe.causalRecordedState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    CausalRevealsLe state
      (causalRecordedState secretKey chain input state) := by
  rw [XmssSecurity.CappedChain.causalRecordedState]
  exact CausalRevealsLe.recordProbe state _

theorem CausalRevealsLe.setCache
    (state : CausalHashState) (cache : QueryCache HashSpec) :
    CausalRevealsLe state { state with cache := cache } := by
  intro index value hvalue
  exact hvalue

theorem CausalRevealsLe.finishKeygen
    (state : CausalHashState) :
    CausalRevealsLe state state.finishKeygen := by
  intro index value hvalue
  exact hvalue

theorem CausalRevealsLe.recordReveal
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest)
    (hcompatible : ∀ previous,
      state.revealed index = some previous → previous = value) :
    CausalRevealsLe state (state.recordReveal index value) := by
  intro candidate candidateValue hcandidate
  by_cases heq : candidate = index
  · subst candidate
    simp only [CausalHashState.recordReveal, Function.update_self]
    exact congrArg some (hcompatible candidateValue hcandidate).symm
  · simpa [CausalHashState.recordReveal, Function.update_of_ne heq] using
      hcandidate

theorem CausalRevealsLe.causalRevealResultState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest)
    (output : HashOutput)
    (hcompatible : ∀ previous,
      state.revealed index = some previous → previous = value) :
    CausalRevealsLe state
      (causalRevealResultState secretKey chain input state index value output) := by
  unfold XmssSecurity.CappedChain.causalRevealResultState
  exact (CausalRevealsLe.causalRecordedState
    secretKey chain input state).trans
      ((CausalRevealsLe.recordReveal
        (XmssSecurity.CappedChain.causalRecordedState secretKey chain input state) index value
          (by simpa using hcompatible)).trans
          (CausalRevealsLe.setCache _ _))

theorem causalInstalledTable_eq_of_agrees_of_revealsLe
    (table base : ChainValueIndex → Digest)
    (initial final : CausalHashState)
    (hinstalled : causalInstalledTable initial base = table)
    (hagrees : CausalRevealsAgree table final)
    (hle : CausalRevealsLe initial final) :
    causalInstalledTable final base = table := by
  funext index
  cases hfinal : final.revealed index with
  | some value =>
      rw [causalInstalledTable_of_revealed final base index value hfinal]
      exact (hagrees index value hfinal).symm
  | none =>
      have hinitial : initial.revealed index = none := by
        cases hvalue : initial.revealed index with
        | none => rfl
        | some value =>
            have := hle index value hvalue
            rw [hfinal] at this
            simp at this
      rw [causalInstalledTable_of_not_revealed final base index hfinal,
        ← hinstalled, causalInstalledTable_of_not_revealed initial base index
          hinitial]

end XmssSecurity.CappedChain
