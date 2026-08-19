import XmssSecurity.Proof.CappedGlobalCausalActionResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

def GlobalCausalRevealsAgree
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

theorem globalCausalRevealsAgree_empty
    (table : GlobalChainValueIndex → Digest) :
    GlobalCausalRevealsAgree table GlobalCausalHashState.empty := by
  intro index value hvalue
  simp [GlobalCausalHashState.empty] at hvalue

theorem GlobalCausalRevealsAgree.finishKeygen
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state) :
    GlobalCausalRevealsAgree table state.finishKeygen :=
  hagrees

theorem GlobalCausalRevealsAgree.recordProbe
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalRevealsAgree table (state.recordProbe probe) := by
  cases probe <;> exact hagrees

theorem GlobalCausalRevealsAgree.globalCausalRecordedState
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalRevealsAgree table
      (globalCausalRecordedState secretKey input state) := by
  unfold XmssSecurity.CappedChain.globalCausalRecordedState
  exact hagrees.recordProbe _

theorem GlobalCausalRevealsAgree.setCache
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state)
    (cache : QueryCache HashSpec) :
    GlobalCausalRevealsAgree table { state with cache := cache } :=
  hagrees

theorem GlobalCausalRevealsAgree.recordReveal
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state)
    (index : GlobalChainValueIndex) (value : Digest)
    (hvalue : table index = value) :
    GlobalCausalRevealsAgree table (state.recordReveal index value) := by
  intro candidate candidateValue hcand
  by_cases heq : candidate = index
  · subst candidate
    simp [GlobalCausalHashState.recordReveal] at hcand
    subst candidateValue
    exact hvalue
  · simp [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] at hcand
    exact hagrees candidate candidateValue hcand

theorem GlobalCausalRevealsAgree.globalCausalRevealResultState
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalCausalRevealsAgree table state)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (output : HashOutput) (hvalue : table index = value) :
    GlobalCausalRevealsAgree table
      (globalCausalRevealResultState secretKey input state
        index value output) := by
  unfold XmssSecurity.CappedChain.globalCausalRevealResultState
  exact ((hagrees.globalCausalRecordedState secretKey input).recordReveal
    index value hvalue).setCache _

def globalCausalInstalledTable
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest) :
    GlobalChainValueIndex → Digest :=
  fun index => (state.revealed index).getD (base index)

@[simp]
theorem globalCausalInstalledTable_empty
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable GlobalCausalHashState.empty base = base := by
  funext index
  rfl

theorem globalCausalInstalledTable_of_revealed
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (value : Digest)
    (hrevealed : state.revealed index = some value) :
    globalCausalInstalledTable state base index = value := by
  simp [globalCausalInstalledTable, hrevealed]

theorem globalCausalInstalledTable_of_not_revealed
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex)
    (hrevealed : state.revealed index = none) :
    globalCausalInstalledTable state base index = base index := by
  simp [globalCausalInstalledTable, hrevealed]

theorem globalCausalInstalledTable_recordProbe
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    globalCausalInstalledTable (state.recordProbe probe) base =
      globalCausalInstalledTable state base :=
  rfl

theorem globalCausalInstalledTable_globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable
        (globalCausalRecordedState secretKey input state) base =
      globalCausalInstalledTable state base := by
  rw [globalCausalRecordedState]
  exact globalCausalInstalledTable_recordProbe state base _

theorem globalCausalInstalledTable_setCache
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (cache : QueryCache HashSpec) :
    globalCausalInstalledTable { state with cache := cache } base =
      globalCausalInstalledTable state base :=
  rfl

theorem globalCausalInstalledTable_finishKeygen
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable state.finishKeygen base =
      globalCausalInstalledTable state base :=
  rfl

theorem globalCausalInstalledTable_recordReveal
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (value : Digest) :
    globalCausalInstalledTable (state.recordReveal index value) base =
      Function.update (globalCausalInstalledTable state base) index value := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [globalCausalInstalledTable, GlobalCausalHashState.recordReveal]
  · simp [globalCausalInstalledTable, GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq]

theorem globalCausalInstalledTable_update_base_of_revealed
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (value replacement : Digest)
    (hrevealed : state.revealed index = some value) :
    globalCausalInstalledTable state
        (Function.update base index replacement) =
      globalCausalInstalledTable state base := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [globalCausalInstalledTable, hrevealed]
  · simp [globalCausalInstalledTable, Function.update_of_ne heq]

@[simp]
theorem globalCausalRevealResultState_revealed_self
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) :
    (globalCausalRevealResultState secretKey input state index value output).revealed
      index = some value := by
  unfold globalCausalRevealResultState GlobalCausalHashState.recordReveal
  simp

theorem globalCausalInstalledTable_globalCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (value : Digest)
    (output : HashOutput) :
    globalCausalInstalledTable
        (globalCausalRevealResultState secretKey input state index value output)
        base =
      Function.update (globalCausalInstalledTable state base) index value := by
  unfold globalCausalRevealResultState
  rw [globalCausalInstalledTable_setCache,
    globalCausalInstalledTable_recordReveal,
    globalCausalInstalledTable_globalCausalRecordedState]

theorem globalCausalRevealsAgree_globalCausalInstalledTable
    (state : GlobalCausalHashState)
    (base : GlobalChainValueIndex → Digest) :
    GlobalCausalRevealsAgree (globalCausalInstalledTable state base) state := by
  intro index value hvalue
  exact globalCausalInstalledTable_of_revealed
    state base index value hvalue

def GlobalCausalRevealsLe
    (left right : GlobalCausalHashState) : Prop :=
  ∀ index value, left.revealed index = some value →
    right.revealed index = some value

theorem GlobalCausalRevealsLe.refl (state : GlobalCausalHashState) :
    GlobalCausalRevealsLe state state := by
  intro index value hvalue
  exact hvalue

theorem GlobalCausalRevealsLe.trans
    {left middle right : GlobalCausalHashState}
    (hleft : GlobalCausalRevealsLe left middle)
    (hright : GlobalCausalRevealsLe middle right) :
    GlobalCausalRevealsLe left right := by
  intro index value hvalue
  exact hright index value (hleft index value hvalue)

theorem GlobalCausalRevealsLe.recordProbe
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalRevealsLe state (state.recordProbe probe) := by
  intro index value hvalue
  exact hvalue

theorem GlobalCausalRevealsLe.globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    GlobalCausalRevealsLe state
      (globalCausalRecordedState secretKey input state) := by
  rw [XmssSecurity.CappedChain.globalCausalRecordedState]
  exact GlobalCausalRevealsLe.recordProbe state _

theorem GlobalCausalRevealsLe.setCache
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    GlobalCausalRevealsLe state { state with cache := cache } := by
  intro index value hvalue
  exact hvalue

theorem GlobalCausalRevealsLe.finishKeygen
    (state : GlobalCausalHashState) :
    GlobalCausalRevealsLe state state.finishKeygen := by
  intro index value hvalue
  exact hvalue

theorem GlobalCausalRevealsLe.recordReveal
    (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (value : Digest)
    (hcompatible : ∀ previous,
      state.revealed index = some previous → previous = value) :
    GlobalCausalRevealsLe state (state.recordReveal index value) := by
  intro candidate candidateValue hcandidate
  by_cases heq : candidate = index
  · subst candidate
    simp only [GlobalCausalHashState.recordReveal, Function.update_self]
    exact congrArg some (hcompatible candidateValue hcandidate).symm
  · simpa [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] using hcandidate

theorem GlobalCausalRevealsLe.globalCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput)
    (hcompatible : ∀ previous,
      state.revealed index = some previous → previous = value) :
    GlobalCausalRevealsLe state
      (globalCausalRevealResultState secretKey input state
        index value output) := by
  unfold XmssSecurity.CappedChain.globalCausalRevealResultState
  exact (GlobalCausalRevealsLe.globalCausalRecordedState
    secretKey input state).trans
      ((GlobalCausalRevealsLe.recordReveal
        (XmssSecurity.CappedChain.globalCausalRecordedState
          secretKey input state) index value (by simpa using hcompatible)).trans
          (GlobalCausalRevealsLe.setCache _ _))

theorem globalCausalInstalledTable_eq_of_agrees_of_revealsLe
    (table base : GlobalChainValueIndex → Digest)
    (initial final : GlobalCausalHashState)
    (hinstalled : globalCausalInstalledTable initial base = table)
    (hagrees : GlobalCausalRevealsAgree table final)
    (hle : GlobalCausalRevealsLe initial final) :
    globalCausalInstalledTable final base = table := by
  funext index
  cases hfinal : final.revealed index with
  | some value =>
      rw [globalCausalInstalledTable_of_revealed
        final base index value hfinal]
      exact (hagrees index value hfinal).symm
  | none =>
      have hinitial : initial.revealed index = none := by
        cases hvalue : initial.revealed index with
        | none => rfl
        | some value =>
            have hleValue := hle index value hvalue
            rw [hfinal] at hleValue
            simp at hleValue
      rw [globalCausalInstalledTable_of_not_revealed
          final base index hfinal,
        ← hinstalled,
        globalCausalInstalledTable_of_not_revealed
          initial base index hinitial]

end XmssSecurity.CappedChain
