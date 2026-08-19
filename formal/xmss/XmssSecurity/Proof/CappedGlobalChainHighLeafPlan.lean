import XmssSecurity.Proof.CappedGlobalChainHighAttackerHashDisjointness

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

inductive GlobalFilteredCausalHashPlan where
  | cached (output : HashOutput)
  | reveal (index : GlobalChainValueIndex)
  | probeThenFresh (index : GlobalChainValueIndex) (target : Digest)
  | redirect (output : HashOutput)
  | fresh

structure GlobalLeafInputData where
  epoch : Epoch
  endpoints : ChainIndex → Digest

noncomputable def globalLeafInputData?
    (parameter : PublicParameter) (input : HashInput) :
    Option GlobalLeafInputData := by
  classical
  exact
  if h : ∃ data : GlobalLeafInputData,
      input = Concrete.CacheView.leafInput parameter data.epoch data.endpoints then
    some h.choose
  else none

theorem globalLeafInputData?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput)
    (data : GlobalLeafInputData) :
    globalLeafInputData? parameter input = some data ↔
      input = Concrete.CacheView.leafInput parameter data.epoch data.endpoints := by
  constructor
  · intro hdata
    unfold globalLeafInputData? at hdata
    split at hdata
    · rename_i hexists
      have heq : hexists.choose = data := by simpa using hdata
      rw [← heq]
      exact hexists.choose_spec
    · simp at hdata
  · intro hinput
    unfold globalLeafInputData?
    split
    · rename_i hexists
      have hchosen := hexists.choose_spec
      have heq := (Concrete.CacheView.leafInput_eq_iff parameter
        hexists.choose.epoch data.epoch hexists.choose.endpoints
          data.endpoints).mp (hchosen.symm.trans hinput)
      apply congrArg some
      cases hchosenData : hexists.choose with
      | mk chosenEpoch chosenEndpoints =>
          cases hdata : data with
          | mk epoch endpoints =>
              simp only [hchosenData, hdata] at heq ⊢
              obtain ⟨rfl, rfl⟩ := heq
              rfl
    · rename_i hnone
      exact (hnone ⟨data, hinput⟩).elim

@[simp]
theorem globalLeafInputData?_leafInput
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    globalLeafInputData? parameter
        (Concrete.CacheView.leafInput parameter epoch endpoints) =
      some ⟨epoch, endpoints⟩ := by
  rw [globalLeafInputData?_eq_some_iff]

noncomputable def globalHiddenLeafProbe?
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ chain : ChainIndex,
      state.revealed (chain, epoch, chainEndpointDigit) = none then
    let chain := h.choose
    some ((chain, epoch, chainEndpointDigit), endpoints chain)
  else none

theorem globalHiddenLeafProbe?_eq_some
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest) :
    globalHiddenLeafProbe? state epoch endpoints = some (index, target) →
      ∃ chain : ChainIndex,
        index = (chain, epoch, chainEndpointDigit) ∧
        target = endpoints chain ∧
        state.revealed index = none := by
  intro hprobe
  unfold globalHiddenLeafProbe? at hprobe
  split at hprobe
  · rename_i hexists
    simp only [Option.some.injEq, Prod.mk.injEq] at hprobe
    refine ⟨hexists.choose, hprobe.1.symm, hprobe.2.symm, ?_⟩
    simpa [hprobe.1] using hexists.choose_spec
  · simp at hprobe

theorem globalHiddenLeafProbe?_eq_none_iff
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    globalHiddenLeafProbe? state epoch endpoints = none ↔
      ∀ chain : ChainIndex,
        state.revealed (chain, epoch, chainEndpointDigit) ≠ none := by
  unfold globalHiddenLeafProbe?
  split
  · rename_i hexists
    constructor
    · intro himpossible
      simp at himpossible
    · intro hall
      exact (hall hexists.choose hexists.choose_spec).elim
  · rename_i hnone
    constructor
    · intro _ chain hhidden
      exact hnone ⟨chain, hhidden⟩
    · intro _
      rfl

def GlobalLeafRevealsMatch
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : Prop :=
  ∀ chain : ChainIndex,
    state.revealed (chain, epoch, chainEndpointDigit) = some (endpoints chain)

noncomputable def globalFilteredCausalLeafHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalFilteredCausalHashPlan := by
  classical
  exact
  match globalLeafInputData? secretKey.parameter input with
  | none => .fresh
  | some data =>
      match globalHiddenLeafProbe? state data.epoch data.endpoints with
      | some (index, target) => .probeThenFresh index target
      | none =>
          if GlobalLeafRevealsMatch state data.epoch data.endpoints then
            match state.keygenCache
                (keygenLeafTargetInput secretKey state.keygenCache input) with
            | some output => .redirect output
            | none => .fresh
          else .fresh

end XmssSecurity.CappedChain
