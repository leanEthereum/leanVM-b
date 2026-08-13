import XmssSecurity.CausalPairedKeygen

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def HashCachesAgreeOn (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ input, inputs input → left input = right input

theorem HashCachesAgreeOn.cacheQuery
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (input : HashInput) (output : HashOutput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate hcandidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hagrees candidate hcandidate

theorem relTriple_randomOracle_run_of_cachesAgreeOn
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (input : HashInput) (hinput : inputs input)
    (hagrees : HashCachesAgreeOn inputs left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees⟩

def OutsideChainHashInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (input : HashInput) : Prop :=
  ∃ epoch candidate step,
    candidate ≠ chain ∧
      AtHashAddress parameter (.chain epoch candidate step) input

theorem CoupledFixedChainMaterialBaseRelation.outsideChainCachesAgree
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter chain left right) :
    HashCachesAgreeOn (OutsideChainHashInput parameter chain)
      left.2.2.2 right.1.2.2.2 := by
  intro input hinput
  obtain ⟨epoch, candidate, step, hne, haddress⟩ := hinput
  rw [fixedChainMaterialRepresentation_cache_avoids_otherChain
      parameter chain candidate hne left hrel.2.2.1
        epoch step input haddress,
    fixedChainMaterialRepresentation_cache_avoids_otherChain
      parameter chain candidate hne right.1 hrel.2.2.2
        epoch step input haddress]

theorem outsideChainHashInput_chainInput
    (parameter : PublicParameter) (chain candidate : ChainIndex)
    (hne : candidate ≠ chain) (epoch : Epoch) (step : ChainStep)
    (value : Digest) :
    OutsideChainHashInput parameter chain
      (Concrete.CacheView.chainInput
        parameter epoch candidate step value) := by
  refine ⟨epoch, candidate, step, hne, ?_⟩
  simp [Concrete.CacheView.chainInput]

theorem relTriple_chainHash_run_outside
    (parameter : PublicParameter) (chain candidate : ChainIndex)
    (hne : candidate ≠ chain) (epoch : Epoch) (step : ChainStep)
    (value : Digest) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter chain) left right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.chainHash parameter epoch candidate step value :
          OracleComp HashSpec Digest)).run left)
      ((simulateQ randomOracle
        (Concrete.chainHash parameter epoch candidate step value :
          OracleComp HashSpec Digest)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter chain)
            leftResult.2 rightResult.2) := by
  let input := Concrete.CacheView.chainInput
    parameter epoch candidate step value
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle input).run left)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle input).run right) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_run_of_cachesAgreeOn
      (OutsideChainHashInput parameter chain) left right input
        (outsideChainHashInput_chainInput
          parameter chain candidate hne epoch step value) hagrees)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_chainTrajectory_run_outside
    (parameter : PublicParameter) (chain candidate : ChainIndex)
    (hne : candidate ≠ chain) (epoch : Epoch) (position : Nat) :
    ∀ (steps : Nat) (value : Digest)
      (left right : QueryCache HashSpec),
      HashCachesAgreeOn (OutsideChainHashInput parameter chain) left right →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch candidate
            position steps value)).run left)
        ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch candidate
            position steps value)).run right)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            HashCachesAgreeOn (OutsideChainHashInput parameter chain)
              leftResult.2 rightResult.2) := by
  intro steps
  induction steps with
  | zero =>
      intro value left right hagrees
      simp only [Concrete.chainTrajectory_zero, simulateQ_pure,
        StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, hagrees⟩
  | succ steps ih =>
      intro value left right hagrees
      rw [Concrete.chainTrajectory_succ,
        simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih value left right hagrees)
      intro leftPrior rightPrior hprior
      obtain ⟨hvalues, hcaches⟩ := hprior
      obtain ⟨leftValues, leftCache⟩ := leftPrior
      obtain ⟨rightValues, rightCache⟩ := rightPrior
      dsimp only at hvalues hcaches ⊢
      subst rightValues
      split
      · rename_i hvalid
        rw [simulateQ_bind, StateT.run_bind]
        apply relTriple_bind
          (relTriple_chainHash_run_outside parameter chain candidate hne
            epoch ⟨position + steps, hvalid⟩ leftValues.back
              leftCache rightCache hcaches)
        intro leftNext rightNext hnext
        obtain ⟨hnextValue, hnextCaches⟩ := hnext
        obtain ⟨leftValue, leftNextCache⟩ := leftNext
        obtain ⟨rightValue, rightNextCache⟩ := rightNext
        dsimp only at hnextValue hnextCaches ⊢
        subst rightValue
        simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨rfl, hnextCaches⟩
      · simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨rfl, hcaches⟩

end XmssSecurity
