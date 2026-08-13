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
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
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
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl⟩

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
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
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
  exact ⟨congrArg truncateHash hresult.1,
    hresult.2.1, hresult.2.2.1, hresult.2.2.2⟩

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
              leftResult.2 rightResult.2 ∧
            left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  intro steps
  induction steps with
  | zero =>
      intro value left right hagrees
      simp only [Concrete.chainTrajectory_zero, simulateQ_pure,
        StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl⟩
  | succ steps ih =>
      intro value left right hagrees
      rw [Concrete.chainTrajectory_succ,
        simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih value left right hagrees)
      intro leftPrior rightPrior hprior
      obtain ⟨hvalues, hcaches, hleftPrior, hrightPrior⟩ := hprior
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
        obtain ⟨hnextValue, hnextCaches, hleftNext, hrightNext⟩ := hnext
        obtain ⟨leftValue, leftNextCache⟩ := leftNext
        obtain ⟨rightValue, rightNextCache⟩ := rightNext
        dsimp only at hnextValue hnextCaches ⊢
        subst rightValue
        simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨rfl, hnextCaches,
          hleftPrior.trans hleftNext, hrightPrior.trans hrightNext⟩
      · simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure
          ⟨rfl, hcaches, hleftPrior, hrightPrior⟩

theorem relTriple_chainWalk_run_outside
    (parameter : PublicParameter) (chain candidate : ChainIndex)
    (hne : candidate ≠ chain) (epoch : Epoch) (position : Nat) :
    ∀ (steps : Nat) (value : Digest)
      (left right : QueryCache HashSpec),
      HashCachesAgreeOn (OutsideChainHashInput parameter chain) left right →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate
            position steps value)).run left)
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate
            position steps value)).run right)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            HashCachesAgreeOn (OutsideChainHashInput parameter chain)
              leftResult.2 rightResult.2 ∧
            left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  intro steps
  induction steps with
  | zero =>
      intro value left right hagrees
      simp only [Concrete.chainWalk, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl⟩
  | succ steps ih =>
      intro value left right hagrees
      rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih value left right hagrees)
      intro leftPrior rightPrior hprior
      obtain ⟨hvalues, hcaches, hleftPrior, hrightPrior⟩ := hprior
      obtain ⟨leftValue, leftCache⟩ := leftPrior
      obtain ⟨rightValue, rightCache⟩ := rightPrior
      dsimp only at hvalues hcaches ⊢
      subst rightValue
      split
      · rename_i hvalid
        exact relTriple_post_mono
          (relTriple_chainHash_run_outside parameter chain candidate hne
            epoch ⟨position + steps, hvalid⟩ leftValue
              leftCache rightCache hcaches)
          (fun _ _ hnext => ⟨hnext.1, hnext.2.1,
            hleftPrior.trans hnext.2.2.1,
            hrightPrior.trans hnext.2.2.2⟩)
      · exact relTriple_pure_pure
          ⟨rfl, hcaches, hleftPrior, hrightPrior⟩

theorem simulate_chainWalk_run_eq_pure_of_table_matches
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (hseeds : ChainTableSeedsMatch secretKey chain table)
    (hedges : ChainTableEdgesMatch cache secretKey.parameter chain table)
    (epoch : Epoch) : ∀ (steps : Nat) (hsteps : steps < chainLength),
    (simulateQ randomOracle
      (Concrete.chainWalk secretKey.parameter epoch chain 0 steps
        (secretKey.chainStart epoch chain))).run cache =
      pure (table (epoch, ⟨steps, hsteps⟩), cache) := by
  intro steps
  induction steps with
  | zero =>
      intro hsteps
      simp [Concrete.chainWalk, hseeds epoch]
  | succ steps ih =>
      intro hsteps
      have hprevious : steps < chainLength := by omega
      have hedgeStep : steps < chainLength - 1 := by omega
      rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind,
        ih hprevious]
      simp only [pure_bind]
      split
      · rename_i hvalid
        simp only [zero_add] at hvalid ⊢
        let edge : ChainEdgeIndex := (epoch, ⟨steps, hedgeStep⟩)
        obtain ⟨output, hcached, htruncate⟩ := hedges edge
        let input := chainTableEdgeInput
          secretKey.parameter chain table edge
        change (fun result : HashOutput × QueryCache HashSpec =>
          (truncateHash result.1, result.2)) <$>
            (randomOracle input).run cache = _
        rw [randomOracle, QueryImpl.withCaching_run_some _ hcached]
        simp [htruncate, chainTableEdgeTarget, chainStepNextDigit, edge]
      · rename_i hinvalid
        omega

theorem relTriple_keygenChainWalk_run
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (epoch : Epoch) (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      ⟨parameter, leftSecret⟩ selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      ⟨parameter, rightSecret⟩ selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight
      parameter selected rightTable)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 (chainLength - 1)
          (leftSecret epoch candidate))).run left)
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 (chainLength - 1)
          (rightSecret epoch candidate))).run right)
      (fun leftResult rightResult =>
        (candidate ≠ selected → leftResult.1 = rightResult.1) ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          initialLeft ≤ leftResult.2 ∧
          initialRight ≤ rightResult.2) := by
  by_cases hcandidate : candidate = selected
  · subst candidate
    have hsteps : chainLength - 1 < chainLength := by
      simp [chainLength]
    rw [simulate_chainWalk_run_eq_pure_of_table_matches left
        ⟨parameter, leftSecret⟩ selected leftTable hleftSeeds
          (hleftEdges.mono hleftLe) epoch (chainLength - 1) hsteps,
      simulate_chainWalk_run_eq_pure_of_table_matches right
        ⟨parameter, rightSecret⟩ selected rightTable hrightSeeds
          (hrightEdges.mono hrightLe) epoch (chainLength - 1) hsteps]
    exact relTriple_pure_pure
      ⟨fun hne => (hne rfl).elim, hagrees, hleftLe, hrightLe⟩
  · have hsecret : leftSecret epoch candidate =
        rightSecret epoch candidate :=
      secret_eq_of_outsideChain_eq selected leftSecret rightSecret
        houtside epoch candidate hcandidate
    rw [← hsecret]
    apply relTriple_post_mono
      (relTriple_chainWalk_run_outside parameter selected candidate
        hcandidate epoch 0 (chainLength - 1)
          (leftSecret epoch candidate) left right hagrees)
    intro leftResult rightResult hresult
    exact ⟨fun _ => hresult.1, hresult.2.1,
      hleftLe.trans hresult.2.2.1,
      hrightLe.trans hresult.2.2.2⟩

theorem relTriple_simulate_sequenceFin_run
    {n : Nat} {alpha : Type}
    (leftComputation rightComputation : Fin n → OracleComp HashSpec alpha)
    (StateRelation : QueryCache HashSpec → QueryCache HashSpec → Prop)
    (ValueRelation : Fin n → alpha → alpha → Prop)
    (hstep : ∀ index left right, StateRelation left right →
      RelTriple
        ((simulateQ randomOracle (leftComputation index)).run left)
        ((simulateQ randomOracle (rightComputation index)).run right)
        (fun leftResult rightResult =>
          ValueRelation index leftResult.1 rightResult.1 ∧
            StateRelation leftResult.2 rightResult.2))
    (left right : QueryCache HashSpec) (hstate : StateRelation left right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.sequenceFin leftComputation)).run left)
      ((simulateQ randomOracle
        (Concrete.sequenceFin rightComputation)).run right)
      (fun leftResult rightResult =>
        (∀ index, ValueRelation index
          (leftResult.1 index) (rightResult.1 index)) ∧
        StateRelation leftResult.2 rightResult.2) := by
  induction n generalizing left right with
  | zero =>
      simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact ⟨fun index => Fin.elim0 index, hstate⟩
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (hstep 0 left right hstate)
      intro leftHeadResult rightHeadResult hhead
      obtain ⟨hheadValue, hheadState⟩ := hhead
      obtain ⟨leftHead, leftHeadState⟩ := leftHeadResult
      obtain ⟨rightHead, rightHeadState⟩ := rightHeadResult
      dsimp only at hheadValue hheadState ⊢
      apply relTriple_bind
        (ih (fun index => leftComputation index.succ)
          (fun index => rightComputation index.succ)
          (fun index => ValueRelation index.succ)
          (fun index left right hrelation =>
            hstep index.succ left right hrelation)
          leftHeadState rightHeadState hheadState)
      intro leftTailResult rightTailResult htail
      obtain ⟨htailValues, htailState⟩ := htail
      obtain ⟨leftTail, leftTailState⟩ := leftTailResult
      obtain ⟨rightTail, rightTailState⟩ := rightTailResult
      dsimp only at htailValues htailState ⊢
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨?_, htailState⟩
      intro index
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact hheadValue
      · exact htailValues tailIndex

theorem relTriple_sequenceFin_keygenChainWalk_run
    (parameter : PublicParameter) (selected : ChainIndex) (epoch : Epoch)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      ⟨parameter, leftSecret⟩ selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      ⟨parameter, rightSecret⟩ selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight
      parameter selected rightTable) :
    ∀ (count : Nat) (chainAt : Fin count → ChainIndex)
      (left right : QueryCache HashSpec),
      HashCachesAgreeOn (OutsideChainHashInput parameter selected) left right →
      initialLeft ≤ left → initialRight ≤ right →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.sequenceFin fun index =>
            Concrete.chainWalk parameter epoch (chainAt index) 0
              (chainLength - 1) (leftSecret epoch (chainAt index)) :
            OracleComp HashSpec (Fin count → Digest))).run left)
        ((simulateQ randomOracle
          (Concrete.sequenceFin fun index =>
            Concrete.chainWalk parameter epoch (chainAt index) 0
              (chainLength - 1) (rightSecret epoch (chainAt index)) :
            OracleComp HashSpec (Fin count → Digest))).run right)
        (fun leftResult rightResult =>
          (∀ index, chainAt index ≠ selected →
            leftResult.1 index = rightResult.1 index) ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          initialLeft ≤ leftResult.2 ∧
          initialRight ≤ rightResult.2) := by
  intro count chainAt left right hagrees hleftLe hrightLe
  let StateRelation := fun
      (left right : QueryCache HashSpec) =>
    HashCachesAgreeOn (OutsideChainHashInput parameter selected) left right ∧
      initialLeft ≤ left ∧ initialRight ≤ right
  let ValueRelation := fun (index : Fin count) (left right : Digest) =>
    chainAt index ≠ selected → left = right
  have hstep : ∀ index left right, StateRelation left right →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch (chainAt index) 0
            (chainLength - 1) (leftSecret epoch (chainAt index)))).run left)
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch (chainAt index) 0
            (chainLength - 1) (rightSecret epoch (chainAt index)))).run right)
        (fun leftResult rightResult =>
          ValueRelation index leftResult.1 rightResult.1 ∧
            StateRelation leftResult.2 rightResult.2) := by
    intro index currentLeft currentRight hstate
    exact relTriple_keygenChainWalk_run parameter selected (chainAt index) epoch
      leftSecret rightSecret leftTable rightTable initialLeft initialRight
      houtside hleftSeeds hleftEdges hrightSeeds hrightEdges
      currentLeft currentRight hstate.1 hstate.2.1 hstate.2.2
  simpa [StateRelation, ValueRelation] using
    (relTriple_simulate_sequenceFin_run
      (fun index => Concrete.chainWalk parameter epoch (chainAt index) 0
        (chainLength - 1) (leftSecret epoch (chainAt index)))
      (fun index => Concrete.chainWalk parameter epoch (chainAt index) 0
        (chainLength - 1) (rightSecret epoch (chainAt index)))
      StateRelation ValueRelation hstep left right
        ⟨hagrees, hleftLe, hrightLe⟩)

end XmssSecurity
