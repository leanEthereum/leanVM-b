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

theorem HashCachesAgreeOn.cacheQuery_distinct
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ candidate, inputs candidate → candidate ≠ leftInput)
    (hright : ∀ candidate, inputs candidate → candidate ≠ rightInput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery leftInput output)
      (right.cacheQuery rightInput output) := by
  intro candidate hcandidate
  rw [QueryCache.cacheQuery_of_ne left output (hleft candidate hcandidate),
    QueryCache.cacheQuery_of_ne right output (hright candidate hcandidate)]
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

theorem relTriple_randomOracle_run_of_both_none
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (leftInput rightInput : HashInput)
    (hleftNone : left leftInput = none)
    (hrightNone : right rightInput = none)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hleft : ∀ candidate, inputs candidate → candidate ≠ leftInput)
    (hright : ∀ candidate, inputs candidate → candidate ≠ rightInput) :
    RelTriple
      ((randomOracle leftInput).run left)
      ((randomOracle rightInput).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hleftNone,
    QueryImpl.withCaching_run_none _ hrightNone,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
  intro leftOutput rightOutput houtput
  subst rightOutput
  exact relTriple_pure_pure ⟨rfl,
    HashCachesAgreeOn.cacheQuery_distinct inputs left right hagrees
      leftInput rightInput leftOutput hleft hright,
    QueryCache.le_cacheQuery left hleftNone,
    QueryCache.le_cacheQuery right hrightNone⟩

theorem relTriple_strengthen_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    {leftProperty : alpha → Prop} {rightProperty : beta → Prop}
    (hrel : RelTriple left right relation)
    (hleft : ∀ result ∈ support left, leftProperty result)
    (hright : ∀ result ∈ support right, rightProperty result) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftProperty leftResult ∧ rightProperty rightResult) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel ⊢
  obtain ⟨coupling, hcoupling⟩ := hrel
  refine ⟨coupling, ?_⟩
  intro pair hpair
  have hleftSupportDist : pair.1 ∈ support 𝒟[left] := by
    rw [← coupling.2.map_fst, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hrightSupportDist : pair.2 ∈ support 𝒟[right] := by
    rw [← coupling.2.map_snd, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hleftSupport : pair.1 ∈ support left := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleftSupportDist ⊢
    simpa using hleftSupportDist
  have hrightSupport : pair.2 ∈ support right := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hrightSupportDist ⊢
    simpa using hrightSupportDist
  exact ⟨hcoupling pair hpair,
    hleft pair.1 hleftSupport, hright pair.2 hrightSupport⟩

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

theorem outsideChainHashInput_ne_leafInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (input : HashInput)
    (hinput : OutsideChainHashInput parameter chain input) :
    input ≠ Concrete.CacheView.leafInput parameter epoch endpoints := by
  intro heq
  obtain ⟨targetEpoch, candidate, step, _hne, hchain⟩ := hinput
  have hleaf : AtHashAddress parameter (.leaf epoch) input := by
    rw [heq]
    simp [Concrete.CacheView.leafInput]
  have hdomain := atHashAddress_unique parameter
    (.chain targetEpoch candidate step) (.leaf epoch) input hchain hleaf
  simp at hdomain

theorem relTriple_leafHash_run_of_both_none
    (parameter : PublicParameter) (chain : ChainIndex) (epoch : Epoch)
    (leftEndpoints rightEndpoints : ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hleftNone : left (Concrete.CacheView.leafInput
      parameter epoch leftEndpoints) = none)
    (hrightNone : right (Concrete.CacheView.leafInput
      parameter epoch rightEndpoints) = none)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter chain) left right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch leftEndpoints :
          OracleComp HashSpec Digest)).run left)
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch rightEndpoints :
          OracleComp HashSpec Digest)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter chain)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  let leftInput := Concrete.CacheView.leafInput
    parameter epoch leftEndpoints
  let rightInput := Concrete.CacheView.leafInput
    parameter epoch rightEndpoints
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle leftInput).run left)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle rightInput).run right) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_run_of_both_none
      (OutsideChainHashInput parameter chain) left right
      leftInput rightInput hleftNone hrightNone hagrees
      (outsideChainHashInput_ne_leafInput
        parameter chain epoch leftEndpoints)
      (outsideChainHashInput_ne_leafInput
        parameter chain epoch rightEndpoints))
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1,
    hresult.2.1, hresult.2.2.1, hresult.2.2.2⟩

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

theorem oneTimePublicKey_run_leafInput_none
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec)
    (habsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      initialCache input = none)
    (result : (ChainIndex → Digest) × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache)) :
    result.2 (Concrete.CacheView.leafInput parameter epoch result.1) = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.oneTimePublicKey parameter secret epoch)
    (Concrete.CacheView.leafInput parameter epoch result.1)
    initialCache result.2 result.1
  · apply OracleComp.IsQueryBoundP.of_imp
      (p' := AtHashAddress parameter (.leaf epoch))
    · intro input heq
      subst input
      simp [Concrete.CacheView.leafInput]
    · exact Concrete.oneTimePublicKey_queryBound_zero_leafAddress
        parameter secret epoch epoch
  · exact habsent _ (by simp [Concrete.CacheView.leafInput])
  · exact hresult

theorem relTriple_fixedChainMaterial_oneTimePublicKey_run_from_cache
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter selected left right) (epoch : Epoch)
    (leftCache rightCache : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) leftCache rightCache)
    (hleftLe : left.2.2.2 ≤ leftCache)
    (hrightLe : right.1.2.2.2 ≤ rightCache) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter
          (unflattenSecret left.1.2) epoch)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter
          (unflattenSecret right.1.1.2) epoch)).run rightCache)
      (fun leftResult rightResult =>
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        left.2.2.2 ≤ leftResult.2 ∧
        right.1.2.2.2 ≤ rightResult.2) := by
  have hleftMatches := fixedChainMaterialRepresentation_matches
    parameter selected left hrel.2.2.1
  have hrightMatches := fixedChainMaterialRepresentation_matches
    parameter selected right.1 hrel.2.2.2
  have houtside : secretOutsideChain selected (unflattenSecret left.1.2) =
      secretOutsideChain selected (unflattenSecret right.1.1.2) :=
    secretOutsideChain_eq_of_outsideChainSecret_eq selected
      left.1.2 right.1.1.2 hrel.2.1
  simpa [Concrete.oneTimePublicKey] using
    (relTriple_sequenceFin_keygenChainWalk_run parameter selected epoch
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      (fixedChainMaterialTable selected left)
      (fixedChainMaterialTable selected right.1)
      left.2.2.2 right.1.2.2.2 houtside
      hleftMatches.1 hleftMatches.2 hrightMatches.1 hrightMatches.2
      numChains (fun chain => chain) leftCache rightCache hagrees
      hleftLe hrightLe)

theorem relTriple_fixedChainMaterial_oneTimePublicKey_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter selected left right) (epoch : Epoch) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter
          (unflattenSecret left.1.2) epoch)).run left.2.2.2)
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter
          (unflattenSecret right.1.1.2) epoch)).run right.1.2.2.2)
      (fun leftResult rightResult =>
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        left.2.2.2 ≤ leftResult.2 ∧
        right.1.2.2.2 ≤ rightResult.2) := by
  exact relTriple_fixedChainMaterial_oneTimePublicKey_run_from_cache
    parameter selected left right hrel epoch left.2.2.2 right.1.2.2.2
    (hrel.outsideChainCachesAgree parameter selected left right) le_rfl le_rfl

theorem relTriple_fixedChainMaterial_leafAt_run_from_cache
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter selected left right) (epoch : Epoch)
    (leftCache rightCache : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) leftCache rightCache)
    (hleftLe : left.2.2.2 ≤ leftCache)
    (hrightLe : right.1.2.2.2 ≤ rightCache)
    (hleftAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      leftCache input = none)
    (hrightAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      rightCache input = none) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret left.1.2) epoch :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret right.1.1.2) epoch :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2) := by
  let leftComputation :=
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter
        (unflattenSecret left.1.2) epoch)).run leftCache
  let rightComputation :=
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter
        (unflattenSecret right.1.1.2) epoch)).run rightCache
  have hots := relTriple_fixedChainMaterial_oneTimePublicKey_run_from_cache
    parameter selected left right hrel epoch leftCache rightCache
      hagrees hleftLe hrightLe
  have hotsFresh := relTriple_strengthen_support hots
    (oneTimePublicKey_run_leafInput_none parameter
      (unflattenSecret left.1.2) epoch leftCache hleftAbsent)
    (oneTimePublicKey_run_leafInput_none parameter
      (unflattenSecret right.1.1.2) epoch rightCache hrightAbsent)
  unfold Concrete.leafAt
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind hotsFresh
  intro leftEndpointsResult rightEndpointsResult hresult
  obtain ⟨hotsResult, hleftFresh, hrightFresh⟩ := hresult
  obtain ⟨leftEndpoints, leftCache⟩ := leftEndpointsResult
  obtain ⟨rightEndpoints, rightCache⟩ := rightEndpointsResult
  dsimp only at hotsResult hleftFresh hrightFresh ⊢
  apply relTriple_post_mono
    (relTriple_leafHash_run_of_both_none parameter selected epoch
      leftEndpoints rightEndpoints leftCache rightCache
      hleftFresh hrightFresh hotsResult.2.1)
  intro leftResult rightResult hleaf
  exact ⟨hleaf.1, hleaf.2.1,
    hotsResult.2.2.1.trans hleaf.2.2.1,
    hotsResult.2.2.2.trans hleaf.2.2.2⟩

theorem relTriple_fixedChainMaterial_leafAt_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter selected left right) (epoch : Epoch) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret left.1.2) epoch :
          OracleComp HashSpec Digest)).run left.2.2.2)
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret right.1.1.2) epoch :
          OracleComp HashSpec Digest)).run right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2) := by
  apply relTriple_fixedChainMaterial_leafAt_run_from_cache
    parameter selected left right hrel epoch left.2.2.2 right.1.2.2.2
    (hrel.outsideChainCachesAgree parameter selected left right) le_rfl le_rfl
  · intro input hinput
    exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected left hrel.2.2.1 epoch input hinput
  · intro input hinput
    exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected right.1 hrel.2.2.2 epoch input hinput

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_leafTreeValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation parameter selected left right) :
    ∀ (indices : List TreeValueIndex),
      (∀ index ∈ indices, index.1.val = 0) →
      indices.Pairwise TreeValueIndex.Precedes →
      ∀ (leftCache rightCache : QueryCache HashSpec),
        TreeValuesFresh parameter indices leftCache →
        TreeValuesFresh parameter indices rightCache →
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftCache rightCache →
        left.2.2.2 ≤ leftCache → right.1.2.2.2 ≤ rightCache →
        RelTriple
          (treeValues parameter (unflattenSecret left.1.2) indices leftCache)
          (treeValues parameter (unflattenSecret right.1.1.2) indices rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              HashCachesAgreeOn (OutsideChainHashInput parameter selected)
                leftResult.2 rightResult.2 ∧
              left.2.2.2 ≤ leftResult.2 ∧
              right.1.2.2.2 ≤ rightResult.2) := by
  intro indices
  induction indices with
  | nil =>
      intro _hzero _hordered leftCache rightCache _hleftFresh _hrightFresh
        hagrees hleftLe hrightLe
      simp only [treeValues_nil]
      exact relTriple_pure_pure ⟨rfl, hagrees, hleftLe, hrightLe⟩
  | cons current indices ih =>
      intro hzero hordered leftCache rightCache hleftFresh hrightFresh
        hagrees hleftLe hrightLe
      have hcurrentZero : current.1.val = 0 := hzero current (by simp)
      have htailZero : ∀ index ∈ indices, index.1.val = 0 := by
        intro index hindex
        exact hzero index (by simp [hindex])
      have hcurrentBefore : ∀ target ∈ indices,
          current.Precedes target := (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hleftAbsent : ∀ input,
          AtHashAddress parameter (.leaf current.node) input →
            leftCache input = none := by
        intro input hinput
        apply hleftFresh current (by simp) input
        unfold TreeValueIndex.domain
        rw [dif_pos hcurrentZero]
        exact hinput
      have hrightAbsent : ∀ input,
          AtHashAddress parameter (.leaf current.node) input →
            rightCache input = none := by
        intro input hinput
        apply hrightFresh current (by simp) input
        unfold TreeValueIndex.domain
        rw [dif_pos hcurrentZero]
        exact hinput
      have hhead : RelTriple
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret left.1.2))).run
              leftCache)
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret right.1.1.2))).run
              rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              HashCachesAgreeOn (OutsideChainHashInput parameter selected)
                leftResult.2 rightResult.2 ∧
              left.2.2.2 ≤ leftResult.2 ∧
              right.1.2.2.2 ≤ rightResult.2) := by
        simpa [TreeValueIndex.computation, hcurrentZero] using
          (relTriple_fixedChainMaterial_leafAt_run_from_cache
            parameter selected left right hrel current.node
            leftCache rightCache hagrees hleftLe hrightLe
            hleftAbsent hrightAbsent)
      have hheadFresh := relTriple_strengthen_support hhead
        (fun result hresult =>
          treeValue_preserves_tail_fresh parameter
            (unflattenSecret left.1.2) current indices hcurrentBefore
            leftCache hleftFresh result hresult)
        (fun result hresult =>
          treeValue_preserves_tail_fresh parameter
            (unflattenSecret right.1.1.2) current indices hcurrentBefore
            rightCache hrightFresh result hresult)
      simp only [treeValues_cons]
      apply relTriple_bind hheadFresh
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftTailFresh, hrightTailFresh⟩ := hheadResult
      obtain ⟨leftHead, leftHeadCache⟩ := leftHeadResult
      obtain ⟨rightHead, rightHeadCache⟩ := rightHeadResult
      dsimp only at hheadRelation hleftTailFresh hrightTailFresh ⊢
      apply relTriple_bind
        (ih htailZero htailOrdered leftHeadCache rightHeadCache
          hleftTailFresh hrightTailFresh hheadRelation.2.1
          hheadRelation.2.2.1 hheadRelation.2.2.2)
      intro leftTailResult rightTailResult htailResult
      obtain ⟨leftTail, leftTailCache⟩ := leftTailResult
      obtain ⟨rightTail, rightTailCache⟩ := rightTailResult
      dsimp only at htailResult ⊢
      apply relTriple_pure_pure
      exact ⟨congrArg₂ List.cons hheadRelation.1 htailResult.1,
        htailResult.2.1, htailResult.2.2.1, htailResult.2.2.2⟩

theorem relTriple_fixedChainMaterial_allLeafValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesAtHeight 0) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesAtHeight 0) right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2) := by
  have hzero : ∀ index ∈ treeValueIndicesAtHeight 0,
      index.1.val = 0 := by
    intro index hindex
    rw [treeValueIndicesAtHeight, List.mem_ofFn] at hindex
    obtain ⟨node, rfl⟩ := hindex
    rfl
  have hordered : (treeValueIndicesAtHeight 0).Pairwise
      TreeValueIndex.Precedes := by
    simp only [treeValueIndicesAtHeight, List.pairwise_ofFn]
    intro leftNode rightNode hlt
    exact Or.inr ⟨rfl, hlt⟩
  have hleftFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) left.2.2.2 := by
    intro index hindex input hinput
    have hheight := hzero index hindex
    unfold TreeValueIndex.domain at hinput
    rw [dif_pos hheight] at hinput
    exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected left hrel.2.2.1 index.node input hinput
  have hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) right.1.2.2.2 := by
    intro index hindex input hinput
    have hheight := hzero index hindex
    unfold TreeValueIndex.domain at hinput
    rw [dif_pos hheight] at hinput
    exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected right.1 hrel.2.2.2 index.node input hinput
  exact relTriple_fixedChainMaterial_leafTreeValues_run
    parameter selected left right hrel (treeValueIndicesAtHeight 0)
    hzero hordered left.2.2.2 right.1.2.2.2 hleftFresh hrightFresh
    (hrel.outsideChainCachesAgree parameter selected left right) le_rfl le_rfl

end XmssSecurity
