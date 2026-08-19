import XmssSecurity.Proof.CausalPairedKeygen

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

theorem relTriple_with_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftResult ∈ support left ∧ rightResult ∈ support right) :=
  relTriple_strengthen_support hrel
    (fun _ hresult => hresult) (fun _ hresult => hresult)

theorem relTriple_with_support_four
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {first second third fourth : alpha → beta → Prop}
    (hrel : RelTriple left right (fun leftResult rightResult =>
      first leftResult rightResult ∧ second leftResult rightResult ∧
        third leftResult rightResult ∧ fourth leftResult rightResult)) :
    RelTriple left right (fun leftResult rightResult =>
      first leftResult rightResult ∧ second leftResult rightResult ∧
        third leftResult rightResult ∧ fourth leftResult rightResult ∧
        leftResult ∈ support left ∧ rightResult ∈ support right) := by
  apply relTriple_post_mono (relTriple_with_support hrel)
  intro leftResult rightResult hresult
  exact ⟨hresult.1.1, hresult.1.2.1, hresult.1.2.2.1,
    hresult.1.2.2.2, hresult.2.1, hresult.2.2⟩

def OutsideChainHashInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (input : HashInput) : Prop :=
  ∃ epoch candidate step,
    candidate ≠ chain ∧
      AtHashAddress parameter (.chain epoch candidate step) input

structure CoupledFixedChainMaterialInvariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest)) : Prop where
  tableEq : fixedChainMaterialTable selected left = right.2
  outsideEq : outsideChainSecret selected left.1.2 =
    outsideChainSecret selected right.1.1.2
  leftMatches : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter
        (unflattenSecret left.1.2)) selected
        (fixedChainMaterialTable selected left) ∧
    ChainTableEdgesMatch left.2.2.2 parameter selected
      (fixedChainMaterialTable selected left)
  rightMatches : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter
        (unflattenSecret right.1.1.2)) selected
        (fixedChainMaterialTable selected right.1) ∧
    ChainTableEdgesMatch right.1.2.2.2 parameter selected
      (fixedChainMaterialTable selected right.1)
  cachesAgree : HashCachesAgreeOn
    (OutsideChainHashInput parameter selected) left.2.2.2 right.1.2.2.2
  leftLeafFresh : ∀ epoch input,
    AtHashAddress parameter (.leaf epoch) input → left.2.2.2 input = none
  rightLeafFresh : ∀ epoch input,
    AtHashAddress parameter (.leaf epoch) input → right.1.2.2.2 input = none
  leftMerkleFresh : ∀ level node input,
    AtHashAddress parameter (.merkle level node) input →
      left.2.2.2 input = none
  rightMerkleFresh : ∀ level node input,
    AtHashAddress parameter (.merkle level node) input →
      right.1.2.2.2 input = none

theorem coupledFixedChainMaterialBaseRelation_to_invariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialBaseRelation
      parameter selected left right) :
    CoupledFixedChainMaterialInvariant parameter selected left right := by
  refine ⟨hrel.1, hrel.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fixedChainMaterialRepresentation_matches
      parameter selected left hrel.2.2.1
  · exact fixedChainMaterialRepresentation_matches
      parameter selected right.1 hrel.2.2.2
  · intro input hinput
    obtain ⟨epoch, candidate, step, hne, haddress⟩ := hinput
    rw [fixedChainMaterialRepresentation_cache_avoids_otherChain
        parameter selected candidate hne left hrel.2.2.1
          epoch step input haddress,
      fixedChainMaterialRepresentation_cache_avoids_otherChain
        parameter selected candidate hne right.1 hrel.2.2.2
          epoch step input haddress]
  · exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected left hrel.2.2.1
  · exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected right.1 hrel.2.2.2
  · intro level node input hinput
    exact fixedChainMaterialRepresentation_cache_avoids_merkle
      parameter selected left hrel.2.2.1 (.merkle level node)
        ⟨level, node, rfl⟩ input hinput
  · intro level node input hinput
    exact fixedChainMaterialRepresentation_cache_avoids_merkle
      parameter selected right.1 hrel.2.2.2 (.merkle level node)
        ⟨level, node, rfl⟩ input hinput

theorem relTriple_fixedChainMaterialRepresentation_withBase_invariant
    (parameter : PublicParameter) (selected : ChainIndex) :
    RelTriple
      (fixedChainMaterialRepresentation parameter selected)
      (fixedChainMaterialWithBase parameter selected)
      (CoupledFixedChainMaterialInvariant parameter selected) := by
  apply relTriple_post_mono
    (relTriple_fixedChainMaterialRepresentation_withBase parameter selected)
  exact coupledFixedChainMaterialBaseRelation_to_invariant parameter selected

theorem programmedFixedSeedChainTrajectories_support_as_actual
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) := by
  apply (mem_support_iff_of_evalDist_eq
    (evalDist_fixedSeedChainTrajectories_eq_programmed
      parameter secret chain (chainLength - 1) le_rfl allEpochs ∅
        allEpochs_nodup (by simp)) result).mpr
  exact hresult

theorem programmedFixedSeedChainTrajectories_table_eq
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    chainValueTableOfList result.1 =
      keygenChainValueTable result.2 (SecretKey.withoutPrecomputation parameter secret) chain := by
  exact Concrete.fixedSeedChainTrajectoriesFromCache_table_eq
    parameter secret chain result
      (programmedFixedSeedChainTrajectories_support_as_actual
        parameter secret chain result hresult)

theorem Concrete.fixedSeedChainTrajectoriesFromCache_avoids_otherChain
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain candidate : ChainIndex) (hne : candidate ≠ chain)
    (targetEpoch : Epoch) (targetStep : ChainStep) (input : HashInput)
    (hinput : AtHashAddress parameter
      (.chain targetEpoch candidate targetStep) input) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 input = none := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons epoch epochs ih =>
      intro cache result hcache hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) input cache first.2 first.1
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter
              (.chain targetEpoch candidate targetStep))
          · intro queried heq
            subst queried
            exact hinput
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hvalid heq
            simp only [HashDomain.chain.injEq] at heq
            exact hne heq.2.1.symm
        · exact hcache
        · exact hfirst
      · exact hrest

theorem programmedFixedSeedChainTrajectories_avoids_otherChain
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain candidate : ChainIndex) (hne : candidate ≠ chain)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (targetEpoch : Epoch) (targetStep : ChainStep) (input : HashInput)
    (hinput : AtHashAddress parameter
      (.chain targetEpoch candidate targetStep) input) :
    result.2 input = none := by
  exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_otherChain
    parameter secret chain candidate hne targetEpoch targetStep input hinput
      allEpochs ∅ result (by simp)
      (programmedFixedSeedChainTrajectories_support_as_actual
        parameter secret chain result hresult)

theorem Concrete.fixedSeedChainTrajectoriesFromCache_component_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (target : Epoch),
      target ∈ epochs →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      ∃ before after trajectory,
        (trajectory, after) ∈ support
          ((simulateQ randomOracle
            (Concrete.chainTrajectory parameter target chain 0 steps
              (secret target chain))).run before) ∧
        after ≤ result.2 := by
  intro epochs
  induction epochs with
  | nil =>
      intro _cache _result target hmem _hresult
      simp at hmem
  | cons epoch epochs ih =>
      intro cache result target hmem hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · have hrestInfo :=
          Concrete.fixedSeedChainTrajectoriesFromCache_support_info
            parameter secret chain steps epochs first.2 rest hrest
        exact ⟨cache, first.2, first.1, hfirst, hrestInfo.1⟩
      · exact ih first.2 rest target htail hrest

theorem Concrete.fixedSeedChainTrajectoriesFromCache_edgesMatch
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    ChainTableEdgesMatch result.2 parameter chain
      (chainValueTableOfList result.1) := by
  rw [Concrete.fixedSeedChainTrajectoriesFromCache_table_eq
    parameter secret chain result hresult]
  rintro ⟨epoch, step⟩
  obtain ⟨before, after, trajectory, htrajectory, hafter⟩ :=
    Concrete.fixedSeedChainTrajectoriesFromCache_component_support
      parameter secret chain (chainLength - 1) allEpochs ∅ result epoch
        (mem_allEpochs epoch) hresult
  have hmapped : (trajectory.back, after) ∈ support
      ((fun value : FullChainTrajectory × QueryCache HashSpec =>
        (value.1.back, value.2)) <$>
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter epoch chain 0
              (chainLength - 1) (secret epoch chain))).run before) := by
    rw [support_map]
    exact ⟨(trajectory, after), htrajectory, rfl⟩
  have hwalk : (trajectory.back, after) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
          (secret epoch chain) : OracleComp HashSpec Digest)).run before) :=
    (mem_support_iff_of_evalDist_eq
      (evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache
        parameter epoch chain 0 (chainLength - 1)
          (secret epoch chain) before) (trajectory.back, after)).mp hmapped
  obtain ⟨output, hcached⟩ :=
    Concrete.CacheReplay.chainWalk_query_cached_in_largerCache
      parameter epoch chain 0 (chainLength - 1) (secret epoch chain)
        step.val step.isLt (by simp)
        before after result.2 trajectory.back
        hwalk hafter
  have hstepIndex :
      (⟨0 + step.val, by omega⟩ : ChainStep) = step := by
    apply Fin.ext
    simp
  rw [hstepIndex] at hcached
  refine ⟨output, ?_, ?_⟩
  · simpa [chainTableEdgeInput, keygenChainValueTable,
      chainStepDigit, SecretKey.withoutPrecomputation] using hcached
  · let stepFunction :=
      Concrete.CacheView.chainStep result.2 parameter epoch chain
    calc
      truncateHash output = Concrete.CacheView.digestAt result.2
          (Concrete.CacheView.chainInput parameter epoch chain step
            (Wots.walk stepFunction 0 step.val (secret epoch chain))) :=
        (Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached).symm
      _ = stepFunction step.val
          (Wots.walk stepFunction 0 step.val (secret epoch chain)) := by
        symm
        exact Concrete.CacheView.chainStep_eq result.2 parameter epoch chain
          step.val _ step.isLt
      _ = chainTableEdgeTarget
          (keygenChainValueTable result.2 (SecretKey.withoutPrecomputation parameter secret) chain)
          (epoch, step) := by
        change stepFunction step.val
            (Wots.walk stepFunction 0 step.val (secret epoch chain)) =
          Wots.signChain stepFunction (chainStepNextDigit step)
            (secret epoch chain)
        unfold Wots.signChain
        rw [show (chainStepNextDigit step).val = step.val + 1 by
          simp [chainStepNextDigit]]
        simp only [Wots.walk, zero_add]

theorem programmedFixedSeedChainTrajectories_edgesMatch
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    ChainTableEdgesMatch result.2 parameter chain
      (chainValueTableOfList result.1) := by
  exact Concrete.fixedSeedChainTrajectoriesFromCache_edgesMatch
    parameter secret chain result
      (programmedFixedSeedChainTrajectories_support_as_actual
        parameter secret chain result hresult)

noncomputable def warmedMaterialAsFixed
    (_chain : ChainIndex) (material : WarmedTrajectoryMaterial) :
    FixedChainMaterial :=
  let table := chainValueTableOfList material.2.1
  (material.1,
    (allChainEdges.map (chainTableEdgeTarget table), ([], material.2.2)))

theorem fixedChainMaterialTable_warmedMaterialAsFixed
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : WarmedTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain)) :
    fixedChainMaterialTable chain (warmedMaterialAsFixed chain material) =
      chainValueTableOfList material.2.1 := by
  let table := chainValueTableOfList material.2.1
  have htrajectory := programmedWarmedTrajectoryMaterial_support_trajectory
    parameter chain material hmaterial
  have htable := programmedFixedSeedChainTrajectories_table_eq
    parameter (unflattenSecret material.1.2) chain material.2 htrajectory
  have hseeds : (fun epoch => material.1.2 (epoch, chain)) =
      chainTableSeedTargets table := by
    funext epoch
    have hmatch := keygenChainValueTable_seedsMatch material.2.2
      (SecretKey.withoutPrecomputation parameter
        (unflattenSecret material.1.2)) chain epoch
    rw [← htable] at hmatch
    simpa [table, ChainTableSeedsMatch, unflattenSecret,
      chainTableSeedTargets, SecretKey.withoutPrecomputation] using hmatch
  unfold warmedMaterialAsFixed fixedChainMaterialTable
  dsimp only
  rw [chainEdgeTableOfTape_map, hseeds]
  exact chainTableMaterialEquiv.symm_apply_apply table

theorem warmedMaterialAsFixed_invariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftMaterial : WarmedTrajectoryMaterial)
    (rightMaterial : FixedChainMaterial)
    (base : ChainValueIndex → Digest)
    (hleft : leftMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter selected))
    (hright : rightMaterial ∈ support
      (fixedChainMaterialRepresentation parameter selected))
    (htable : chainValueTableOfList leftMaterial.2.1 = base)
    (houtside : outsideChainSecret selected leftMaterial.1.2 =
      outsideChainSecret selected rightMaterial.1.2) :
    CoupledFixedChainMaterialInvariant parameter selected
      (warmedMaterialAsFixed selected leftMaterial) (rightMaterial, base) := by
  have htrajectory := programmedWarmedTrajectoryMaterial_support_trajectory
    parameter selected leftMaterial hleft
  have hactual := programmedFixedSeedChainTrajectories_support_as_actual
    parameter (unflattenSecret leftMaterial.1.2) selected leftMaterial.2
      htrajectory
  have htableFixed := fixedChainMaterialTable_warmedMaterialAsFixed
    parameter selected leftMaterial hleft
  have hrightMatches := fixedChainMaterialRepresentation_matches
    parameter selected rightMaterial hright
  refine ⟨htableFixed.trans htable, houtside,
    ?_, hrightMatches, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htableFixed]
    constructor
    · rw [programmedFixedSeedChainTrajectories_table_eq
          parameter (unflattenSecret leftMaterial.1.2) selected
            leftMaterial.2 htrajectory]
      exact keygenChainValueTable_seedsMatch leftMaterial.2.2
        (SecretKey.withoutPrecomputation parameter
          (unflattenSecret leftMaterial.1.2)) selected
    · exact programmedFixedSeedChainTrajectories_edgesMatch
        parameter (unflattenSecret leftMaterial.1.2) selected
          leftMaterial.2 htrajectory
  · intro input hinput
    obtain ⟨epoch, candidate, step, hne, haddress⟩ := hinput
    change leftMaterial.2.2 input = rightMaterial.2.2.2 input
    rw [programmedFixedSeedChainTrajectories_avoids_otherChain
      parameter (unflattenSecret leftMaterial.1.2) selected candidate hne
        leftMaterial.2 htrajectory epoch step input haddress,
      fixedChainMaterialRepresentation_cache_avoids_otherChain
        parameter selected candidate hne rightMaterial hright
          epoch step input haddress]
  · intro epoch input hinput
    change leftMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_leaf
      parameter (unflattenSecret leftMaterial.1.2) selected
        leftMaterial.2 htrajectory epoch input hinput
  · exact fixedChainMaterialRepresentation_cache_avoids_leaf
      parameter selected rightMaterial hright
  · intro level node input hinput
    change leftMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter (unflattenSecret leftMaterial.1.2) selected
        leftMaterial.2 htrajectory level node input hinput
  · intro level node input hinput
    exact fixedChainMaterialRepresentation_cache_avoids_merkle
      parameter selected rightMaterial hright (.merkle level node)
        ⟨level, node, rfl⟩ input hinput

theorem warmedMaterialsAsFixed_invariant
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftMaterial rightMaterial : WarmedTrajectoryMaterial)
    (base : ChainValueIndex → Digest)
    (hleft : leftMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter selected))
    (hright : rightMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter selected))
    (htable : chainValueTableOfList leftMaterial.2.1 = base)
    (houtside : outsideChainSecret selected leftMaterial.1.2 =
      outsideChainSecret selected rightMaterial.1.2) :
    CoupledFixedChainMaterialInvariant parameter selected
      (warmedMaterialAsFixed selected leftMaterial)
      (warmedMaterialAsFixed selected rightMaterial, base) := by
  have hleftTrajectory :=
    programmedWarmedTrajectoryMaterial_support_trajectory
      parameter selected leftMaterial hleft
  have hrightTrajectory :=
    programmedWarmedTrajectoryMaterial_support_trajectory
      parameter selected rightMaterial hright
  have hleftTable := fixedChainMaterialTable_warmedMaterialAsFixed
    parameter selected leftMaterial hleft
  have hrightTable := fixedChainMaterialTable_warmedMaterialAsFixed
    parameter selected rightMaterial hright
  refine ⟨hleftTable.trans htable, houtside, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hleftTable]
    constructor
    · rw [programmedFixedSeedChainTrajectories_table_eq
          parameter (unflattenSecret leftMaterial.1.2) selected
            leftMaterial.2 hleftTrajectory]
      exact keygenChainValueTable_seedsMatch leftMaterial.2.2
        (SecretKey.withoutPrecomputation parameter
          (unflattenSecret leftMaterial.1.2)) selected
    · exact programmedFixedSeedChainTrajectories_edgesMatch
        parameter (unflattenSecret leftMaterial.1.2) selected
          leftMaterial.2 hleftTrajectory
  · rw [hrightTable]
    constructor
    · rw [programmedFixedSeedChainTrajectories_table_eq
          parameter (unflattenSecret rightMaterial.1.2) selected
            rightMaterial.2 hrightTrajectory]
      exact keygenChainValueTable_seedsMatch rightMaterial.2.2
        (SecretKey.withoutPrecomputation parameter
          (unflattenSecret rightMaterial.1.2)) selected
    · exact programmedFixedSeedChainTrajectories_edgesMatch
        parameter (unflattenSecret rightMaterial.1.2) selected
          rightMaterial.2 hrightTrajectory
  · intro input hinput
    obtain ⟨epoch, candidate, step, hne, haddress⟩ := hinput
    change leftMaterial.2.2 input = rightMaterial.2.2 input
    rw [programmedFixedSeedChainTrajectories_avoids_otherChain
      parameter (unflattenSecret leftMaterial.1.2) selected candidate hne
        leftMaterial.2 hleftTrajectory epoch step input haddress,
      programmedFixedSeedChainTrajectories_avoids_otherChain
        parameter (unflattenSecret rightMaterial.1.2) selected candidate hne
          rightMaterial.2 hrightTrajectory epoch step input haddress]
  · intro epoch input hinput
    change leftMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_leaf
      parameter (unflattenSecret leftMaterial.1.2) selected
        leftMaterial.2 hleftTrajectory epoch input hinput
  · intro epoch input hinput
    change rightMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_leaf
      parameter (unflattenSecret rightMaterial.1.2) selected
        rightMaterial.2 hrightTrajectory epoch input hinput
  · intro level node input hinput
    change leftMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter (unflattenSecret leftMaterial.1.2) selected
        leftMaterial.2 hleftTrajectory level node input hinput
  · intro level node input hinput
    change rightMaterial.2.2 input = none
    exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter (unflattenSecret rightMaterial.1.2) selected
        rightMaterial.2 hrightTrajectory level node input hinput

theorem CoupledFixedChainMaterialInvariant.outsideChainCachesAgree
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant
      parameter chain left right) :
    HashCachesAgreeOn (OutsideChainHashInput parameter chain)
      left.2.2.2 right.1.2.2.2 := by
  exact hrel.cachesAgree

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

theorem outsideChainHashInput_ne_merkleInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (input : HashInput)
    (hinput : OutsideChainHashInput parameter chain input) :
    input ≠ Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  obtain ⟨epoch, candidate, step, _hne, hchain⟩ := hinput
  have hmerkle : AtHashAddress parameter (.merkle level node) input := by
    rw [heq]
    simp [Concrete.CacheView.merkleInput]
  have hdomain := atHashAddress_unique parameter
    (.chain epoch candidate step) (.merkle level node) input hchain hmerkle
  simp at hdomain

theorem relTriple_nodeHash_run_of_both_none
    (parameter : PublicParameter) (chain : ChainIndex)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest)
    (left right : QueryCache HashSpec)
    (hleftNone : left (Concrete.CacheView.merkleInput
      parameter level node leftChild rightChild) = none)
    (hrightNone : right (Concrete.CacheView.merkleInput
      parameter level node leftChild rightChild) = none)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter chain) left right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run left)
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter chain)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  let input := Concrete.CacheView.merkleInput
    parameter level node leftChild rightChild
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run left)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run right) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_run_of_both_none
      (OutsideChainHashInput parameter chain) left right input input
      hleftNone hrightNone hagrees
      (outsideChainHashInput_ne_merkleInput
        parameter chain level node leftChild rightChild)
      (outsideChainHashInput_ne_merkleInput
        parameter chain level node leftChild rightChild))
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1,
    hresult.2.1, hresult.2.2.1, hresult.2.2.2⟩

theorem relTriple_treeNode_succ_run_of_cached_children
    (parameter : PublicParameter) (chain : ChainIndex)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (leftChild rightChild : Digest)
    (left right : QueryCache HashSpec)
    (hleftLeft :
      (simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret levels
          (Concrete.childNode node false) : OracleComp HashSpec Digest)).run left =
        pure (leftChild, left))
    (hleftRight :
      (simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret levels
          (Concrete.childNode node false) : OracleComp HashSpec Digest)).run right =
        pure (leftChild, right))
    (hrightLeft :
      (simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret levels
          (Concrete.childNode node true) : OracleComp HashSpec Digest)).run left =
        pure (rightChild, left))
    (hrightRight :
      (simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret levels
          (Concrete.childNode node true) : OracleComp HashSpec Digest)).run right =
        pure (rightChild, right))
    (hleftNone : left (Concrete.CacheView.merkleInput parameter
      ⟨levels, hlevel⟩ node leftChild rightChild) = none)
    (hrightNone : right (Concrete.CacheView.merkleInput parameter
      ⟨levels, hlevel⟩ node leftChild rightChild) = none)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter chain) left right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run left)
      ((simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter chain)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  simp only [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftLeft, hleftRight, hrightLeft, hrightRight, pure_bind,
    hlevel, ↓reduceDIte]
  exact relTriple_nodeHash_run_of_both_none parameter chain
    ⟨levels, hlevel⟩ node leftChild rightChild left right
    hleftNone hrightNone hagrees

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
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable)
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
    have hleftRun := simulate_chainWalk_run_eq_pure_of_table_matches left
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable
        hleftSeeds (hleftEdges.mono hleftLe) epoch (chainLength - 1) hsteps
    have hrightRun := simulate_chainWalk_run_eq_pure_of_table_matches right
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable
        hrightSeeds (hrightEdges.mono hrightLe) epoch (chainLength - 1) hsteps
    simp only [SecretKey.withoutPrecomputation] at hleftRun hrightRun
    rw [hleftRun, hrightRun]
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
      (SecretKey.withoutPrecomputation parameter leftSecret) selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter rightSecret) selected rightTable)
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
    (hrel : CoupledFixedChainMaterialInvariant
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
  have hleftMatches := hrel.leftMatches
  have hrightMatches := hrel.rightMatches
  have houtside : secretOutsideChain selected (unflattenSecret left.1.2) =
      secretOutsideChain selected (unflattenSecret right.1.1.2) :=
    secretOutsideChain_eq_of_outsideChainSecret_eq selected
      left.1.2 right.1.1.2 hrel.outsideEq
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
    (hrel : CoupledFixedChainMaterialInvariant
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
    (hrel : CoupledFixedChainMaterialInvariant
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
    (hrel : CoupledFixedChainMaterialInvariant
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
    exact hrel.leftLeafFresh epoch input hinput
  · intro input hinput
    exact hrel.rightLeafFresh epoch input hinput

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_leafTreeValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
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
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
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
    exact hrel.leftLeafFresh index.node input hinput
  have hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) right.1.2.2.2 := by
    intro index hindex input hinput
    have hheight := hzero index hindex
    unfold TreeValueIndex.domain at hinput
    rw [dif_pos hheight] at hinput
    exact hrel.rightLeafFresh index.node input hinput
  exact relTriple_fixedChainMaterial_leafTreeValues_run
    parameter selected left right hrel (treeValueIndicesAtHeight 0)
    hzero hordered left.2.2.2 right.1.2.2.2 hleftFresh hrightFresh
    (hrel.outsideChainCachesAgree parameter selected left right) le_rfl le_rfl

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_merkleTreeValue_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (processed : List TreeValueIndex)
    (leftPrefix rightPrefix : List Digest × QueryCache HashSpec)
    (hleftPrefix : leftPrefix ∈ support
      (treeValues parameter (unflattenSecret left.1.2)
        processed left.2.2.2))
    (hrightPrefix : rightPrefix ∈ support
      (treeValues parameter (unflattenSecret right.1.1.2)
        processed right.1.2.2.2))
    (hprefixValues : leftPrefix.1 = rightPrefix.1)
    (current : TreeValueIndex) (hpositive : 0 < current.1.val)
    (hleftChild : TreeValueIndex.ofSubtree (current.1.val - 1)
      (Concrete.childNode current.node false) (by omega)
      (childNode_subtreeValid (current.1.val - 1) current.node false
        (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
        processed)
    (hrightChild : TreeValueIndex.ofSubtree (current.1.val - 1)
      (Concrete.childNode current.node true) (by omega)
      (childNode_subtreeValid (current.1.val - 1) current.node true
        (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
        processed)
    (hleftFresh : ∀ input,
      AtHashAddress parameter current.domain input →
        leftPrefix.2 input = none)
    (hrightFresh : ∀ input,
      AtHashAddress parameter current.domain input →
        rightPrefix.2 input = none)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) leftPrefix.2 rightPrefix.2) :
    RelTriple
      ((simulateQ randomOracle
        (current.computation parameter (unflattenSecret left.1.2))).run
          leftPrefix.2)
      ((simulateQ randomOracle
        (current.computation parameter (unflattenSecret right.1.1.2))).run
          rightPrefix.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2) := by
  let levels := current.1.val - 1
  have hsucc : current.1.val = levels + 1 := by
    dsimp [levels]
    omega
  have hlevel : levels < treeHeight := by
    dsimp [levels]
    omega
  have hparentValid : TreeSubtreeValid (levels + 1) current.node := by
    simpa [← hsucc] using current.subtreeValid
  let leftIndex := TreeValueIndex.ofSubtree levels
    (Concrete.childNode current.node false) (by omega)
      (childNode_subtreeValid levels current.node false hparentValid)
  let rightIndex := TreeValueIndex.ofSubtree levels
    (Concrete.childNode current.node true) (by omega)
      (childNode_subtreeValid levels current.node true hparentValid)
  have hleftIndex : leftIndex ∈ processed := by
    simpa [leftIndex, levels] using hleftChild
  have hrightIndex : rightIndex ∈ processed := by
    simpa [rightIndex, levels] using hrightChild
  have hleftReplay := treeValues_support_replay parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix hleftPrefix
  have hrightReplay := treeValues_support_replay parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix hrightPrefix
  have hleftChildEq := treeValuesReplay_eq_at_mem parameter parameter
    (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
    leftPrefix.2 rightPrefix.2 processed leftPrefix.1
    hleftReplay (hprefixValues ▸ hrightReplay) leftIndex hleftIndex
  have hrightChildEq := treeValuesReplay_eq_at_mem parameter parameter
    (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
    leftPrefix.2 rightPrefix.2 processed leftPrefix.1
    hleftReplay (hprefixValues ▸ hrightReplay) rightIndex hrightIndex
  let leftChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter
    (unflattenSecret left.1.2) levels (Concrete.childNode current.node false)
  let rightChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter
    (unflattenSecret left.1.2) levels (Concrete.childNode current.node true)
  have hleftLeft := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix
      hleftPrefix leftIndex hleftIndex
  have hleftRight := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix
      hrightPrefix leftIndex hleftIndex
  have hrightLeft := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix
      hleftPrefix rightIndex hrightIndex
  have hrightRight := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix
      hrightPrefix rightIndex hrightIndex
  have hleftChildEq' : leftChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false) := by
    simpa [leftIndex, leftChild] using hleftChildEq
  have hrightChildEq' : rightChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true) := by
    simpa [rightIndex, rightChild] using hrightChildEq
  have hleftLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (leftChild, leftPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node false))).run leftPrefix.2 = _
      at hleftLeft
    exact hleftLeft
  have hleftRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (leftChild, rightPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false), rightPrefix.2) at hleftRight
    rw [hleftChildEq']
    exact hleftRight
  have hrightLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (rightChild, leftPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node true))).run leftPrefix.2 = _
      at hrightLeft
    exact hrightLeft
  have hrightRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (rightChild, rightPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true), rightPrefix.2) at hrightRight
    rw [hrightChildEq']
    exact hrightRight
  have hdomain : current.domain = .merkle ⟨levels, hlevel⟩ current.node := by
    unfold TreeValueIndex.domain
    rw [dif_neg (by omega)]
  have hleftNone : leftPrefix.2 (Concrete.CacheView.merkleInput parameter
      ⟨levels, hlevel⟩ current.node leftChild rightChild) = none := by
    apply hleftFresh
    rw [hdomain]
    simp [Concrete.CacheView.merkleInput]
  have hrightNone : rightPrefix.2 (Concrete.CacheView.merkleInput parameter
      ⟨levels, hlevel⟩ current.node leftChild rightChild) = none := by
    apply hrightFresh
    rw [hdomain]
    simp [Concrete.CacheView.merkleInput]
  change RelTriple
    ((simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret left.1.2)
        current.1.val current.node)).run leftPrefix.2)
    ((simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret right.1.1.2)
        current.1.val current.node)).run rightPrefix.2) _
  rw [hsucc]
  apply relTriple_post_mono
    (relTriple_treeNode_succ_run_of_cached_children parameter selected
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      levels current.node hlevel leftChild rightChild
      leftPrefix.2 rightPrefix.2 hleftLeft' hleftRight'
      hrightLeft' hrightRight' hleftNone hrightNone hagrees)
  intro leftResult rightResult hresult
  have hleftLe := treeValues_cache_le parameter (unflattenSecret left.1.2)
    processed left.2.2.2 leftPrefix hleftPrefix
  have hrightLe := treeValues_cache_le parameter (unflattenSecret right.1.1.2)
    processed right.1.2.2.2 rightPrefix hrightPrefix
  simpa [TreeValueIndex.computation, hsucc] using
    ⟨hresult.1, hresult.2.1,
      hleftLe.trans hresult.2.2.1,
      hrightLe.trans hresult.2.2.2⟩

theorem treeValues_append
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (left right : List TreeValueIndex) (cache : QueryCache HashSpec),
      treeValues parameter secret (left ++ right) cache = (do
        let leftResult ← treeValues parameter secret left cache
        let rightResult ← treeValues parameter secret right leftResult.2
        pure (leftResult.1 ++ rightResult.1, rightResult.2)) := by
  intro left
  induction left with
  | nil =>
      intro right cache
      simp
  | cons current left ih =>
      intro right cache
      rw [List.cons_append, treeValues_cons, treeValues_cons]
      simp [ih, bind_assoc]

theorem treeValues_append_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (left right : List TreeValueIndex) (cache : QueryCache HashSpec)
    (leftResult rightResult : List Digest × QueryCache HashSpec)
    (hleft : leftResult ∈ support
      (treeValues parameter secret left cache))
    (hright : rightResult ∈ support
      (treeValues parameter secret right leftResult.2)) :
    (leftResult.1 ++ rightResult.1, rightResult.2) ∈ support
      (treeValues parameter secret (left ++ right) cache) := by
  rw [treeValues_append, mem_support_bind_iff]
  refine ⟨leftResult, hleft, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨rightResult, hright, by simp⟩

theorem treeValues_singleton_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (index : TreeValueIndex) (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (index.computation parameter secret)).run cache)) :
    ([result.1], result.2) ∈ support
      (treeValues parameter secret [index] cache) := by
  rw [treeValues_cons, mem_support_bind_iff]
  refine ⟨result, hresult, ?_⟩
  simp

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_merkleTreeValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest)) :
    ∀ (indices base : List TreeValueIndex)
      (leftBase rightBase : List Digest × QueryCache HashSpec),
      (∀ current ∈ indices, ∃ hpositive : 0 < current.1.val,
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node false) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node false
            (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
            base ∧
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node true) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node true
            (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
            base) →
      indices.Pairwise TreeValueIndex.Precedes →
      leftBase ∈ support
        (treeValues parameter (unflattenSecret left.1.2) base left.2.2.2) →
      rightBase ∈ support
        (treeValues parameter (unflattenSecret right.1.1.2)
          base right.1.2.2.2) →
      leftBase.1 = rightBase.1 →
      TreeValuesFresh parameter indices leftBase.2 →
      TreeValuesFresh parameter indices rightBase.2 →
      HashCachesAgreeOn (OutsideChainHashInput parameter selected)
        leftBase.2 rightBase.2 →
      RelTriple
        (treeValues parameter (unflattenSecret left.1.2) indices leftBase.2)
        (treeValues parameter (unflattenSecret right.1.1.2) indices rightBase.2)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            HashCachesAgreeOn (OutsideChainHashInput parameter selected)
              leftResult.2 rightResult.2 ∧
            left.2.2.2 ≤ leftResult.2 ∧
            right.1.2.2.2 ≤ rightResult.2 ∧
            (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
              (treeValues parameter (unflattenSecret left.1.2)
                (base ++ indices) left.2.2.2) ∧
            (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
              (treeValues parameter (unflattenSecret right.1.1.2)
                (base ++ indices) right.1.2.2.2)) := by
  intro indices
  induction indices with
  | nil =>
      intro base leftBase rightBase _hchildren _hordered hleftBase hrightBase
        hbaseValues _hleftFresh _hrightFresh hagrees
      simp only [treeValues_nil]
      apply relTriple_pure_pure
      refine ⟨rfl, hagrees,
        treeValues_cache_le parameter (unflattenSecret left.1.2)
          base left.2.2.2 leftBase hleftBase,
        treeValues_cache_le parameter (unflattenSecret right.1.1.2)
          base right.1.2.2.2 rightBase hrightBase,
        ?_, ?_⟩
      · simpa using hleftBase
      · simpa using hrightBase
  | cons current indices ih =>
      intro base leftBase rightBase hchildren hordered hleftBase hrightBase
        hbaseValues hleftFresh hrightFresh hagrees
      obtain ⟨hpositive, hleftChild, hrightChild⟩ :=
        hchildren current (by simp)
      have htailChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node false) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node false
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ∧
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node true) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node true
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base := by
        intro target htarget
        exact hchildren target (by simp [htarget])
      have hcurrentBefore : ∀ target ∈ indices,
          current.Precedes target := (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hleftCurrentFresh : ∀ input,
          AtHashAddress parameter current.domain input →
            leftBase.2 input = none := by
        intro input hinput
        exact hleftFresh current (by simp) input hinput
      have hrightCurrentFresh : ∀ input,
          AtHashAddress parameter current.domain input →
            rightBase.2 input = none := by
        intro input hinput
        exact hrightFresh current (by simp) input hinput
      have hhead := relTriple_fixedChainMaterial_merkleTreeValue_run
        parameter selected left right base leftBase rightBase
        hleftBase hrightBase hbaseValues current hpositive
        hleftChild hrightChild hleftCurrentFresh hrightCurrentFresh hagrees
      let LeftProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (leftBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              (base ++ [current]) left.2.2.2)
      let RightProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (rightBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              (base ++ [current]) right.1.2.2.2)
      have hleftProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret left.1.2))).run
              leftBase.2), LeftProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter
            (unflattenSecret left.1.2) current indices hcurrentBefore
            leftBase.2 hleftFresh result hresult,
          treeValues_append_support parameter (unflattenSecret left.1.2)
            base [current] left.2.2.2 leftBase ([result.1], result.2)
            hleftBase (treeValues_singleton_support parameter
              (unflattenSecret left.1.2) current leftBase.2 result hresult)⟩
      have hrightProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret right.1.1.2))).run
              rightBase.2), RightProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter
            (unflattenSecret right.1.1.2) current indices hcurrentBefore
            rightBase.2 hrightFresh result hresult,
          treeValues_append_support parameter (unflattenSecret right.1.1.2)
            base [current] right.1.2.2.2 rightBase ([result.1], result.2)
            hrightBase (treeValues_singleton_support parameter
              (unflattenSecret right.1.1.2) current rightBase.2 result hresult)⟩
      have hheadExtended := relTriple_strengthen_support
        (leftProperty := LeftProperty) (rightProperty := RightProperty)
        hhead hleftProperty hrightProperty
      simp only [treeValues_cons]
      apply relTriple_bind hheadExtended
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftProperties, hrightProperties⟩ := hheadResult
      obtain ⟨leftHead, leftHeadCache⟩ := leftHeadResult
      obtain ⟨rightHead, rightHeadCache⟩ := rightHeadResult
      dsimp only at hheadRelation hleftProperties hrightProperties ⊢
      let nextLeftBase : List Digest × QueryCache HashSpec :=
        (leftBase.1 ++ [leftHead], leftHeadCache)
      let nextRightBase : List Digest × QueryCache HashSpec :=
        (rightBase.1 ++ [rightHead], rightHeadCache)
      have hnextValues : nextLeftBase.1 = nextRightBase.1 := by
        simp [nextLeftBase, nextRightBase, hbaseValues, hheadRelation.1]
      have hnextChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node false) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node false
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ++ [current] ∧
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node true) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node true
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ++ [current] := by
        intro target htarget
        obtain ⟨hpos, hleft, hright⟩ := htailChildren target htarget
        exact ⟨hpos, List.mem_append_left [current] hleft,
          List.mem_append_left [current] hright⟩
      apply relTriple_bind
        (ih (base ++ [current]) nextLeftBase nextRightBase
          hnextChildren htailOrdered hleftProperties.2 hrightProperties.2
          hnextValues hleftProperties.1 hrightProperties.1
          hheadRelation.2.1)
      intro leftTailResult rightTailResult htailResult
      obtain ⟨leftTail, leftTailCache⟩ := leftTailResult
      obtain ⟨rightTail, rightTailCache⟩ := rightTailResult
      dsimp only at htailResult ⊢
      apply relTriple_pure_pure
      refine ⟨congrArg₂ List.cons hheadRelation.1 htailResult.1,
        htailResult.2.1, htailResult.2.2.1,
        htailResult.2.2.2.1, ?_, ?_⟩
      · simpa [nextLeftBase, List.append_assoc] using
          htailResult.2.2.2.2.1
      · simpa [nextRightBase, List.append_assoc] using
          htailResult.2.2.2.2.2

def treeValueIndicesBelow : Nat → List TreeValueIndex
  | 0 => []
  | height + 1 =>
      treeValueIndicesBelow height ++
        if hheight : height < treeHeight + 1 then
          treeValueIndicesAtHeight ⟨height, hheight⟩
        else []

theorem treeValueIndicesBelow_succ (height : Nat)
    (hheight : height < treeHeight + 1) :
    treeValueIndicesBelow (height + 1) =
      treeValueIndicesBelow height ++
        treeValueIndicesAtHeight ⟨height, hheight⟩ := by
  rw [treeValueIndicesBelow, dif_pos hheight]

theorem mem_treeValueIndicesAtHeight_iff
    (height : Fin (treeHeight + 1)) (index : TreeValueIndex) :
    index ∈ treeValueIndicesAtHeight height ↔ index.1 = height := by
  constructor
  · intro hindex
    rw [treeValueIndicesAtHeight, List.mem_ofFn] at hindex
    obtain ⟨node, rfl⟩ := hindex
    rfl
  · intro hheight
    cases index with
    | mk indexHeight node =>
        dsimp only at hheight
        subst indexHeight
        rw [treeValueIndicesAtHeight, List.mem_ofFn]
        exact ⟨node, rfl⟩

theorem childTreeValueIndex_mem_below
    (current : TreeValueIndex) (hpositive : 0 < current.1.val)
    (right : Bool) :
    TreeValueIndex.ofSubtree (current.1.val - 1)
      (Concrete.childNode current.node right) (by omega)
      (childNode_subtreeValid (current.1.val - 1) current.node right
        (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
      treeValueIndicesBelow current.1.val := by
  let child := TreeValueIndex.ofSubtree (current.1.val - 1)
    (Concrete.childNode current.node right) (by omega)
    (childNode_subtreeValid (current.1.val - 1) current.node right
      (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid))
  have hbound : current.1.val - 1 < treeHeight + 1 := by omega
  have hdecompose : current.1.val = (current.1.val - 1) + 1 := by omega
  have hbelow := congrArg treeValueIndicesBelow hdecompose
  rw [treeValueIndicesBelow_succ _ hbound] at hbelow
  rw [hbelow, List.mem_append]
  right
  apply (mem_treeValueIndicesAtHeight_iff
    ⟨current.1.val - 1, hbound⟩ child).2
  apply Fin.ext
  simp [child]

theorem relTriple_fixedChainMaterial_merkleHeight_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (height : Fin (treeHeight + 1)) (hpositive : 0 < height.val)
    (leftBase rightBase : List Digest × QueryCache HashSpec)
    (hleftBase : leftBase ∈ support
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow height.val) left.2.2.2))
    (hrightBase : rightBase ∈ support
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow height.val) right.1.2.2.2))
    (hbaseValues : leftBase.1 = rightBase.1)
    (hleftFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) leftBase.2)
    (hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) rightBase.2)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) leftBase.2 rightBase.2) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesAtHeight height) leftBase.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesAtHeight height) rightBase.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2 ∧
          (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              (treeValueIndicesBelow (height.val + 1)) left.2.2.2) ∧
          (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              (treeValueIndicesBelow (height.val + 1)) right.1.2.2.2)) := by
  have hchildren : ∀ current ∈ treeValueIndicesAtHeight height,
      ∃ hcurrentPositive : 0 < current.1.val,
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node false) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node false
            (by simpa [Nat.sub_add_cancel hcurrentPositive] using
              current.subtreeValid)) ∈ treeValueIndicesBelow height.val ∧
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node true) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node true
            (by simpa [Nat.sub_add_cancel hcurrentPositive] using
              current.subtreeValid)) ∈ treeValueIndicesBelow height.val := by
    intro current hcurrent
    have hheight := (mem_treeValueIndicesAtHeight_iff height current).1 hcurrent
    have hvalue : current.1.val = height.val := congrArg Fin.val hheight
    have hcurrentPositive : 0 < current.1.val := by omega
    refine ⟨hcurrentPositive, ?_, ?_⟩
    · simpa only [hvalue] using
        (childTreeValueIndex_mem_below current hcurrentPositive false)
    · simpa only [hvalue] using
        (childTreeValueIndex_mem_below current hcurrentPositive true)
  have hordered : (treeValueIndicesAtHeight height).Pairwise
      TreeValueIndex.Precedes := by
    simp only [treeValueIndicesAtHeight, List.pairwise_ofFn]
    intro leftNode rightNode hlt
    exact Or.inr ⟨rfl, hlt⟩
  have hcoupling := relTriple_fixedChainMaterial_merkleTreeValues_run
    parameter selected left right (treeValueIndicesAtHeight height)
    (treeValueIndicesBelow height.val) leftBase rightBase
    hchildren hordered hleftBase hrightBase hbaseValues
    hleftFresh hrightFresh hagrees
  apply relTriple_post_mono hcoupling
  intro leftResult rightResult hresult
  have hbelow := treeValueIndicesBelow_succ height.val height.isLt
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.1,
    hresult.2.2.2.1,
    hbelow ▸ hresult.2.2.2.2.1,
    hbelow ▸ hresult.2.2.2.2.2⟩

theorem treeValues_preserves_fresh_after
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (processed future : List TreeValueIndex),
      (∀ current ∈ processed, ∀ target ∈ future,
        current.Precedes target) →
      ∀ (cache : QueryCache HashSpec),
        TreeValuesFresh parameter future cache →
        ∀ result ∈ support
          (treeValues parameter secret processed cache),
          TreeValuesFresh parameter future result.2 := by
  intro processed
  induction processed with
  | nil =>
      intro future _hbefore cache hfresh result hresult
      simp only [treeValues_nil, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hfresh
  | cons current processed ih =>
      intro future hbefore cache hfresh result hresult
      rw [treeValues_cons, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htailBind⟩ := hresult
      rw [mem_support_bind_iff] at htailBind
      obtain ⟨tail, htail, hpure⟩ := htailBind
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hheadFresh : TreeValuesFresh parameter future head.2 := by
        intro target htarget input hinput
        exact treeValue_preserves_fresh_later parameter secret current target
          (hbefore current (by simp) target htarget) cache head hhead
          input hinput (hfresh target htarget input hinput)
      apply ih future
        (fun candidate hcandidate target htarget =>
          hbefore candidate (by simp [hcandidate]) target htarget)
        head.2 hheadFresh tail htail

theorem treeValueIndicesBelow_height_lt :
    ∀ (height : Nat), height ≤ treeHeight + 1 →
      ∀ index ∈ treeValueIndicesBelow height, index.1.val < height := by
  intro height
  induction height with
  | zero => simp [treeValueIndicesBelow]
  | succ height ih =>
      intro hbound index hindex
      have hheight : height < treeHeight + 1 := by omega
      rw [treeValueIndicesBelow_succ height hheight,
        List.mem_append] at hindex
      rcases hindex with hprior | hcurrent
      · exact (ih (by omega) index hprior).trans (by omega)
      · have heq :=
          (mem_treeValueIndicesAtHeight_iff ⟨height, hheight⟩ index).1
            hcurrent
        simp [congrArg Fin.val heq]

theorem fixedChainMaterial_treeValues_fresh
    (parameter : PublicParameter) (_selected : ChainIndex)
    (material : FixedChainMaterial)
    (hleaf : ∀ epoch input,
      AtHashAddress parameter (.leaf epoch) input → material.2.2.2 input = none)
    (hmerkle : ∀ level node input,
      AtHashAddress parameter (.merkle level node) input →
        material.2.2.2 input = none) :
    TreeValuesFresh parameter allTreeValueIndices material.2.2.2 := by
  intro index _hindex input hinput
  by_cases hzero : index.1.val = 0
  · unfold TreeValueIndex.domain at hinput
    rw [dif_pos hzero] at hinput
    exact hleaf index.node input hinput
  · unfold TreeValueIndex.domain at hinput
    rw [dif_neg hzero] at hinput
    exact hmerkle ⟨index.1.val - 1, by omega⟩ index.node input hinput

theorem fixedChainMaterial_treeValuesBelow_fresh_at_height
    (parameter : PublicParameter) (selected : ChainIndex)
    (material : FixedChainMaterial)
    (hleaf : ∀ epoch input,
      AtHashAddress parameter (.leaf epoch) input → material.2.2.2 input = none)
    (hmerkle : ∀ level node input,
      AtHashAddress parameter (.merkle level node) input →
        material.2.2.2 input = none)
    (height : Fin (treeHeight + 1))
    (result : List Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      (treeValues parameter (unflattenSecret material.1.2)
        (treeValueIndicesBelow height.val) material.2.2.2)) :
    TreeValuesFresh parameter (treeValueIndicesAtHeight height) result.2 := by
  have hbefore : ∀ current ∈ treeValueIndicesBelow height.val,
      ∀ target ∈ treeValueIndicesAtHeight height,
        current.Precedes target := by
    intro current hcurrent target htarget
    have hcurrentLt := treeValueIndicesBelow_height_lt height.val
      (by omega) current hcurrent
    have htargetHeight :=
      (mem_treeValueIndicesAtHeight_iff height target).1 htarget
    left
    simpa [congrArg Fin.val htargetHeight] using hcurrentLt
  have hinitialFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) material.2.2.2 := by
    intro index hindex input hinput
    exact fixedChainMaterial_treeValues_fresh parameter selected material
      hleaf hmerkle index (mem_allTreeValueIndices index) input hinput
  exact treeValues_preserves_fresh_after parameter
    (unflattenSecret material.1.2)
    (treeValueIndicesBelow height.val) (treeValueIndicesAtHeight height)
    hbefore material.2.2.2 hinitialFresh result hresult

theorem relTriple_fixedChainMaterial_treeValuesBelow_one
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow 1) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow 1) right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2 ∧
          leftResult ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              (treeValueIndicesBelow 1) left.2.2.2) ∧
          rightResult ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              (treeValueIndicesBelow 1) right.1.2.2.2)) := by
  have hheight : treeValueIndicesBelow 1 =
      treeValueIndicesAtHeight 0 := by
    rw [treeValueIndicesBelow_succ 0 (by omega)]
    rw [treeValueIndicesBelow]
    exact List.nil_append _
  rw [hheight]
  exact relTriple_with_support_four
    (relTriple_fixedChainMaterial_allLeafValues_run
      parameter selected left right hrel)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem relTriple_fixedChainMaterial_treeValuesBelow_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
    ∀ (height : Nat), 1 ≤ height → height ≤ treeHeight + 1 →
      RelTriple
        (treeValues parameter (unflattenSecret left.1.2)
          (treeValueIndicesBelow height) left.2.2.2)
        (treeValues parameter (unflattenSecret right.1.1.2)
          (treeValueIndicesBelow height) right.1.2.2.2)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            HashCachesAgreeOn (OutsideChainHashInput parameter selected)
              leftResult.2 rightResult.2 ∧
            left.2.2.2 ≤ leftResult.2 ∧
            right.1.2.2.2 ≤ rightResult.2 ∧
            leftResult ∈ support
              (treeValues parameter (unflattenSecret left.1.2)
                (treeValueIndicesBelow height) left.2.2.2) ∧
            rightResult ∈ support
              (treeValues parameter (unflattenSecret right.1.1.2)
                (treeValueIndicesBelow height) right.1.2.2.2)) := by
  intro height
  induction height with
  | zero =>
      intro hpositive _hbound
      omega
  | succ height ih =>
      intro _hpositive hbound
      by_cases hzero : height = 0
      · subst height
        exact relTriple_fixedChainMaterial_treeValuesBelow_one
          parameter selected left right hrel
      · have hheightPositive : 1 ≤ height := by omega
        have hheightBound : height ≤ treeHeight + 1 := by omega
        have hcurrentBound : height < treeHeight + 1 := by omega
        let currentHeight : Fin (treeHeight + 1) :=
          ⟨height, hcurrentBound⟩
        have hprefix := ih hheightPositive hheightBound
        have hdecompose := treeValueIndicesBelow_succ height hcurrentBound
        rw [hdecompose, treeValues_append, treeValues_append]
        apply relTriple_bind hprefix
        intro leftBase rightBase hbase
        have hleftFresh :=
          fixedChainMaterial_treeValuesBelow_fresh_at_height
            parameter selected left hrel.leftLeafFresh hrel.leftMerkleFresh
            currentHeight
            leftBase hbase.2.2.2.2.1
        have hrightFresh :=
          fixedChainMaterial_treeValuesBelow_fresh_at_height
            parameter selected right.1 hrel.rightLeafFresh hrel.rightMerkleFresh
            currentHeight
            rightBase hbase.2.2.2.2.2
        have hheightCoupling := relTriple_fixedChainMaterial_merkleHeight_run
          parameter selected left right currentHeight (by
            dsimp [currentHeight]
            omega)
          leftBase rightBase hbase.2.2.2.2.1 hbase.2.2.2.2.2
          hbase.1 hleftFresh hrightFresh hbase.2.1
        apply relTriple_bind hheightCoupling
        intro leftCurrent rightCurrent hcurrent
        obtain ⟨leftValues, leftCache⟩ := leftBase
        obtain ⟨rightValues, rightCache⟩ := rightBase
        obtain ⟨leftNewValues, leftNewCache⟩ := leftCurrent
        obtain ⟨rightNewValues, rightNewCache⟩ := rightCurrent
        dsimp only at hbase hcurrent ⊢
        have hleftSupport := hcurrent.2.2.2.2.1
        have hrightSupport := hcurrent.2.2.2.2.2
        rw [treeValueIndicesBelow_succ height hcurrentBound,
          treeValues_append] at hleftSupport hrightSupport
        apply relTriple_pure_pure
        exact ⟨congrArg₂ List.append hbase.1 hcurrent.1,
          hcurrent.2.1, hcurrent.2.2.1,
          hcurrent.2.2.2.1, hleftSupport, hrightSupport⟩

theorem treeValueIndicesBelow_eq_flatMap
    (height : Nat) (hheight : height ≤ treeHeight + 1) :
    treeValueIndicesBelow height =
      (List.ofFn fun index : Fin height =>
        (⟨index.val, index.isLt.trans_le hheight⟩ :
          Fin (treeHeight + 1))).flatMap treeValueIndicesAtHeight := by
  induction height with
  | zero => simp [treeValueIndicesBelow]
  | succ height ih =>
      have hlt : height < treeHeight + 1 := by omega
      rw [treeValueIndicesBelow_succ height hlt, ih (by omega),
        List.ofFn_succ']
      simp

theorem treeValueIndicesBelow_all :
    treeValueIndicesBelow (treeHeight + 1) = allTreeValueIndices := by
  rw [treeValueIndicesBelow_eq_flatMap (treeHeight + 1) le_rfl]
  unfold allTreeValueIndices
  apply congrArg (List.flatMap treeValueIndicesAtHeight)
  apply List.ofFn_inj.2
  funext index
  apply Fin.ext
  rfl

theorem relTriple_fixedChainMaterial_allTreeValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        allTreeValueIndices left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        allTreeValueIndices right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2 ∧
          leftResult ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              allTreeValueIndices left.2.2.2) ∧
          rightResult ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              allTreeValueIndices right.1.2.2.2)) := by
  rw [← treeValueIndicesBelow_all]
  exact relTriple_fixedChainMaterial_treeValuesBelow_run
    parameter selected left right hrel (treeHeight + 1) (by omega) le_rfl

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_allTreeValues_root_and_paths
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        allTreeValueIndices left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        allTreeValueIndices right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          TreeValuesReplay parameter (unflattenSecret left.1.2)
            leftResult.2 allTreeValueIndices leftResult.1 ∧
          TreeValuesReplay parameter (unflattenSecret right.1.1.2)
            rightResult.2 allTreeValueIndices rightResult.1 ∧
          Concrete.CacheReplay.treeNode leftResult.2 parameter
              (unflattenSecret left.1.2) treeHeight Concrete.rootNode =
            Concrete.CacheReplay.treeNode rightResult.2 parameter
              (unflattenSecret right.1.1.2) treeHeight Concrete.rootNode ∧
          (∀ epoch,
            Concrete.CacheReplay.authenticationPath leftResult.2
                (SecretKey.withoutPrecomputation parameter
                  (unflattenSecret left.1.2)) epoch =
              Concrete.CacheReplay.authenticationPath rightResult.2
                (SecretKey.withoutPrecomputation parameter
                  (unflattenSecret right.1.1.2)) epoch) ∧
          HashCachesAgreeOn (OutsideChainHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left.2.2.2 ≤ leftResult.2 ∧
          right.1.2.2.2 ≤ rightResult.2) := by
  apply relTriple_post_mono
    (relTriple_fixedChainMaterial_allTreeValues_run
      parameter selected left right hrel)
  intro leftResult rightResult hresult
  have hleftReplay := treeValues_support_replay parameter
    (unflattenSecret left.1.2) allTreeValueIndices left.2.2.2
      leftResult hresult.2.2.2.2.1
  have hrightReplay := treeValues_support_replay parameter
    (unflattenSecret right.1.1.2) allTreeValueIndices right.1.2.2.2
      rightResult hresult.2.2.2.2.2
  refine ⟨hresult.1, hleftReplay, hrightReplay, ?_, ?_,
    hresult.2.1, hresult.2.2.1, hresult.2.2.2.1⟩
  · exact globalTreeValuesReplay_eq_root parameter
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      leftResult.2 rightResult.2 leftResult.1 hleftReplay
      (hresult.1 ▸ hrightReplay)
  · intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      leftResult.2 rightResult.2 leftResult.1 hleftReplay
      (hresult.1 ▸ hrightReplay) epoch

def ProgrammedActualKeygenCacheRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) : Prop :=
  ProgrammedActualKeygenBaseRelation chain left right ∧
    HashCachesAgreeOn
      (OutsideChainHashInput left.publicKey.parameter chain)
      left.cache right.1.cache

def CoupledWarmedKeygenCacheRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : CoupledWarmedKeygenView)
    (right : CoupledWarmedKeygenView × (ChainValueIndex → Digest)) : Prop :=
  CoupledWarmedKeygenBaseRelation parameter selected left right ∧
    HashCachesAgreeOn (OutsideChainHashInput parameter selected)
      left.cache right.1.cache

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedKeygenExperiment_withBase_cache
    (parameter : PublicParameter) (selected : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter selected)
      (coupledWarmedKeygenWithBase parameter selected)
      (CoupledWarmedKeygenCacheRelation parameter selected) := by
  classical
  let leftMaterialExperiment :=
    programmedWarmedTrajectoryMaterial parameter selected
  let rightMaterialExperiment := warmedTrajectoryMaterialWithBase
    parameter selected
  have hmaterials : RelTriple leftMaterialExperiment rightMaterialExperiment
      (fun left right =>
        warmedMaterialOutsideTable selected left =
            warmedMaterialBaseView selected right ∧
          left ∈ support leftMaterialExperiment ∧
          right ∈ support rightMaterialExperiment) := by
    apply relTriple_of_evalDist_map_eq_with_support_general
    exact evalDist_warmedMaterialOutsideTable_eq_baseView parameter selected
  unfold coupledWarmedKeygenExperiment coupledWarmedKeygenWithBase
  change RelTriple
    (leftMaterialExperiment >>= fun material =>
      treeValues parameter (unflattenSecret material.1.2)
        allTreeValueIndices material.2.2 >>= fun tree =>
      pure ({
        secret := unflattenSecret material.1.2
        table := chainValueTableOfList material.2.1
        values := tree.1
        cache := tree.2
      } : CoupledWarmedKeygenView))
    (rightMaterialExperiment >>= fun materialBase =>
      treeValues parameter (unflattenSecret materialBase.1.1.2)
        allTreeValueIndices materialBase.1.2.2 >>= fun tree =>
      pure (({
        secret := unflattenSecret materialBase.1.1.2
        table := chainValueTableOfList materialBase.1.2.1
        values := tree.1
        cache := tree.2
      } : CoupledWarmedKeygenView), materialBase.2))
    (CoupledWarmedKeygenCacheRelation parameter selected)
  apply relTriple_bind hmaterials
  intro leftMaterial rightMaterialBase hmaterial
  let rightMaterial := rightMaterialBase.1
  have hleft : leftMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter selected) := by
    simpa [leftMaterialExperiment] using hmaterial.2.1
  have hrightBase : rightMaterialBase ∈ support
      (warmedTrajectoryMaterialWithBase parameter selected) := by
    simpa [rightMaterialExperiment] using hmaterial.2.2
  have hright : rightMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter selected) :=
    warmedTrajectoryMaterialWithBase_support_material
      parameter selected rightMaterialBase hrightBase
  have hinvariant := warmedMaterialsAsFixed_invariant parameter selected
    leftMaterial rightMaterial rightMaterialBase.2 hleft hright
      (congrArg Prod.snd hmaterial.1)
      (congrArg Prod.fst hmaterial.1)
  have htrees := relTriple_fixedChainMaterial_allTreeValues_root_and_paths
    parameter selected (warmedMaterialAsFixed selected leftMaterial)
      (warmedMaterialAsFixed selected rightMaterial, rightMaterialBase.2)
      hinvariant
  have htable := hinvariant.tableEq
  rw [fixedChainMaterialTable_warmedMaterialAsFixed
    parameter selected leftMaterial hleft] at htable
  apply relTriple_bind htrees
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  refine ⟨⟨htable, ?_, htree.1, htree.2.1,
    htree.2.2.1, htree.2.2.2.1, htree.2.2.2.2.1⟩, ?_⟩
  · exact secretOutsideChain_eq_of_outsideChainSecret_eq selected
      leftMaterial.1.2 rightMaterial.1.2 hinvariant.outsideEq
  · exact htree.2.2.2.2.2.1

theorem relTriple_coupledWarmedFixedChainKeygen_withBase_cache
    (chain : ChainIndex) :
    RelTriple
      (coupledWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBase chain)
      (ProgrammedActualKeygenCacheRelation chain) := by
  unfold coupledWarmedFixedChainKeygen
    coupledWarmedFixedChainKeygenWithBase
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_withBase_cache
      leftParameter chain)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨⟨hview.1.1, ?_, hview.1.2.1, hview.1.2.2.2.2.2.2⟩, ?_⟩
  · exact congrArg (fun root => PublicKey.mk root leftParameter)
      hview.1.2.2.2.2.2.1
  · exact hview.2

theorem relTriple_programmedWarmedFixedChainKeygen_withBase_cache
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))
      (ProgrammedActualKeygenCacheRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain).symm
  exact relTriple_of_evalDist_eq_right
    (evalDist_coupledWarmedFixedChainKeygenWithBase_eq_actual chain)
      (relTriple_coupledWarmedFixedChainKeygen_withBase_cache chain)

noncomputable def fixedChainTreeKeygenView
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : FixedChainMaterial)
    (tree : List Digest × QueryCache HashSpec) :
    ProgrammedFixedChainKeygenView := {
  publicKey := ⟨Concrete.CacheReplay.treeNode tree.2 parameter
    (unflattenSecret material.1.2) treeHeight Concrete.rootNode, parameter⟩
  secretKey := SecretKey.withoutPrecomputation parameter
    (unflattenSecret material.1.2)
  cache := tree.2
  table := fixedChainMaterialTable chain material
}

noncomputable def fixedChainTreeKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let material ← fixedChainMaterialRepresentation parameter chain
  let tree ← treeValues parameter (unflattenSecret material.1.2)
    allTreeValueIndices material.2.2.2
  pure (fixedChainTreeKeygenView parameter chain material tree)

noncomputable def fixedChainTreeKeygenWithBase
    (chain : ChainIndex) :
    ProbComp (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let materialBase ← fixedChainMaterialWithBase parameter chain
  let tree ← treeValues parameter (unflattenSecret materialBase.1.1.2)
    allTreeValueIndices materialBase.1.2.2.2
  pure (fixedChainTreeKeygenView parameter chain materialBase.1 tree,
    materialBase.2)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainTreeKeygen_eq_programmedFixed
    (chain : ChainIndex) :
    evalDist (fixedChainTreeKeygen chain) =
      evalDist (programmedFixedChainKeygen chain) := by
  unfold fixedChainTreeKeygen programmedFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro material
  let secret := unflattenSecret material.1.2
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := fixedChainMaterialTable chain material
  }
  symm
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run material.2.2.2 >>= finish) =
      evalDist (((fun tree : List Digest × QueryCache HashSpec =>
        (Concrete.CacheReplay.treeNode tree.2 parameter secret
          treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter secret allTreeValueIndices material.2.2.2) >>=
              finish) := by
        rw [evalDist_bind,
          evalDist_rootTree_run_eq_treeValues_root_cache,
          ← evalDist_bind]
    _ = evalDist (treeValues parameter secret allTreeValueIndices
          material.2.2.2 >>= fun tree =>
        pure (fixedChainTreeKeygenView parameter chain material tree)) := by
      simp [finish, fixedChainTreeKeygenView, secret,
        SecretKey.withoutPrecomputation, map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_fixedChainTreeKeygenWithBase_eq_independentBase
    (chain : ChainIndex) :
    evalDist (fixedChainTreeKeygenWithBase chain) =
      evalDist (fixedChainTreeKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base)) := by
  unfold fixedChainTreeKeygenWithBase fixedChainTreeKeygen
    fixedChainMaterialWithBase
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro material
  let finish : (ChainValueIndex → Digest) →
      (List Digest × QueryCache HashSpec) →
      ProbComp (ProgrammedFixedChainKeygenView ×
        (ChainValueIndex → Digest)) := fun base tree =>
    pure (fixedChainTreeKeygenView parameter chain material tree, base)
  simpa [finish, bind_assoc] using
    (OracleComp.DeferredSampling.evalDist_bind_comm
      (uniformChainValueTable chain)
      (treeValues parameter (unflattenSecret material.1.2)
        allTreeValueIndices material.2.2.2) finish)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_fixedChainTreeKeygen_withBase
    (chain : ChainIndex) :
    RelTriple
      (fixedChainTreeKeygen chain)
      (fixedChainTreeKeygenWithBase chain)
      (ProgrammedActualKeygenCacheRelation chain) := by
  unfold fixedChainTreeKeygen fixedChainTreeKeygenWithBase
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_fixedChainMaterialRepresentation_withBase_invariant
      leftParameter chain)
  intro leftMaterial rightMaterial hmaterial
  apply relTriple_bind
    (relTriple_fixedChainMaterial_allTreeValues_root_and_paths
      leftParameter chain leftMaterial rightMaterial hmaterial)
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  refine ⟨⟨hmaterial.tableEq, ?_, ?_, htree.2.2.2.2.1⟩, ?_⟩
  · exact congrArg (fun root => PublicKey.mk root leftParameter)
      htree.2.2.2.1
  · exact secretOutsideChain_eq_of_outsideChainSecret_eq chain
      leftMaterial.1.2 rightMaterial.1.1.2 hmaterial.outsideEq
  · exact htree.2.2.2.2.2.1

theorem relTriple_programmedFixedChainKeygen_withBase_cache
    (chain : ChainIndex) :
    RelTriple
      (programmedFixedChainKeygen chain)
      (programmedFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))
      (ProgrammedActualKeygenCacheRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_fixedChainTreeKeygen_eq_programmedFixed chain).symm
  have hright : evalDist (fixedChainTreeKeygenWithBase chain) =
      evalDist (programmedFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base)) := by
    calc
      evalDist (fixedChainTreeKeygenWithBase chain) =
          evalDist (fixedChainTreeKeygen chain >>= fun keyView =>
            uniformChainValueTable chain >>= fun base => pure (keyView, base)) :=
        evalDist_fixedChainTreeKeygenWithBase_eq_independentBase chain
      _ = evalDist (programmedFixedChainKeygen chain >>= fun keyView =>
            uniformChainValueTable chain >>= fun base => pure (keyView, base)) := by
        rw [evalDist_bind,
          evalDist_fixedChainTreeKeygen_eq_programmedFixed,
          ← evalDist_bind]
  exact relTriple_of_evalDist_eq_right hright
    (relTriple_fixedChainTreeKeygen_withBase chain)

end XmssSecurity
