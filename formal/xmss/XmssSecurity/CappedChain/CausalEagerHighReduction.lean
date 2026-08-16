import XmssSecurity.CausalWarmedHighIndependence
import XmssSecurity.CappedChain.CausalDirectReduction
import XmssSecurity.CappedChain.CappedObservedSigning
import XmssSecurity.CausalTreeCacheCorrespondence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

noncomputable local instance eagerHighSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

attribute [local irreducible]
  coupledWarmedFixedChainKeygenWithHigh
  coupledWarmedFixedChainKeygenWithBaseHigh
  coupledWarmedFixedChainKeygen
  coupledWarmedKeygenExperiment
  coupledWarmedKeygenWithBaseHigh
  programmedWarmedFixedChainKeygen

noncomputable def highProgrammedWarmedDetailedGame
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← XmssSecurity.programmedWarmedFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey keyView.secretKey keyView.cache
  pure ((keyView, execution.1), execution.2)

theorem evalDist_chronologicallyWarmedDetailedGame_eq_highProgrammed
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex) :
    evalDist (chronologicallyWarmedDetailedGame adversary chain) =
      evalDist (highProgrammedWarmedDetailedGame adversary chain) := by
  unfold chronologicallyWarmedDetailedGame highProgrammedWarmedDetailedGame
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  have hkeygen :
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) =
        evalDist (XmssSecurity.programmedWarmedFixedChainKeygen chain) := by
    calc
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) =
        evalDist (actualFixedChainKeygen chain) :=
        (evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed chain).symm
      _ = evalDist (XmssSecurity.actualFixedChainKeygen chain) := by rfl
      _ = evalDist (XmssSecurity.programmedWarmedFixedChainKeygen chain) :=
        XmssSecurity.evalDist_actualFixedChainKeygen_eq_programmedWarmed chain
  rw [hkeygen]


noncomputable def uniformCoupledWarmedFixedChainKeygenWithHigh
    (chain : ChainIndex) :
    ProbComp ((ProgrammedFixedChainKeygenView × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) := do
  let base ← $ᵗ (ChainValueIndex → Digest)
  let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
  pure ((keyHigh.1, base), keyHigh.2)


attribute [local irreducible]
  uniformCoupledWarmedFixedChainKeygenWithHigh

set_option maxHeartbeats 50000 in
set_option maxRecDepth 1000000 in
theorem evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
    (chain : ChainIndex) :
    evalDist (uniformCoupledWarmedFixedChainKeygenWithHigh chain) =
    evalDist (coupledWarmedFixedChainKeygenWithBaseHigh chain) := by
  unfold uniformCoupledWarmedFixedChainKeygenWithHigh
  calc
    _ = evalDist (do
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        let base ← $ᵗ (ChainValueIndex → Digest)
        pure ((keyHigh.1, base), keyHigh.2)) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (ChainValueIndex → Digest))
        (coupledWarmedFixedChainKeygenWithHigh chain)
        (fun base keyHigh => pure ((keyHigh.1, base), keyHigh.2))
    _ = evalDist (do
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        let base ← uniformChainValueTable chain
        pure ((keyHigh.1, base), keyHigh.2)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyHigh
      unfold uniformChainValueTable
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
        0 chain]
    _ = evalDist (coupledWarmedFixedChainKeygenWithBaseHigh chain) := by
      unfold coupledWarmedFixedChainKeygenWithHigh
        coupledWarmedFixedChainKeygenWithBaseHigh
        coupledWarmedKeygenExperimentWithHigh
        coupledWarmedKeygenWithBaseHigh
        programmedWarmedTrajectoryMaterialWithBaseHigh
      simp only [bind_assoc, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameter
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro materialHigh
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        (treeValues parameter (unflattenSecret materialHigh.1.1.2)
          allTreeValueIndices materialHigh.1.2.2)
        (uniformChainValueTable chain)
        (fun tree base => pure
          ((CoupledWarmedKeygenView.toProgrammedView parameter {
              secret := unflattenSecret materialHigh.1.1.2
              table := chainValueTableOfList materialHigh.1.2.1
              values := tree.1
              cache := tree.2
            }, base), materialHigh.2))


set_option maxHeartbeats 50000 in
set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_uniformHigh
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (uniformCoupledWarmedFixedChainKeygenWithHigh chain)
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_right
    (evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
      chain).symm
  exact relTriple_programmedWarmedFixedChainKeygen_withBaseHigh chain

structure CoupledWarmedKeygenTreeCacheHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : CoupledWarmedKeygenView)
    (right : (CoupledWarmedKeygenView × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) : Prop where
  base : CoupledWarmedKeygenCacheHighRelation parameter chain left right
  retained : HashCachesAgreeOn (TreeRetainedHashInput parameter chain)
    left.cache right.1.1.cache
  replayLeaves : ∃ leftEndpoints rightEndpoints,
    LeafReplayWitness parameter left.secret right.1.1.secret left.cache
      right.1.1.cache leftEndpoints rightEndpoints

set_option maxHeartbeats 10000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedKeygenExperiment_withBaseHigh_tree
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter chain)
      (coupledWarmedKeygenWithBaseHigh parameter chain)
      (CoupledWarmedKeygenTreeCacheHighRelation parameter chain) := by
  unfold coupledWarmedKeygenExperiment coupledWarmedKeygenWithBaseHigh
  apply relTriple_bind
    (relTriple_programmedWarmedTrajectoryMaterial_withBaseHigh parameter chain)
  intro leftMaterial rightMaterialBaseHigh hmaterial
  let rightMaterial := rightMaterialBaseHigh.1.1
  have hinvariant := warmedMaterialsAsFixed_invariant parameter chain
    leftMaterial rightMaterial rightMaterialBaseHigh.1.2
      hmaterial.leftSupport hmaterial.rightSupport hmaterial.tableEq
        hmaterial.outsideEq
  have htrees := relTriple_with_support
    (relTriple_fixedChainMaterial_allTreeValues_run_with_correspondence
      parameter chain (warmedMaterialAsFixed chain leftMaterial)
        (warmedMaterialAsFixed chain rightMaterial,
          rightMaterialBaseHigh.1.2) hinvariant)
  have htable := hinvariant.tableEq
  rw [fixedChainMaterialTable_warmedMaterialAsFixed parameter chain
    leftMaterial hmaterial.leftSupport] at htable
  apply relTriple_bind htrees
  intro leftTree rightTree htree
  obtain ⟨htreeRelation, hleftTreeSupport, hrightTreeSupport⟩ := htree
  obtain ⟨hvalues, leftEndpoints, rightEndpoints, hcache,
    hleftEndpointReplay, hrightEndpointReplay⟩ := htreeRelation
  have hleftTreeReplay := treeValues_support_replay parameter
    (unflattenSecret leftMaterial.1.2) allTreeValueIndices
      leftMaterial.2.2 leftTree hleftTreeSupport
  have hrightTreeReplay := treeValues_support_replay parameter
    (unflattenSecret rightMaterial.1.2) allTreeValueIndices
      rightMaterial.2.2 rightTree hrightTreeSupport
  have hroot := globalTreeValuesReplay_eq_root parameter
    (unflattenSecret leftMaterial.1.2) (unflattenSecret rightMaterial.1.2)
      leftTree.2 rightTree.2 leftTree.1 hleftTreeReplay
        (hvalues ▸ hrightTreeReplay)
  have hauth : ∀ epoch,
      Concrete.CacheReplay.authenticationPath leftTree.2
          ⟨parameter, unflattenSecret leftMaterial.1.2⟩ epoch =
        Concrete.CacheReplay.authenticationPath rightTree.2
          ⟨parameter, unflattenSecret rightMaterial.1.2⟩ epoch := by
    intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      (unflattenSecret leftMaterial.1.2) (unflattenSecret rightMaterial.1.2)
        leftTree.2 rightTree.2 leftTree.1 hleftTreeReplay
          (hvalues ▸ hrightTreeReplay) epoch
  have hleftCacheLe := treeValues_cache_le parameter
    (unflattenSecret leftMaterial.1.2) allTreeValueIndices
      leftMaterial.2.2 leftTree hleftTreeSupport
  apply relTriple_pure_pure
  refine ⟨?_, hcache.retained,
    leftEndpoints, rightEndpoints,
      ⟨hcache.leaves, hleftEndpointReplay, hrightEndpointReplay⟩⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨⟨htable, ?_, hvalues, hleftTreeReplay, hrightTreeReplay,
          hroot, hauth⟩, ?_⟩
      · exact secretOutsideChain_eq_of_outsideChainSecret_eq chain
          leftMaterial.1.2 rightMaterial.1.2 hinvariant.outsideEq
      · intro input hinput
        exact hcache.retained input (Or.inl hinput)
    · have htrajectory := programmedWarmedTrajectoryMaterial_support_trajectory
          parameter chain leftMaterial hmaterial.leftSupport
      have hmatches := programmedFixedSeedChainTrajectories_edgesMatch parameter
        (unflattenSecret leftMaterial.1.2) chain leftMaterial.2 htrajectory
      calc
        chainEdgeHighTableOfCache leftTree.2 parameter chain
            (chainValueTableOfList leftMaterial.2.1) =
          chainEdgeHighTableOfCache leftMaterial.2.2 parameter chain
            (chainValueTableOfList leftMaterial.2.1) :=
              (chainEdgeHighTableOfCache_mono leftMaterial.2.2 leftTree.2
                parameter chain (chainValueTableOfList leftMaterial.2.1)
                  hmatches hleftCacheLe).symm
        _ = rightMaterialBaseHigh.2 := hmaterial.highEq

def replayLeafInput
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : HashInput :=
  Concrete.CacheView.leafInput parameter epoch
    (Concrete.CacheReplay.oneTimePublicKey cache parameter secret epoch)

structure LeafReplayCacheEq
    (leftCache rightCache : QueryCache HashSpec)
    (rightInput input : HashInput) : Prop where
  eq : rightCache rightInput = leftCache input

structure LeafCachePair
    (output : HashOutput) (leftCache rightCache : QueryCache HashSpec)
    (leftInput rightInput : HashInput) : Prop where
  leftCached : leftCache leftInput = some output
  rightCached : rightCache rightInput = some output

def LeafReplayAt
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) (epoch : Epoch) : Prop :=
  leftCache (replayLeafInput leftCache parameter leftSecret epoch) =
    rightCache (replayLeafInput rightCache parameter rightSecret epoch)

theorem LeafReplayAt.eq
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) (epoch : Epoch)
    (hrel : LeafReplayAt parameter leftSecret rightSecret leftCache rightCache
      epoch) :
    leftCache (replayLeafInput leftCache parameter leftSecret epoch) =
      rightCache (replayLeafInput rightCache parameter rightSecret epoch) := by
  exact hrel

structure LeafReplayCorrespondence
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop where
  outputs (epoch : Epoch) : LeafReplayAt parameter leftSecret rightSecret
    leftCache rightCache epoch
  transport (epoch : Epoch) (rightInput input : HashInput)
    (hrightInput : rightInput = replayLeafInput rightCache parameter rightSecret
      epoch)
    (hleftInput : input = replayLeafInput leftCache parameter leftSecret epoch) :
    LeafReplayCacheEq leftCache rightCache rightInput input

structure ProgrammedActualKeygenTreeCacheHighRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) : Prop where
  base : ProgrammedActualKeygenCacheHighRelation chain left right
  retained : HashCachesAgreeOn
    (TreeRetainedHashInput left.secretKey.parameter chain)
    left.cache right.1.1.cache
  replayLeaves : LeafReplayCorrespondence left.secretKey.parameter
    left.secretKey.chainStart right.1.1.secretKey.chainStart left.cache
      right.1.1.cache

theorem ProgrammedActualKeygenTreeCacheHighRelation.parameter_eq
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation chain left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen chain))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen chain)) :
    right.1.1.secretKey.parameter = left.secretKey.parameter := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    chain left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult chain right.1.1
    hrightSupport
  calc
    right.1.1.secretKey.parameter = right.1.1.publicKey.parameter :=
      (right.1.1.parameter_eq hrightKey).symm
    _ = left.publicKey.parameter :=
      congrArg PublicKey.parameter hrel.base.base.1.2.1.symm
    _ = left.secretKey.parameter := left.parameter_eq hleftKey

theorem ProgrammedActualKeygenTreeCacheHighRelation.replay_other_eq
    (selected candidate : ChainIndex) (hne : candidate ≠ selected)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (epoch : Epoch) :
    Concrete.CacheReplay.oneTimePublicKey left.cache
        left.secretKey.parameter left.secretKey.chainStart epoch candidate =
      Concrete.CacheReplay.oneTimePublicKey right.1.1.cache
        right.1.1.secretKey.parameter right.1.1.secretKey.chainStart
          epoch candidate := by
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hcaches : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
      left.cache right.1.1.cache := by
    rw [← left.parameter_eq hleftKey]
    exact hrel.base.base.2
  rw [hparameter]
  unfold Concrete.CacheReplay.oneTimePublicKey
  rw [secret_eq_of_outsideChain_eq selected left.secretKey.chainStart
      right.1.1.secretKey.chainStart hrel.base.base.1.2.2.1 epoch candidate hne,
    Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
      left.secretKey.parameter selected candidate hne left.cache
        right.1.1.cache hcaches epoch]

set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedFixedChainKeygen_withBaseHigh_tree
    (chain : ChainIndex) :
    RelTriple
      (coupledWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenTreeCacheHighRelation chain) := by
  unfold coupledWarmedFixedChainKeygen
    coupledWarmedFixedChainKeygenWithBaseHigh
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_withBaseHigh_tree
      leftParameter chain)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨⟨hview.base.base.1.1, ?_, hview.base.base.1.2.1,
          hview.base.base.1.2.2.2.2.2.2⟩, hview.base.base.2⟩
      exact congrArg (fun root => PublicKey.mk root leftParameter)
        hview.base.base.1.2.2.2.2.2.1
    · simpa [CoupledWarmedKeygenView.toProgrammedView] using hview.base.highEq
  · simpa [CoupledWarmedKeygenView.toProgrammedView] using hview.retained
  · obtain ⟨leftEndpoints, rightEndpoints, hwitness⟩ := hview.replayLeaves
    have houtputs := LeafReplayWitness.outputsCorrespond _ _ _ _ _
      leftEndpoints rightEndpoints hwitness
    have houtputAt : ∀ epoch, LeafReplayAt leftParameter leftView.secret
        rightView.1.1.secret leftView.cache rightView.1.1.cache epoch := by
      intro epoch
      simpa [LeafReplayAt, replayLeafInput,
        CoupledWarmedKeygenView.toProgrammedView] using houtputs epoch
    refine ⟨houtputAt, ?_⟩
    intro epoch rightInput input hrightInput hleftInput
    subst rightInput
    subst input
    constructor
    exact (LeafReplayAt.eq _ _ _ _ _ _ (houtputAt epoch)).symm

theorem relTriple_programmedWarmedFixedChainKeygen_withBaseHigh_tree
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenTreeCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain).symm
  exact relTriple_coupledWarmedFixedChainKeygen_withBaseHigh_tree chain

theorem relTriple_programmedWarmedFixedChainKeygen_uniformHigh_tree
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (uniformCoupledWarmedFixedChainKeygenWithHigh chain)
      (ProgrammedActualKeygenTreeCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_right
    (evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
      chain).symm
  exact relTriple_programmedWarmedFixedChainKeygen_withBaseHigh_tree chain


def KeygenAddressedHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, AtHashAddress parameter domain input

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (KeygenAddressedHashInput parameter) :=
  Classical.decPred _

theorem Concrete.tweakableHash_queryBound_zero_unaddressed
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash,
    KeygenAddressedHashInput]

theorem Concrete.chainWalk_queryBound_zero_unaddressed
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter epoch chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.oneTimePublicKey_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    (Concrete.oneTimePublicKey parameter secret epoch :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.oneTimePublicKey]
  apply Concrete.sequenceFin_queryBound_zero
  intro chain
  exact Concrete.chainWalk_queryBound_zero_unaddressed parameter epoch chain
    0 (chainLength - 1) (secret epoch chain)

theorem Concrete.leafAt_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    (Concrete.leafAt parameter secret epoch :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_unaddressed parameter secret
      epoch) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _

theorem Concrete.treeNode_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact Concrete.leafAt_queryBound_zero_unaddressed parameter secret node
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node false)) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node true)) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.keygen_cache_none_unaddressed
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (input : HashInput)
    (hinput : ¬ KeygenAddressedHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Concrete.treeNode_queryBound_zero_unaddressed parameter secret
      treeHeight Concrete.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

theorem Concrete.keygen_cache_none_at_encodingAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress keyResult.1.2.parameter (.encoding epoch) input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Concrete.treeNode_queryBound_zero_encodingAddress parameter secret
      epoch treeHeight Concrete.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot


noncomputable def eagerTreeInputProbe?
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Option (ChainValueIndex × Digest) :=
  match chainInputProbe? parameter selected input with
  | some probe => some probe
  | none => leafInputProbe? parameter selected input

def LeafInputMatchesOutside
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (selected : ChainIndex) (input : HashInput) : Prop :=
  ∃ epoch endpoints,
    input = Concrete.CacheView.leafInput secretKey.parameter epoch endpoints ∧
      ∀ chain, chain ≠ selected →
        endpoints chain = Concrete.CacheReplay.oneTimePublicKey cache
          secretKey.parameter secretKey.chainStart epoch chain

noncomputable instance (parameter : PublicParameter) (selected : ChainIndex) :
    DecidablePred (TreeRetainedHashInput parameter selected) :=
  Classical.decPred _

noncomputable instance (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (selected : ChainIndex) :
    DecidablePred (LeafInputMatchesOutside secretKey cache selected) :=
  Classical.decPred _

attribute [local irreducible] causalHashQuery
attribute [local irreducible] filteredProbingAttackerHashQueryAtFromHigh

abbrev FilteredTreeHashComputation :=
  OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
    (HashOutput × CausalHashState)

inductive FilteredTreeHashProgram where
  | chain (probe : ChainValueIndex × Digest)
  | currentCached
  | keygenCached
  | leafCached
  | fresh
  | leafProbe (probe : ChainValueIndex × Digest)

noncomputable def filteredTreeKeygenLeafOutput
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState) :
    Option HashOutput :=
  state.keygenCache (keygenLeafTargetInput secretKey state.keygenCache input)

noncomputable def filteredTreeChainHashComputation
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : ChainValueIndex × Digest) :
    FilteredTreeHashComputation :=
  filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input state
    (some probe)

noncomputable def filteredTreePureHashComputation
    (output : HashOutput) (state : CausalHashState) :
    FilteredTreeHashComputation :=
  pure (output, state)

noncomputable def filteredTreeFreshHashComputation
    (input : HashInput) (state : CausalHashState) :
    FilteredTreeHashComputation :=
  (causalHashQuery input).run state

noncomputable def filteredTreeProbeThenFreshHashComputation
    (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex) (target : Digest) :
    FilteredTreeHashComputation := do
  let _ ← RevealProbeOracleSimulation.probeQuery index target
  filteredTreeFreshHashComputation input state

noncomputable def FilteredTreeHashProgram.computation
    (program : FilteredTreeHashProgram)
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredTreeHashComputation :=
  match program with
  | .chain probe => filteredTreeChainHashComputation high secretKey selected
      input state probe
  | .currentCached =>
      match state.cache input with
      | some output => filteredTreePureHashComputation output state
      | none => filteredTreeFreshHashComputation input state
  | .keygenCached =>
      match state.keygenCache input with
      | some output => filteredTreePureHashComputation output state
      | none => filteredTreeFreshHashComputation input state
  | .leafCached =>
      match filteredTreeKeygenLeafOutput secretKey input state with
      | some output => filteredTreePureHashComputation output state
      | none => filteredTreeFreshHashComputation input state
  | .fresh => filteredTreeFreshHashComputation input state
  | .leafProbe probe => filteredTreeProbeThenFreshHashComputation input state
      probe.1 probe.2


set_option maxHeartbeats 50000
set_option maxRecDepth 1000000

def filteredTreeOuterPlan
    (chainProbe : Option (ChainValueIndex × Digest))
    (noChain : FilteredTreeHashProgram) : FilteredTreeHashProgram :=
  match chainProbe with
  | some probe => FilteredTreeHashProgram.chain probe
  | none => noChain

def filteredTreeNoChainPlan
    (leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (leaf : ChainValueIndex × Digest → FilteredTreeHashProgram) :
    FilteredTreeHashProgram :=
  match leafProbe with
  | none => ordinary
  | some probe => leaf probe

def filteredTreeOrdinaryPlan
    (current : Option HashOutput) (retained : Bool)
    (keygen : Option HashOutput) : FilteredTreeHashProgram :=
  match current with
  | some _ => FilteredTreeHashProgram.currentCached
  | none => if retained then
      match keygen with
      | some _ => FilteredTreeHashProgram.keygenCached
      | none => FilteredTreeHashProgram.fresh
    else FilteredTreeHashProgram.fresh

def filteredTreeLeafPlan
    (index : ChainValueIndex) (revealed : Option Digest) (target : Digest) (isMatch : Bool)
    (cached : Option HashOutput) : FilteredTreeHashProgram :=
  match revealed with
  | some value => if value = target then
      if isMatch then
        match cached with
        | some _ => FilteredTreeHashProgram.leafCached
        | none => FilteredTreeHashProgram.fresh
      else FilteredTreeHashProgram.fresh
    else FilteredTreeHashProgram.fresh
  | none => FilteredTreeHashProgram.leafProbe (index, target)

noncomputable def filteredTreeLeafHashQueryAtFromHigh
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest) :
    FilteredTreeHashProgram :=
  filteredTreeLeafPlan index (state.revealed index) target
    (decide (LeafInputMatchesOutside secretKey state.keygenCache selected input))
    (filteredTreeKeygenLeafOutput secretKey input state)

noncomputable def filteredTreeOrdinaryHashQueryAtFromHigh
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredTreeHashProgram :=
  filteredTreeOrdinaryPlan (state.cache input)
    (decide (TreeRetainedHashInput secretKey.parameter selected input))
    (state.keygenCache input)

noncomputable def filteredTreeNoChainHashQueryAtFromHigh
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredTreeHashProgram :=
  filteredTreeNoChainPlan (leafInputProbe? secretKey.parameter selected input)
    (filteredTreeOrdinaryHashQueryAtFromHigh secretKey selected input state)
    (fun probe => filteredTreeLeafHashQueryAtFromHigh secretKey selected input
      state probe.1 probe.2)

noncomputable def filteredTreeProbingAttackerHashQueryAtFromHigh
    (_high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    FilteredTreeHashProgram :=
  filteredTreeOuterPlan (chainInputProbe? secretKey.parameter selected input)
    (filteredTreeNoChainHashQueryAtFromHigh secretKey selected input state)

noncomputable def filteredTreeHashComputationAtFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredTreeHashComputation :=
  (filteredTreeProbingAttackerHashQueryAtFromHigh high secretKey selected input
    state).computation high secretKey selected input state

attribute [local irreducible]
  FilteredTreeHashProgram.computation
  filteredTreeHashComputationAtFromHigh
  filteredTreeChainHashComputation
  filteredTreePureHashComputation
  filteredTreeFreshHashComputation
  filteredTreeProbeThenFreshHashComputation


structure FilteredTreePlanIs
    (expected : FilteredTreeHashProgram)
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : Prop where
  eq : filteredTreeProbingAttackerHashQueryAtFromHigh high secretKey selected
      input state = expected

theorem filteredTreeOuterPlan_eq_chain
    (probe? : Option (ChainValueIndex × Digest))
    (fallback : FilteredTreeHashProgram)
    (probe : ChainValueIndex × Digest) (hprobe : probe? = some probe) :
    filteredTreeOuterPlan probe? fallback = FilteredTreeHashProgram.chain probe := by
  subst probe?
  rfl

theorem filteredTreeOuterPlan_eq_currentCached
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (current : Option HashOutput) (output : HashOutput)
    (leafPlan : ChainValueIndex × Digest → FilteredTreeHashProgram)
    (retained : Bool) (keygen : Option HashOutput)
    (hchain : chainProbe = none) (hleaf : leafProbe = none)
    (hcurrent : current = some output) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe
        (filteredTreeOrdinaryPlan current retained keygen) leafPlan) =
      FilteredTreeHashProgram.currentCached := by
  subst chainProbe
  subst leafProbe
  subst current
  rfl

theorem filteredTreeOuterPlan_eq_keygenCached
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (current : Option HashOutput) (retained : Bool)
    (keygen : Option HashOutput) (output : HashOutput)
    (leafPlan : ChainValueIndex × Digest → FilteredTreeHashProgram)
    (hchain : chainProbe = none) (hleaf : leafProbe = none)
    (hcurrent : current = none) (hretained : retained = true)
    (hkeygen : keygen = some output) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe
        (filteredTreeOrdinaryPlan current retained keygen) leafPlan) =
      FilteredTreeHashProgram.keygenCached := by
  subst chainProbe
  subst leafProbe
  subst current
  subst retained
  subst keygen
  rfl

theorem filteredTreeOuterPlan_eq_fresh_of_not_retained
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (current : Option HashOutput) (retained : Bool)
    (keygen : Option HashOutput)
    (leafPlan : ChainValueIndex × Digest → FilteredTreeHashProgram)
    (hchain : chainProbe = none) (hleaf : leafProbe = none)
    (hcurrent : current = none) (hretained : retained = false) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe
        (filteredTreeOrdinaryPlan current retained keygen) leafPlan) =
      FilteredTreeHashProgram.fresh := by
  subst chainProbe
  subst leafProbe
  subst current
  subst retained
  rfl

theorem filteredTreeOuterPlan_eq_fresh_of_keygen_none
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (current : Option HashOutput) (retained : Bool)
    (keygen : Option HashOutput)
    (leafPlan : ChainValueIndex × Digest → FilteredTreeHashProgram)
    (hchain : chainProbe = none) (hleaf : leafProbe = none)
    (hcurrent : current = none) (hretained : retained = true)
    (hkeygen : keygen = none) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe
        (filteredTreeOrdinaryPlan current retained keygen) leafPlan) =
      FilteredTreeHashProgram.fresh := by
  subst chainProbe
  subst leafProbe
  subst current
  subst retained
  subst keygen
  rfl

theorem filteredTreeOuterPlan_eq_leafProbe
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (revealed : ChainValueIndex → Option Digest) (isMatch : Bool)
    (cached : Option HashOutput) (index : ChainValueIndex) (target : Digest)
    (hchain : chainProbe = none)
    (hleaf : leafProbe = some (index, target))
    (hhidden : revealed index = none) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe ordinary (fun probe =>
        filteredTreeLeafPlan probe.1 (revealed probe.1) probe.2 isMatch cached)) =
      FilteredTreeHashProgram.leafProbe (index, target) := by
  subst chainProbe
  subst leafProbe
  simp [filteredTreeOuterPlan, filteredTreeNoChainPlan, filteredTreeLeafPlan,
    hhidden]

theorem filteredTreeOuterPlan_eq_leafCached
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (revealed : ChainValueIndex → Option Digest) (isMatch : Bool)
    (cached : Option HashOutput) (index : ChainValueIndex) (target : Digest)
    (output : HashOutput) (hchain : chainProbe = none)
    (hleaf : leafProbe = some (index, target))
    (hrevealed : revealed index = some target) (hmatches : isMatch = true)
    (hcached : cached = some output) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe ordinary (fun probe =>
        filteredTreeLeafPlan probe.1 (revealed probe.1) probe.2 isMatch cached)) =
      FilteredTreeHashProgram.leafCached := by
  subst chainProbe
  subst leafProbe
  subst isMatch
  subst cached
  simp [filteredTreeOuterPlan, filteredTreeNoChainPlan, filteredTreeLeafPlan,
    hrevealed]

theorem filteredTreeOuterPlan_eq_leafFresh_of_not_matches
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (revealed : ChainValueIndex → Option Digest) (isMatch : Bool)
    (cached : Option HashOutput) (index : ChainValueIndex) (target : Digest)
    (hchain : chainProbe = none)
    (hleaf : leafProbe = some (index, target))
    (hrevealed : revealed index = some target) (hmatches : isMatch = false) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe ordinary (fun probe =>
        filteredTreeLeafPlan probe.1 (revealed probe.1) probe.2 isMatch cached)) =
      FilteredTreeHashProgram.fresh := by
  subst chainProbe
  subst leafProbe
  subst isMatch
  simp [filteredTreeOuterPlan, filteredTreeNoChainPlan, filteredTreeLeafPlan,
    hrevealed]

theorem filteredTreeOuterPlan_eq_leafFresh_of_cache_none
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (revealed : ChainValueIndex → Option Digest) (isMatch : Bool)
    (cached : Option HashOutput) (index : ChainValueIndex) (target : Digest)
    (hchain : chainProbe = none)
    (hleaf : leafProbe = some (index, target))
    (hrevealed : revealed index = some target) (hmatches : isMatch = true)
    (hcached : cached = none) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe ordinary (fun probe =>
        filteredTreeLeafPlan probe.1 (revealed probe.1) probe.2 isMatch cached)) =
      FilteredTreeHashProgram.fresh := by
  subst chainProbe
  subst leafProbe
  subst isMatch
  subst cached
  simp [filteredTreeOuterPlan, filteredTreeNoChainPlan, filteredTreeLeafPlan,
    hrevealed]

theorem filteredTreeOuterPlan_eq_leafFresh_of_mismatch
    (chainProbe leafProbe : Option (ChainValueIndex × Digest))
    (ordinary : FilteredTreeHashProgram)
    (revealed : ChainValueIndex → Option Digest) (isMatch : Bool)
    (cached : Option HashOutput) (index : ChainValueIndex) (target value : Digest)
    (hchain : chainProbe = none)
    (hleaf : leafProbe = some (index, target))
    (hrevealed : revealed index = some value) (hmismatch : value ≠ target) :
    filteredTreeOuterPlan chainProbe
      (filteredTreeNoChainPlan leafProbe ordinary (fun probe =>
        filteredTreeLeafPlan probe.1 (revealed probe.1) probe.2 isMatch cached)) =
      FilteredTreeHashProgram.fresh := by
  subst chainProbe
  subst leafProbe
  simp [filteredTreeOuterPlan, filteredTreeNoChainPlan, filteredTreeLeafPlan,
    hrevealed, hmismatch]

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : ChainValueIndex × Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some probe) :
    FilteredTreePlanIs (FilteredTreeHashProgram.chain probe) high secretKey selected
      input state := by
  constructor
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_chain _ _ probe hprobe

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_cached
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (hcached : state.cache input = some output) :
    FilteredTreePlanIs FilteredTreeHashProgram.currentCached high secretKey
      selected input state := by
  constructor
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeOrdinaryHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_currentCached _ _ _ output _ _ _ hchain
    hleaf hcached

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_retained
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (hcurrent : state.cache input = none)
    (hretained : TreeRetainedHashInput secretKey.parameter selected input)
    (hkeygen : state.keygenCache input = some output) :
    FilteredTreePlanIs FilteredTreeHashProgram.keygenCached high secretKey
      selected input state := by
  constructor
  have hretainedBool :
      decide (TreeRetainedHashInput secretKey.parameter selected input) = true := by
    simp [hretained]
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeOrdinaryHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_keygenCached _ _ _ _ _ output _ hchain hleaf
    hcurrent hretainedBool hkeygen

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (hcurrent : state.cache input = none)
    (hfresh : ¬ TreeRetainedHashInput secretKey.parameter selected input ∨
      state.keygenCache input = none) :
    FilteredTreePlanIs FilteredTreeHashProgram.fresh high secretKey selected
      input state := by
  constructor
  rcases hfresh with hnotRetained | hkeygen
  · have hretainedBool :
        decide (TreeRetainedHashInput secretKey.parameter selected input) =
          false := by
      simp [hnotRetained]
    unfold filteredTreeProbingAttackerHashQueryAtFromHigh
      filteredTreeNoChainHashQueryAtFromHigh
      filteredTreeOrdinaryHashQueryAtFromHigh
    exact filteredTreeOuterPlan_eq_fresh_of_not_retained _ _ _ _ _ _ hchain
      hleaf hcurrent hretainedBool
  · by_cases hretained : TreeRetainedHashInput secretKey.parameter selected input
    · have hretainedBool :
          decide (TreeRetainedHashInput secretKey.parameter selected input) =
            true := by
        simp [hretained]
      unfold filteredTreeProbingAttackerHashQueryAtFromHigh
        filteredTreeNoChainHashQueryAtFromHigh
        filteredTreeOrdinaryHashQueryAtFromHigh
      exact filteredTreeOuterPlan_eq_fresh_of_keygen_none _ _ _ _ _ _ hchain
        hleaf hcurrent hretainedBool hkeygen
    · have hretainedBool :
          decide (TreeRetainedHashInput secretKey.parameter selected input) =
            false := by
        simp [hretained]
      unfold filteredTreeProbingAttackerHashQueryAtFromHigh
        filteredTreeNoChainHashQueryAtFromHigh
        filteredTreeOrdinaryHashQueryAtFromHigh
      exact filteredTreeOuterPlan_eq_fresh_of_not_retained _ _ _ _ _ _ hchain
        hleaf hcurrent hretainedBool


theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_hidden
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hhidden : state.revealed index = none) :
    FilteredTreePlanIs (FilteredTreeHashProgram.leafProbe (index, target)) high
      secretKey selected
      input state := by
  constructor
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeLeafHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_leafProbe _ _ _ _ _ _ index target hchain
    hleaf hhidden

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_cached
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (output : HashOutput)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hrevealed : state.revealed index = some target)
    (hmatch : LeafInputMatchesOutside secretKey state.keygenCache selected input)
    (hcached : state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) = some output) :
    FilteredTreePlanIs FilteredTreeHashProgram.leafCached high secretKey selected
      input state := by
  constructor
  have hmatchBool : decide (LeafInputMatchesOutside secretKey state.keygenCache
      selected input) = true := by
    simp [hmatch]
  have hcachedLeaf : filteredTreeKeygenLeafOutput secretKey input state =
      some output := by
    unfold filteredTreeKeygenLeafOutput
    exact hcached
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeLeafHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_leafCached _ _ _ _ _ _ index target output
    hchain hleaf hrevealed hmatchBool hcachedLeaf

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_not_match
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hrevealed : state.revealed index = some target)
    (hmatch : ¬ LeafInputMatchesOutside secretKey state.keygenCache selected
      input) :
    FilteredTreePlanIs FilteredTreeHashProgram.fresh high secretKey selected
      input state := by
  constructor
  have hmatchBool : decide (LeafInputMatchesOutside secretKey state.keygenCache
      selected input) = false := by
    simp [hmatch]
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeLeafHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_leafFresh_of_not_matches _ _ _ _ _ _ index
    target hchain hleaf hrevealed hmatchBool

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_cache_none
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hrevealed : state.revealed index = some target)
    (hmatch : LeafInputMatchesOutside secretKey state.keygenCache selected input)
    (hcached : state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) = none) :
    FilteredTreePlanIs FilteredTreeHashProgram.fresh high secretKey selected
      input state := by
  constructor
  have hmatchBool : decide (LeafInputMatchesOutside secretKey state.keygenCache
      selected input) = true := by
    simp [hmatch]
  have hcachedLeaf : filteredTreeKeygenLeafOutput secretKey input state = none := by
    unfold filteredTreeKeygenLeafOutput
    exact hcached
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeLeafHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_leafFresh_of_cache_none _ _ _ _ _ _ index
    target hchain hleaf hrevealed hmatchBool hcachedLeaf

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_mismatch
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target value : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hrevealed : state.revealed index = some value)
    (hmismatch : value ≠ target) :
    FilteredTreePlanIs FilteredTreeHashProgram.fresh high secretKey selected
      input state := by
  constructor
  unfold filteredTreeProbingAttackerHashQueryAtFromHigh
    filteredTreeNoChainHashQueryAtFromHigh
    filteredTreeLeafHashQueryAtFromHigh
  exact filteredTreeOuterPlan_eq_leafFresh_of_mismatch _ _ _ _ _ _ index target
    value hchain hleaf hrevealed hmismatch

set_option maxHeartbeats 200000

theorem filteredTreeHashComputationAtFromHigh_eq_chain
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : ChainValueIndex × Digest)
    (hplan : FilteredTreePlanIs (FilteredTreeHashProgram.chain probe) high
      secretKey selected input state) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreeChainHashComputation high secretKey selected input state
        probe := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rfl

theorem filteredTreeHashComputationAtFromHigh_eq_leafProbe
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hplan : FilteredTreePlanIs
      (FilteredTreeHashProgram.leafProbe (index, target)) high secretKey selected
        input state) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreeProbeThenFreshHashComputation input state index target := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rfl

theorem filteredTreeHashComputationAtFromHigh_eq_currentCached
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hplan : FilteredTreePlanIs FilteredTreeHashProgram.currentCached high
      secretKey selected input state)
    (hcached : state.cache input = some output) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreePureHashComputation output state := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rw [hcached]


theorem filteredTreeHashComputationAtFromHigh_eq_keygenCached
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hplan : FilteredTreePlanIs FilteredTreeHashProgram.keygenCached high
      secretKey selected input state)
    (hcached : state.keygenCache input = some output) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreePureHashComputation output state := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rw [hcached]


theorem filteredTreeHashComputationAtFromHigh_eq_leafCached
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hplan : FilteredTreePlanIs FilteredTreeHashProgram.leafCached high
      secretKey selected input state)
    (hcached : filteredTreeKeygenLeafOutput secretKey input state =
      some output) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreePureHashComputation output state := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rw [hcached]


theorem filteredTreeHashComputationAtFromHigh_eq_fresh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hplan : FilteredTreePlanIs FilteredTreeHashProgram.fresh high secretKey
      selected input state) :
    filteredTreeHashComputationAtFromHigh high secretKey selected input state =
      filteredTreeFreshHashComputation input state := by
  unfold filteredTreeHashComputationAtFromHigh
  rw [hplan.eq]
  unfold FilteredTreeHashProgram.computation
  rfl



set_option maxHeartbeats 200000
set_option maxRecDepth 1000000

theorem Concrete.keygen_cache_none_at_selected_chainAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (selected : ChainIndex) (input : HashInput)
    (epoch : Epoch) (step : ChainStep)
    (haddress : AtHashAddress keyResult.1.2.parameter
      (.chain epoch selected step) input)
    (hprobe : chainInputProbe? keyResult.1.2.parameter selected input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem epoch selected step
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq : input = Concrete.CacheView.chainInput
          keyResult.1.2.parameter epoch selected step
            (Wots.walk
              (Concrete.CacheView.chainStep keyResult.2
                keyResult.1.2.parameter epoch selected)
              0 step.val (keyResult.1.2.chainStart epoch selected)) :=
        Concrete.keygen_cache_unique_chainAddress keyResult hmem epoch selected
          step input _ output honestOutput haddress (by
            simp [Concrete.CacheView.chainInput]) hcached hhonest
      rw [heq, chainInputProbe?_chainInput] at hprobe
      contradiction

theorem Concrete.keygen_cache_none_at_leafAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (selected : ChainIndex) (input : HashInput) (epoch : Epoch)
    (haddress : AtHashAddress keyResult.1.2.parameter (.leaf epoch) input)
    (hprobe : leafInputProbe? keyResult.1.2.parameter selected input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_leafInput keyResult hmem epoch
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq : input = Concrete.CacheView.leafInput
          keyResult.1.2.parameter epoch
            (Concrete.CacheReplay.oneTimePublicKey keyResult.2
              keyResult.1.2.parameter keyResult.1.2.chainStart epoch) :=
        Concrete.keygen_cache_unique_leafAddress keyResult hmem epoch input _
          output honestOutput haddress (by
            simp [Concrete.CacheView.leafInput]) hcached hhonest
      rw [heq, leafInputProbe?_leafInput] at hprobe
      contradiction

theorem Concrete.keygen_cache_none_of_no_tree_probe_not_outside
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (selected : ChainIndex) (input : HashInput)
    (hchain : chainInputProbe? keyResult.1.2.parameter selected input = none)
    (hleaf : leafInputProbe? keyResult.1.2.parameter selected input = none)
    (hmerkle : ¬ MerkleHashInput keyResult.1.2.parameter input)
    (houtside : ¬ OutsideChainHashInput keyResult.1.2.parameter selected input) :
    keyResult.2 input = none := by
  by_cases haddressed : KeygenAddressedHashInput
      keyResult.1.2.parameter input
  · obtain ⟨domain, hdomain⟩ := haddressed
    cases domain with
    | chain epoch candidate step =>
        by_cases hselected : candidate = selected
        · subst candidate
          exact Concrete.keygen_cache_none_at_selected_chainAddress_of_probe_none
            keyResult hmem selected input epoch step hdomain hchain
        · exact (houtside ⟨epoch, candidate, step, hselected, hdomain⟩).elim
    | leaf epoch =>
        exact Concrete.keygen_cache_none_at_leafAddress_of_probe_none keyResult
          hmem selected input epoch hdomain hleaf
    | merkle level node =>
        exact (hmerkle ⟨level, node, hdomain⟩).elim
    | encoding epoch =>
        exact Concrete.keygen_cache_none_at_encodingAddress keyResult hmem
          epoch input hdomain
  · exact Concrete.keygen_cache_none_unaddressed keyResult hmem input
      haddressed

theorem causalRecordedState_eq_of_chainProbe_none
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hprobe : chainInputProbe? secretKey.parameter selected input = none) :
    causalRecordedState secretKey selected input state = state := by
  rw [causalRecordedState, hprobe]
  rfl

theorem FilteredCausalStateRelation.leftCache_eq_of_rightCache_some
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (input : HashInput) (output : HashOutput)
    (hright : rightState.cache input = some output) :
    leftCache input = some output := by
  rcases hstate.2.1 input with hagree | ⟨_hbase, hnone⟩
  · rw [hagree]
    exact hright
  · rw [hnone] at hright
    contradiction

theorem relTriple_randomOracle_filteredTreeCurrentCached
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (output : HashOutput)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (hright : rightState.cache input = some output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          rightState)).run)
      (FilteredHashResultRelation parameter selected leftBase rightBase table) := by
  have hleft := FilteredCausalStateRelation.leftCache_eq_of_rightCache_some
    parameter selected leftBase rightBase table leftCache rightState hstate input
      output hright
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    filteredTreeHashComputationAtFromHigh_eq_currentCached _ _ _ _ _ _
      (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_cached
        high secretKey selected input rightState output hchain hleaf hright)
      hright,
    filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure]
  exact relTriple_pure_pure ⟨rfl, hstate⟩

theorem relTriple_randomOracle_causalHashQuery_of_leftBase_none
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (hbaseNone : leftBase input = none)
    (hprobe : chainInputProbe? secretKey.parameter selected input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalHashQuery input).run rightState)).run)
      (FilteredHashResultRelation parameter selected leftBase rightBase table) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (SigningComparableHashInput parameter selected) leftBase leftCache
      rightState.cache input hcurrent hstate.1 hstate.2.1
  rw [simulate_eagerTrace_causalHashQuery table input rightState]
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1,
      { causalRecordedState secretKey selected input rightState with
        cache := result.2 }),
      ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult => FilteredHashResultRelation parameter
        selected leftBase rightBase table leftResult (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    simpa only [wrap, causalRecordedState_eq_original] using
      filteredHashResultRelation_of_randomOracleRelation parameter selected
        leftBase rightBase table secretKey input leftCache rightState hstate
          leftResult rightResult hresult []
  have hmapped := relTriple_map
    (R := FilteredHashResultRelation parameter selected leftBase rightBase table)
    (f := id) (g := wrap) hprepared
  simpa [wrap, causalRecordedState_eq_of_chainProbe_none secretKey selected
    input rightState hprobe] using hmapped

theorem relTriple_randomOracle_mappedCausalState_of_leftBase_none
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (hbaseNone : leftBase input = none)
    (hprobe : chainInputProbe? secretKey.parameter selected input = none)
    (trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, { rightState with cache := result.2 }), trace)) <$>
          ((randomOracle input).run rightState.cache))
      (FilteredHashResultRelation parameter selected leftBase rightBase table) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (SigningComparableHashInput parameter selected) leftBase leftCache
      rightState.cache input hcurrent hstate.1 hstate.2.1
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1,
      { causalRecordedState secretKey selected input rightState with
        cache := result.2 }), trace)
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult => FilteredHashResultRelation parameter
        selected leftBase rightBase table leftResult (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    simpa only [wrap, causalRecordedState_eq_original] using
      filteredHashResultRelation_of_randomOracleRelation parameter selected
        leftBase rightBase table secretKey input leftCache rightState hstate
          leftResult rightResult hresult trace
  have hmapped := relTriple_map
    (R := FilteredHashResultRelation parameter selected leftBase rightBase table)
    (f := id) (g := wrap) hprepared
  simpa [wrap, causalRecordedState_eq_of_chainProbe_none secretKey selected
    input rightState hprobe] using hmapped

set_option maxRecDepth 1000000 in
theorem relTriple_programmed_filteredTreeOrdinaryQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput)
    (hchain : chainInputProbe? left.secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? left.secretKey.parameter selected input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
            input rightState)).run)
      (FilteredHashResultRelation left.secretKey.parameter selected left.cache
        right.1.1.cache right.1.2) := by
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
      input = none := by
    rw [hparameter]
    exact hchain
  have hleafRight : leafInputProbe? right.1.1.secretKey.parameter selected
      input = none := by
    rw [hparameter]
    exact hleaf
  cases hrightCurrent : rightState.cache input with
  | some output =>
      exact relTriple_randomOracle_filteredTreeCurrentCached
        left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey input leftCache
            rightState hstate output hchainRight hleafRight hrightCurrent
  | none =>
      by_cases hretained : TreeRetainedHashInput left.secretKey.parameter
          selected input
      · have hretainedRight : TreeRetainedHashInput
            right.1.1.secretKey.parameter selected input := by
          simpa [hparameter] using hretained
        cases hrightBase : right.1.1.cache input with
        | some output =>
            have hleftBase : left.cache input = some output := by
              rw [hrel.retained input hretained]
              exact hrightBase
            have hleftCurrent : leftCache input = some output :=
              hstate.2.2.1 hleftBase
            have hrightKeygen : rightState.keygenCache input = some output := by
              rw [hstate.2.2.2.1]
              exact hrightBase
            rw [randomOracle, QueryImpl.withCaching_run_some _ hleftCurrent,
              filteredTreeHashComputationAtFromHigh_eq_keygenCached _ _ _ _ _ _
                (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_retained
                  (chainValueHighTableOfEdges right.2) right.1.1.secretKey
                    selected input rightState output hchainRight hleafRight
                      hrightCurrent hretainedRight hrightKeygen)
                hrightKeygen,
              filteredTreePureHashComputation, simulateQ_pure,
              WriterT.run_pure]
            exact relTriple_pure_pure ⟨rfl, hstate⟩
        | none =>
            have hleftBase : left.cache input = none := by
              rw [hrel.retained input hretained]
              exact hrightBase
            have hrightKeygen : rightState.keygenCache input = none := by
              rw [hstate.2.2.2.1]
              exact hrightBase
            rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
              (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
                (chainValueHighTableOfEdges right.2) right.1.1.secretKey
                  selected input rightState hchainRight hleafRight hrightCurrent
                    (Or.inr hrightKeygen)), filteredTreeFreshHashComputation]
            exact relTriple_randomOracle_causalHashQuery_of_leftBase_none
              left.secretKey.parameter selected left.cache right.1.1.cache
                right.1.2 right.1.1.secretKey input leftCache rightState hstate
                  hleftBase hchainRight
      · have hnotOutside : ¬ OutsideChainHashInput left.secretKey.parameter
            selected input := fun houtside => hretained (Or.inl houtside)
        have hnotMerkle : ¬ MerkleHashInput left.secretKey.parameter input :=
          fun hmerkle => hretained (Or.inr hmerkle)
        have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
          selected left hleftSupport
        have hleftBase :=
          Concrete.keygen_cache_none_of_no_tree_probe_not_outside
            left.keyResult hleftKey selected input hchain hleaf hnotMerkle
              hnotOutside
        have hnotOutsideRight : ¬ OutsideChainHashInput
            right.1.1.secretKey.parameter selected input := by
          simpa [hparameter] using hnotOutside
        have hnotMerkleRight : ¬ MerkleHashInput
            right.1.1.secretKey.parameter input := by
          simpa [hparameter] using hnotMerkle
        have hrightKey := actualFixedChainKeygen_support_keyResult selected
          right.1.1 hrightSupport
        have hrightBase :=
          Concrete.keygen_cache_none_of_no_tree_probe_not_outside
            right.1.1.keyResult hrightKey selected input hchainRight hleafRight
              hnotMerkleRight hnotOutsideRight
        have hrightKeygen : rightState.keygenCache input = none := by
          rw [hstate.2.2.2.1]
          exact hrightBase
        have hnotRetainedRight : ¬ TreeRetainedHashInput
            right.1.1.secretKey.parameter selected input := by
          simpa [hparameter] using hretained
        rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
              rightState hchainRight hleafRight hrightCurrent
                (Or.inl hnotRetainedRight)), filteredTreeFreshHashComputation]
        exact relTriple_randomOracle_causalHashQuery_of_leftBase_none
          left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
            right.1.1.secretKey input leftCache rightState hstate hleftBase
              hchainRight


theorem simulate_eagerTrace_filteredTreeOrdinaryQuery_support_trace
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input = none)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    result.2 = [] ∧ result.1.2.revealed = state.revealed := by
  cases hcurrent : state.cache input with
  | some output =>
      rw [filteredTreeHashComputationAtFromHigh_eq_currentCached _ _ _ _ _ _
        (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_cached
          high secretKey selected input state output hchain hleaf hcurrent)
        hcurrent, filteredTreePureHashComputation] at hresult
      simp only [simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨rfl, rfl⟩
  | none =>
      by_cases hretained : TreeRetainedHashInput secretKey.parameter selected
          input
      · cases hkeygen : state.keygenCache input with
        | some output =>
            rw [filteredTreeHashComputationAtFromHigh_eq_keygenCached _ _ _ _ _ _
              (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_retained
                high secretKey selected input state output hchain hleaf hcurrent
                  hretained hkeygen)
              hkeygen, filteredTreePureHashComputation] at hresult
            simp only [simulateQ_pure, WriterT.run_pure, support_pure,
              Set.mem_singleton_iff] at hresult
            subst result
            exact ⟨rfl, rfl⟩
        | none =>
            rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
              (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
                high secretKey selected input state hchain hleaf hcurrent
                  (Or.inr hkeygen)), filteredTreeFreshHashComputation,
              simulate_eagerTrace_causalHashQuery,
              support_map] at hresult
            obtain ⟨raw, _hraw, rfl⟩ := hresult
            exact ⟨rfl, rfl⟩
      · rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_no_probes_fresh
            high secretKey selected input state hchain hleaf hcurrent
              (Or.inl hretained)), filteredTreeFreshHashComputation,
          simulate_eagerTrace_causalHashQuery,
          support_map] at hresult
        obtain ⟨raw, _hraw, rfl⟩ := hresult
        exact ⟨rfl, rfl⟩


set_option maxRecDepth 1000000 in
theorem relTriple_programmed_monitoredTreeOrdinaryQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput)
    (hchain : chainInputProbe? left.secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? left.secretKey.parameter selected input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((monitorCausalTrace right.1.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (filteredTreeHashComputationAtFromHigh
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
              input causalState)).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  apply relTriple_monitorCausalTrace_of_filtered_until_hit (α := HashOutput)
    left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
      ((randomOracle input).run leftCache) _ rightState monitor hmonitor
        hmonitorAgrees hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_filteredTreeOrdinaryQuery selected left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausal input
          hchain hleaf)
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    have hparameter := hrel.parameter_eq selected left right hleftSupport
      hrightSupport
    have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
        input = none := by
      rw [hparameter]
      exact hchain
    have hleafRight : leafInputProbe? right.1.1.secretKey.parameter selected
        input = none := by
      rw [hparameter]
      exact hleaf
    obtain ⟨htrace, hfinal⟩ :=
      simulate_eagerTrace_filteredTreeOrdinaryQuery_support_trace right.1.2
        (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
          rightState.causal hchainRight hleafRight result hresult
    rw [htrace]
    constructor
    · trivial
    · rw [hfinal]
      exact ReplaysCausalReveals.nil rightState.causal.revealed

theorem programmedActualTree_leaf_endpoints_eq_replay_of_match_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (index : ChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.leafInput left.secretKey.parameter epoch
      endpoints)
    (hindex : index = (epoch, chainEndpointDigit))
    (htarget : target = endpoints selected)
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target) :
    endpoints = Concrete.CacheReplay.oneTimePublicKey left.cache
      left.secretKey.parameter left.secretKey.chainStart epoch := by
  obtain ⟨matchEpoch, matchEndpoints, hmatchInput, houtside⟩ := hmatch
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hleafEq :
      Concrete.CacheView.leafInput left.secretKey.parameter epoch endpoints =
        Concrete.CacheView.leafInput left.secretKey.parameter matchEpoch
          matchEndpoints := by
    calc
      _ = input := hinput.symm
      _ = Concrete.CacheView.leafInput right.1.1.secretKey.parameter
          matchEpoch matchEndpoints := hmatchInput
      _ = _ := by rw [hparameter]
  obtain ⟨hepoch, hendpoints⟩ :=
    (Concrete.CacheView.leafInput_eq_iff left.secretKey.parameter epoch
      matchEpoch endpoints matchEndpoints).mp hleafEq
  subst matchEpoch
  subst matchEndpoints
  have htableTarget : left.table (epoch, chainEndpointDigit) = target := by
    rw [hrel.base.base.1.1, ← hindex]
    exact hhit
  funext candidate
  by_cases hselected : candidate = selected
  · subst candidate
    rw [← htarget, ← htableTarget]
    exact (programmedKeygen_selectedEndpoint_eq_table selected left
      hleftSupport epoch).symm
  · calc
      endpoints candidate =
          Concrete.CacheReplay.oneTimePublicKey right.1.1.cache
            right.1.1.secretKey.parameter right.1.1.secretKey.chainStart
              epoch candidate := houtside candidate hselected
      _ = Concrete.CacheReplay.oneTimePublicKey left.cache
            left.secretKey.parameter left.secretKey.chainStart epoch
              candidate :=
        (hrel.replay_other_eq selected candidate hselected left right
          hleftSupport hrightSupport epoch).symm

theorem Concrete.keygen_cache_has_leafInput_of_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (input : HashInput)
    (hinput : input = Concrete.CacheView.leafInput
      keyResult.1.2.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey keyResult.2
          keyResult.1.2.parameter keyResult.1.2.chainStart epoch)) :
    ∃ output, keyResult.2 input = some output := by
  obtain ⟨output, hcached⟩ :=
    Concrete.keygen_cache_has_leafInput keyResult hmem epoch
  exact ⟨output, hinput ▸ hcached⟩

theorem Concrete.keygen_cache_has_leafInput_of_endpoints_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (input : HashInput) (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput
      keyResult.1.2.parameter epoch endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey keyResult.2
      keyResult.1.2.parameter keyResult.1.2.chainStart epoch) :
    ∃ output, keyResult.2 input = some output := by
  apply Concrete.keygen_cache_has_leafInput_of_eq keyResult hmem epoch input
  exact hinput.trans (congrArg
    (Concrete.CacheView.leafInput keyResult.1.2.parameter epoch) hendpoints)

theorem programmedKeygen_cache_has_leafInput_of_endpoints_eq
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen selected))
    (epoch : Epoch) (input : HashInput) (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput view.secretKey.parameter epoch
      endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey view.cache
      view.secretKey.parameter view.secretKey.chainStart epoch) :
    ∃ output, view.cache input = some output := by
  have hkey := programmedWarmedFixedChainKeygen_support_keyResult selected view
    hview
  simpa [ProgrammedFixedChainKeygenView.keyResult] using
    (Concrete.keygen_cache_has_leafInput_of_endpoints_eq view.keyResult hkey
      epoch input endpoints hinput hendpoints)

theorem programmedKeygen_cache_has_leafInput_of_eq
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen selected))
    (epoch : Epoch) (input : HashInput)
    (hinput : input = Concrete.CacheView.leafInput view.secretKey.parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey view.cache view.secretKey.parameter
        view.secretKey.chainStart epoch)) :
    ∃ output, view.cache input = some output := by
  have hkey := programmedWarmedFixedChainKeygen_support_keyResult selected view
    hview
  simpa [ProgrammedFixedChainKeygenView.keyResult] using
    (Concrete.keygen_cache_has_leafInput_of_eq view.keyResult hkey epoch input
      hinput)

theorem programmedActualTree_leaf_input_eq_replay_of_match_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target) :
    ∃ epoch, input = Concrete.CacheView.leafInput left.secretKey.parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey left.cache
        left.secretKey.parameter left.secretKey.chainStart epoch) := by
  obtain ⟨epoch, endpoints, hinput, hindex, htarget⟩ :=
    leafInputProbe?_eq_some left.secretKey.parameter selected input index
      target hprobe
  have hendpoints :=
    programmedActualTree_leaf_endpoints_eq_replay_of_match_hit selected left
      right hrel hleftSupport hrightSupport input epoch endpoints index target
        hinput hindex htarget hmatch hhit
  exact ⟨epoch, hinput.trans (congrArg
    (Concrete.CacheView.leafInput left.secretKey.parameter epoch) hendpoints)⟩

theorem keygenLeafTargetInput_eq_replay_of_leaf_eq
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) (input : HashInput)
    (hinput : input = Concrete.CacheView.leafInput secretKey.parameter epoch
      endpoints) :
    keygenLeafTargetInput secretKey cache input =
      replayLeafInput cache secretKey.parameter secretKey.chainStart epoch := by
  rw [hinput]
  simp [replayLeafInput, keygenLeafTargetInput_leafInput]

theorem leafInput_eq_replay_of_parameter_endpoints
    (leftSecret rightSecret : SecretKey) (leftCache : QueryCache HashSpec)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) (input : HashInput)
    (hparameter : rightSecret.parameter = leftSecret.parameter)
    (hinput : input = Concrete.CacheView.leafInput rightSecret.parameter epoch
      endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey leftCache
      leftSecret.parameter leftSecret.chainStart epoch) :
    input = replayLeafInput leftCache leftSecret.parameter
      leftSecret.chainStart epoch := by
  calc
    _ = Concrete.CacheView.leafInput rightSecret.parameter epoch endpoints :=
      hinput
    _ = Concrete.CacheView.leafInput leftSecret.parameter epoch endpoints := by
      rw [hparameter]
    _ = _ := by
      unfold replayLeafInput
      exact congrArg (Concrete.CacheView.leafInput leftSecret.parameter epoch)
        hendpoints

theorem leaf_target_cache_eq_left_of_replay
    (leftSecret rightSecret : SecretKey)
    (leftCache rightCache : QueryCache HashSpec)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) (input : HashInput)
    (hparameter : rightSecret.parameter = leftSecret.parameter)
    (hinputRight : input = Concrete.CacheView.leafInput
      rightSecret.parameter epoch endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey leftCache
      leftSecret.parameter leftSecret.chainStart epoch)
    (hreplay : LeafReplayCorrespondence leftSecret.parameter
      leftSecret.chainStart rightSecret.chainStart leftCache rightCache) :
    LeafReplayCacheEq leftCache rightCache
      (keygenLeafTargetInput rightSecret rightCache input) input := by
  have hrightTargetRight := keygenLeafTargetInput_eq_replay_of_leaf_eq
    rightSecret rightCache epoch endpoints input hinputRight
  have hrightTarget : keygenLeafTargetInput rightSecret rightCache input =
      replayLeafInput rightCache leftSecret.parameter rightSecret.chainStart
        epoch := by
    simpa [hparameter] using hrightTargetRight
  have hleftInput := leafInput_eq_replay_of_parameter_endpoints leftSecret
    rightSecret leftCache epoch endpoints input hparameter hinputRight hendpoints
  exact hreplay.transport epoch
    (keygenLeafTargetInput rightSecret rightCache input) input hrightTarget
      hleftInput

theorem programmedActualTree_leaf_target_cache_eq_left_of_match_hit_decoded
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (index : ChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.leafInput left.secretKey.parameter epoch
      endpoints)
    (hindex : index = (epoch, chainEndpointDigit))
    (htarget : target = endpoints selected)
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target) :
    LeafReplayCacheEq left.cache right.1.1.cache
      (keygenLeafTargetInput right.1.1.secretKey right.1.1.cache input) input := by
  have hendpoints :=
    programmedActualTree_leaf_endpoints_eq_replay_of_match_hit selected left
      right hrel hleftSupport hrightSupport input epoch endpoints index target
        hinput hindex htarget hmatch hhit
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hinputRight : input = Concrete.CacheView.leafInput
      right.1.1.secretKey.parameter epoch endpoints := by
    simpa [hparameter] using hinput
  exact leaf_target_cache_eq_left_of_replay left.secretKey
    right.1.1.secretKey left.cache right.1.1.cache epoch endpoints input
      hparameter hinputRight hendpoints hrel.replayLeaves

theorem programmedActualTree_leaf_target_cache_eq_left_of_match_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target) :
    LeafReplayCacheEq left.cache right.1.1.cache
      (keygenLeafTargetInput right.1.1.secretKey right.1.1.cache input) input := by
  obtain ⟨epoch, endpoints, hinput, hindex, htarget⟩ :=
    leafInputProbe?_eq_some left.secretKey.parameter selected input index
      target hprobe
  exact programmedActualTree_leaf_target_cache_eq_left_of_match_hit_decoded
    selected left right hrel hleftSupport hrightSupport input epoch endpoints
      index target hinput hindex htarget hmatch hhit

theorem programmedKeygen_leaf_cache_pair_of_input_eq
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen selected))
    (epoch : Epoch) (input : HashInput)
    (hinput : input = Concrete.CacheView.leafInput view.secretKey.parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey view.cache view.secretKey.parameter
        view.secretKey.chainStart epoch))
    (rightCache : QueryCache HashSpec) (rightInput : HashInput)
    (heq : LeafReplayCacheEq view.cache rightCache rightInput input) :
    ∃ output, LeafCachePair output view.cache rightCache input rightInput := by
  obtain ⟨output, hleft⟩ :=
    programmedKeygen_cache_has_leafInput_of_eq selected view hview epoch input
      hinput
  exact ⟨output, ⟨hleft, heq.eq.trans hleft⟩⟩

theorem programmedActualTree_leaf_cached_of_match_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target) :
    ∃ output, LeafCachePair output left.cache right.1.1.cache input
      (keygenLeafTargetInput right.1.1.secretKey right.1.1.cache input) := by
  have hform := programmedActualTree_leaf_input_eq_replay_of_match_hit selected
    left right hrel hleftSupport hrightSupport input index target hprobe hmatch
      hhit
  let epoch := Classical.choose hform
  have hinput := Classical.choose_spec hform
  apply programmedKeygen_leaf_cache_pair_of_input_eq selected left hleftSupport
    epoch input hinput right.1.1.cache
      (keygenLeafTargetInput right.1.1.secretKey right.1.1.cache input)
  exact programmedActualTree_leaf_target_cache_eq_left_of_match_hit selected left
    right hrel hleftSupport hrightSupport input index target hprobe hmatch hhit


set_option maxRecDepth 10000000 in
theorem relTriple_programmed_filteredTreeLeafQuery_of_match_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input)
    (hhit : right.1.2 index = target)
    (hrevealed : rightState.revealed index = some target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
            input rightState)).run)
      (FilteredHashResultRelation left.secretKey.parameter selected left.cache
        right.1.1.cache right.1.2) := by
  obtain ⟨output, ⟨hleftBaseCached, hrightBaseCached⟩⟩ :=
    programmedActualTree_leaf_cached_of_match_hit selected left right hrel
      hleftSupport hrightSupport input index target hprobe hmatch hhit
  have hleftCached : leftCache input = some output :=
    hstate.2.2.1 hleftBaseCached
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  obtain ⟨epoch, endpoints, hinput, _hindex, _htarget⟩ :=
    leafInputProbe?_eq_some left.secretKey.parameter selected input index
      target hprobe
  have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
      input = none := by
    rw [hparameter, hinput]
    exact chainInputProbe?_leafInput left.secretKey.parameter selected epoch
      endpoints
  have hleafRight : leafInputProbe? right.1.1.secretKey.parameter selected
      input = some (index, target) := by
    rw [hparameter]
    exact hprobe
  have hkeygenCache : rightState.keygenCache = right.1.1.cache :=
    hstate.2.2.2.1
  have hmatchState : LeafInputMatchesOutside right.1.1.secretKey
      rightState.keygenCache selected input := by
    rwa [hkeygenCache]
  have hrightCached : rightState.keygenCache
      (keygenLeafTargetInput right.1.1.secretKey rightState.keygenCache input) =
        some output := by
    rw [hkeygenCache]
    exact hrightBaseCached
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleftCached]
  rw [filteredTreeHashComputationAtFromHigh_eq_leafCached _ _ _ _ _ _
    (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_cached
      (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
        rightState index target output hchainRight hleafRight hrevealed hmatchState
          hrightCached)
    (by simpa [filteredTreeKeygenLeafOutput] using hrightCached),
    filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure]
  exact relTriple_pure_pure ⟨rfl, hstate⟩


theorem programmedActualTree_leaf_cache_none_of_not_match_or_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hfailure :
      ¬ LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
          selected input ∨
        right.1.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨epoch, endpoints, hinput, hindex, htarget⟩ :=
    leafInputProbe?_eq_some left.secretKey.parameter selected input index
      target hprobe
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  rw [hinput]
  apply Concrete.keygen_cache_leafInput_eq_none_of_ne left.keyResult hleftKey
    epoch endpoints
  intro hendpoints
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hmatch : LeafInputMatchesOutside right.1.1.secretKey right.1.1.cache
      selected input := by
    refine ⟨epoch, endpoints, ?_, ?_⟩
    · simpa [hparameter] using hinput
    · intro candidate hcandidate
      rw [hendpoints]
      exact hrel.replay_other_eq selected candidate hcandidate left right
        hleftSupport hrightSupport epoch
  have hhit : right.1.2 index = target := by
    calc
      right.1.2 index = left.table index :=
        congrFun hrel.base.base.1.1 index |>.symm
      _ = left.table (epoch, chainEndpointDigit) :=
        congrArg left.table hindex
      _ = Concrete.CacheReplay.oneTimePublicKey left.cache
          left.secretKey.parameter left.secretKey.chainStart epoch selected :=
        (programmedKeygen_selectedEndpoint_eq_table selected left
          hleftSupport epoch).symm
      _ = endpoints selected := congrFun hendpoints.symm selected
      _ = target := htarget.symm
  rcases hfailure with hnotMatch | hmiss
  · exact (hnotMatch hmatch).elim
  · exact (hmiss hhit).elim

theorem simulate_eagerTrace_filteredTreeLeafQuery_hidden
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (hhidden : state.revealed index = none) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredTreeHashComputationAtFromHigh high secretKey selected input
        state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, { state with cache := result.2 }),
          [RevealProbeOracleSimulation.ObservedAction.probe index target])) <$>
        ((randomOracle input).run state.cache) := by
  rw [filteredTreeHashComputationAtFromHigh_eq_leafProbe _ _ _ _ _ _ _
    (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_hidden
      high secretKey selected input state index target hchain hleaf hhidden),
      filteredTreeProbeThenFreshHashComputation,
      filteredTreeFreshHashComputation,
      simulateQ_bind, WriterT.run_bind', simulate_eagerTrace_probeQuery]
  simp only [map_eq_bind_pure_comp]
  rw [simulate_eagerTrace_causalHashQuery table input state]
  rw [map_eq_bind_pure_comp]
  simp [Function.comp_def]


set_option maxRecDepth 1000000 in
theorem relTriple_programmed_filteredTreeLeafQuery_until_hit
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (hrevealed : monitor.revealed = rightState.revealed)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
            input rightState)).run)
      (FilteredHashUntilHitRelation left.secretKey.parameter selected
        left.cache right.1.1.cache right.1.2 monitor) := by
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  obtain ⟨epoch, endpoints, hinput, _hindex, _htarget⟩ :=
    leafInputProbe?_eq_some left.secretKey.parameter selected input index
      target hprobe
  have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
      input = none := by
    rw [hparameter, hinput]
    exact chainInputProbe?_leafInput left.secretKey.parameter selected epoch
      endpoints
  have hleafRight : leafInputProbe? right.1.1.secretKey.parameter selected
      input = some (index, target) := by
    rw [hparameter]
    exact hprobe
  cases hrightRevealed : rightState.revealed index with
  | none =>
      by_cases hhit : right.1.2 index = target
      · have hmonitorHidden : monitor.revealed index = none := by
          rw [hrevealed, hrightRevealed]
        have hrightBad : ∀ result ∈ support
            ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
              (filteredTreeHashComputationAtFromHigh
                (chainValueHighTableOfEdges right.2) right.1.1.secretKey
                  selected input rightState)).run),
            RevealProbeOracleSimulation.runObserved right.1.2 monitor
              result.2 = true := by
          intro result hresult
          rw [simulate_eagerTrace_filteredTreeLeafQuery_hidden right.1.2
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
              input rightState index target hchainRight hleafRight
                hrightRevealed, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact RevealProbeOracleSimulation.runObserved_probe_hit_hidden
            right.1.2 monitor index target [] hmonitorHidden hhit
        have hproduct := relTriple_prod
          (oa := (randomOracle input).run leftCache)
          (ob := (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
            (filteredTreeHashComputationAtFromHigh
              (chainValueHighTableOfEdges right.2) right.1.1.secretKey
                selected input rightState)).run)
          (P := fun _ => True)
          (Q := fun result => RevealProbeOracleSimulation.runObserved
            right.1.2 monitor result.2 = true)
          (fun _ _ => True.intro) hrightBad
        apply relTriple_post_mono hproduct
        intro _leftResult _rightResult hresult
        exact Or.inr hresult.2
      · have hbaseNone :=
          programmedActualTree_leaf_cache_none_of_not_match_or_miss
            selected left right hrel hleftSupport hrightSupport input index
              target hprobe (Or.inr hhit)
        rw [simulate_eagerTrace_filteredTreeLeafQuery_hidden right.1.2
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
            input rightState index target hchainRight hleafRight
              hrightRevealed]
        apply relTriple_post_mono
          (relTriple_randomOracle_mappedCausalState_of_leftBase_none
            left.secretKey.parameter selected left.cache right.1.1.cache
              right.1.2 right.1.1.secretKey input leftCache rightState hstate
                hbaseNone hchainRight
                  [RevealProbeOracleSimulation.ObservedAction.probe index
                    target])
        intro leftResult rightResult hresult
        exact Or.inl hresult
  | some value =>
      by_cases hvalue : value = target
      · subst value
        have hhit : right.1.2 index = target :=
          hstate.2.2.2.2 index target hrightRevealed
        by_cases hmatch : LeafInputMatchesOutside right.1.1.secretKey
            right.1.1.cache selected input
        · apply relTriple_post_mono
            (relTriple_programmed_filteredTreeLeafQuery_of_match_hit selected
              left right hrel hleftSupport hrightSupport leftCache rightState
                hstate input index target hprobe hmatch hhit hrightRevealed)
          intro leftResult rightResult hresult
          exact Or.inl hresult
        · have hbaseNone :=
            programmedActualTree_leaf_cache_none_of_not_match_or_miss
              selected left right hrel hleftSupport hrightSupport input index
                target hprobe (Or.inl hmatch)
          have hkeygenCache : rightState.keygenCache = right.1.1.cache :=
            hstate.2.2.2.1
          have hnotMatchState : ¬ LeafInputMatchesOutside
              right.1.1.secretKey rightState.keygenCache selected input := by
            simpa [hkeygenCache] using hmatch
          rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
            (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_not_match
              (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
                input rightState index target hchainRight hleafRight
                  hrightRevealed hnotMatchState),
            filteredTreeFreshHashComputation]
          apply relTriple_post_mono
            (relTriple_randomOracle_causalHashQuery_of_leftBase_none
              left.secretKey.parameter selected left.cache right.1.1.cache
                right.1.2 right.1.1.secretKey input leftCache rightState hstate
                  hbaseNone hchainRight)
          intro leftResult rightResult hresult
          exact Or.inl hresult
      · have hmiss : right.1.2 index ≠ target := by
          intro hhit
          exact hvalue ((hstate.2.2.2.2 index value hrightRevealed).symm.trans
            hhit)
        have hbaseNone :=
          programmedActualTree_leaf_cache_none_of_not_match_or_miss
            selected left right hrel hleftSupport hrightSupport input index
              target hprobe (Or.inr hmiss)
        rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_mismatch
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
              rightState index target value hchainRight hleafRight hrightRevealed
                hvalue), filteredTreeFreshHashComputation]
        apply relTriple_post_mono
          (relTriple_randomOracle_causalHashQuery_of_leftBase_none
            left.secretKey.parameter selected left.cache right.1.1.cache
              right.1.2 right.1.1.secretKey input leftCache rightState hstate
                hbaseNone hchainRight)
        intro leftResult rightResult hresult
        exact Or.inl hresult


theorem simulate_eagerTrace_filteredTreeLeafQuery_support_trace
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (target : Digest)
    (hchain : chainInputProbe? secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? secretKey.parameter selected input =
      some (index, target))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    (result.2 = [] ∨
      result.2 = [RevealProbeOracleSimulation.ObservedAction.probe index target]) ∧
      result.1.2.revealed = state.revealed := by
  cases hrevealed : state.revealed index with
  | none =>
      rw [simulate_eagerTrace_filteredTreeLeafQuery_hidden table high secretKey
        selected input state index target hchain hleaf hrevealed,
          support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      exact ⟨Or.inr rfl, rfl⟩
  | some value =>
      by_cases hvalue : value = target
      · have hrevealedTarget : state.revealed index = some target := by
          simpa [hvalue] using hrevealed
        by_cases hmatch : LeafInputMatchesOutside secretKey state.keygenCache
            selected input
        ·
          cases hcached : state.keygenCache
              (keygenLeafTargetInput secretKey state.keygenCache input) with
          | none =>
              rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
                (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_cache_none
                  high secretKey selected input state index target hchain hleaf
                    hrevealedTarget hmatch hcached),
                filteredTreeFreshHashComputation,
                simulate_eagerTrace_causalHashQuery,
                support_map] at hresult
              obtain ⟨raw, _hraw, rfl⟩ := hresult
              exact ⟨Or.inl rfl, rfl⟩
          | some output =>
              rw [filteredTreeHashComputationAtFromHigh_eq_leafCached _ _ _ _ _ _
                (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_cached
                  high secretKey selected input state index target output hchain
                    hleaf hrevealedTarget hmatch hcached)
                (by simpa [filteredTreeKeygenLeafOutput] using hcached),
                filteredTreePureHashComputation] at hresult
              simp only [simulateQ_pure, WriterT.run_pure, support_pure,
                Set.mem_singleton_iff] at hresult
              subst result
              exact ⟨Or.inl rfl, rfl⟩
        · rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
              (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_not_match
                high secretKey selected input state index target hchain hleaf
                  hrevealedTarget hmatch), filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery,
            support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact ⟨Or.inl rfl, rfl⟩
      · rw [filteredTreeHashComputationAtFromHigh_eq_fresh _ _ _ _ _
            (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_leafProbe_mismatch
              high secretKey selected input state index target value hchain hleaf
                hrevealed hvalue), filteredTreeFreshHashComputation,
          simulate_eagerTrace_causalHashQuery,
          support_map] at hresult
        obtain ⟨raw, _hraw, rfl⟩ := hresult
        exact ⟨Or.inl rfl, rfl⟩


set_option maxRecDepth 1000000 in
theorem relTriple_programmed_monitoredTreeLeafQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((monitorCausalTrace right.1.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (filteredTreeHashComputationAtFromHigh
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
              input causalState)).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  apply relTriple_monitorCausalTrace_of_filtered_until_hit (α := HashOutput)
    left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
      ((randomOracle input).run leftCache) _ rightState monitor hmonitor
        hmonitorAgrees hrevealed
  · exact relTriple_programmed_filteredTreeLeafQuery_until_hit selected
      left right hrel hleftSupport hrightSupport leftCache rightState.causal
        hcausal monitor hrevealed input index target hprobe
  · intro result hresult
    have hparameter := hrel.parameter_eq selected left right hleftSupport
      hrightSupport
    obtain ⟨epoch, endpoints, hinput, _hindex, _htarget⟩ :=
      leafInputProbe?_eq_some left.secretKey.parameter selected input index
        target hprobe
    have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
        input = none := by
      rw [hparameter, hinput]
      exact chainInputProbe?_leafInput left.secretKey.parameter selected epoch
        endpoints
    have hleafRight : leafInputProbe? right.1.1.secretKey.parameter selected
        input = some (index, target) := by
      rw [hparameter]
      exact hprobe
    obtain ⟨htrace, hfinal⟩ :=
      simulate_eagerTrace_filteredTreeLeafQuery_support_trace right.1.2
        (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
          rightState.causal index target hchainRight hleafRight result hresult
    constructor
    · rcases htrace with htrace | htrace <;> rw [htrace]
      · trivial
      · trivial
    · rcases htrace with htrace | htrace
      · rw [htrace, hfinal]
        exact ReplaysCausalReveals.nil rightState.causal.revealed
      · rw [htrace, hfinal]
        exact ReplaysCausalReveals.probe rightState.causal.revealed
          rightState.causal.revealed index target []
            (ReplaysCausalReveals.nil rightState.causal.revealed)

noncomputable def monitoredTreeHashQuery
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (input : HashInput) (state : MonitoredCausalState) :
    ProbComp (HashOutput × MonitoredCausalState) :=
  (monitorCausalTrace table (fun causalState =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredTreeHashComputationAtFromHigh
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
          causalState)).run)).run state

set_option maxRecDepth 1000000 in
theorem relTriple_programmed_monitoredTreeHashQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftCache rightState)
    (input : HashInput) :
    RelTriple
      ((randomOracle input).run leftCache)
      (monitoredTreeHashQuery (right.1.1, right.2) selected right.1.2 input
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  unfold monitoredTreeHashQuery
  cases hchain : chainInputProbe? left.secretKey.parameter selected input with
  | some probe =>
      rcases probe with ⟨index, target⟩
      have hparameter := hrel.parameter_eq selected left right hleftSupport
        hrightSupport
      have hchainRight : chainInputProbe? right.1.1.secretKey.parameter selected
          input = some (index, target) := by
        rw [hparameter]
        exact hchain
      have hhandler : (fun causalState =>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
            (filteredTreeHashComputationAtFromHigh
              (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
                input causalState)).run) =
          (fun causalState =>
            (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
              (filteredProbingAttackerHashQueryAtFromHigh
                (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected
                  input causalState (some (index, target)))).run) := by
        funext causalState
        rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
          (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
            (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
              causalState (index, target) hchainRight)]
        unfold filteredTreeChainHashComputation
        rfl
      rw [hhandler]
      exact relTriple_programmed_monitoredHashQueryWithHigh_until_hit selected
        left right hrel.base hleftSupport hrightSupport leftCache rightState
          hstate input index target hchain
  | none =>
      cases hleaf : leafInputProbe? left.secretKey.parameter selected input with
      | some probe =>
          rcases probe with ⟨index, target⟩
          exact relTriple_programmed_monitoredTreeLeafQuery selected left right
            hrel hleftSupport hrightSupport leftCache rightState hstate input
              index target hleaf
      | none =>
          exact relTriple_programmed_monitoredTreeOrdinaryQuery selected left
            right hrel hleftSupport hrightSupport leftCache rightState hstate
              input hchain hleaf

noncomputable def filteredHighMappedAdversaryRun
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      ((OracleWorld + SigningSpec).Range input × CausalHashState) :=
    match input with
    | .inl (.inl n) => (causalUniformImpl n).run state
    | .inl (.inr hashInput) =>
        filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state
    | .inr request =>
        filteredCausalSigningQuery keyHigh.1 selected request state

noncomputable def filteredHighMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input => StateT.mk (filteredHighMappedAdversaryRun keyHigh selected input)

noncomputable def filteredHighActionTracedMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (OracleComp
            (RevealProbeOracleSimulation.World ChainValueIndex)))) :=
  (filteredHighMappedAdversaryImpl keyHigh selected).withTraceAppend
    attackerActionFragment

noncomputable def filteredHighVerifierRun
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : OracleWorld.Domain)
    (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (OracleWorld.Range input × CausalHashState) :=
    match input with
    | .inl n => (causalUniformImpl n).run state
    | .inr hashInput =>
        filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state

noncomputable def filteredHighVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input => StateT.mk (filteredHighVerifierRun keyHigh selected input)

noncomputable def filteredHighDetailedGameAfterKeygen
    (adversary : Adversary Concrete.cappedScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let handled ← (simulateQ
    (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
      (adversary.main keyHigh.1.publicKey)).run
  let verified ← simulateQ (filteredHighVerifierImpl keyHigh selected)
    (Concrete.cappedScheme.verify keyHigh.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
  pure ((handled.1, verified), handled.2)

abbrev FilteredHighDirectResult :=
  (ProgrammedFixedChainKeygenView × (ChainEdgeIndex → Digest)) ×
    FilteredDirectExecution

noncomputable def filteredHighDirectProgram
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredHighDirectResult := do
  let keyHigh ← RevealProbeOracleSimulation.liftProbComp
    (coupledWarmedFixedChainKeygenWithHigh selected)
  let execution ← (filteredHighDetailedGameAfterKeygen adversary keyHigh
    selected).run (filteredCausalKeygenState selected keyHigh.1)
  pure (keyHigh, execution)

noncomputable def boundedFilteredHighDirectProgram
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredHighDirectResult :=
  RevealProbeOracleSimulation.enforceProbeBound queries
    (filteredHighDirectProgram adversary selected)


theorem boundedFilteredHighDirectProgram_isProbeQueryBoundP
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (selected : ChainIndex) :
    (boundedFilteredHighDirectProgram queries adversary selected).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery queries := by
  exact RevealProbeOracleSimulation.enforceProbeBound_isProbeQueryBoundP
    queries (filteredHighDirectProgram adversary selected)

noncomputable def sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) :=
  unloggedMappedAdversaryImpl publicKey secretKey

theorem sourceDirectMappedAdversaryImpl_eq_compose
    (publicKey : PublicKey) (secretKey : SecretKey) :
    sourceDirectMappedAdversaryImpl publicKey secretKey =
      xmssRomImpl ∘ₛ sourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rfl
    · simp [sourceDirectMappedAdversaryImpl, unloggedMappedAdversaryImpl,
        sourceUnloggedMappedAdversaryImpl, QueryImpl.apply_compose, xmssRomImpl]
  · rfl

abbrev SourceTracedState := QueryCache HashSpec × AttackerActionTrace

noncomputable def actionTracedStateImpl
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace) :
    QueryImpl spec (StateT (σ × AttackerActionTrace) ProbComp) :=
  fun input => StateT.mk fun state => do
    let result ← (impl input).run state.1
    pure (result.1, (result.2, state.2 ++ fragment input result.1))

noncomputable def sourceDirectTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SourceTracedState ProbComp) :=
  actionTracedStateImpl
    (sourceDirectMappedAdversaryImpl publicKey secretKey)
    attackerActionFragment

theorem sourceDirectTracedMappedAdversaryImpl_query_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (cache, trace) =
      (fun result =>
        (result.1.1, (result.2, trace ++ result.1.2))) <$>
        (simulateQ xmssRomImpl
          (sourceActionTracedMappedAdversaryImpl publicKey secretKey input).run
            ).run cache := by
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
    sourceActionTracedMappedAdversaryImpl
  rw [sourceDirectMappedAdversaryImpl_eq_compose]
  simp [QueryImpl.apply_compose, QueryImpl.withTraceAppend_apply,
    map_eq_bind_pure_comp]

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedMappedAdversaryImpl_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (cache, trace) =
      (fun result =>
        (result.1.1, (result.2, trace ++ result.1.2))) <$>
        (simulateQ xmssRomImpl
          (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
            computation).run).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache trace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [StateT.run_bind, WriterT.run_bind', simulateQ_bind, map_bind,
        simulateQ_spec_query]
      rw [sourceDirectTracedMappedAdversaryImpl_query_run_eq]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      simpa [List.append_assoc] using
        (ih head.1.1 head.2 (trace ++ head.1.2))

abbrev MonitoredTracedState := MonitoredCausalState × AttackerActionTrace

noncomputable def filteredHighMonitoredBaseMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT MonitoredCausalState ProbComp) :=
  fun input => monitorCausalTrace table fun causalState =>
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredHighMappedAdversaryRun keyHigh selected input causalState)).run

noncomputable def filteredHighMonitoredMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT MonitoredTracedState ProbComp) :=
  actionTracedStateImpl
    (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table)
    attackerActionFragment

def MonitoredTracedStateRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (left : SourceTracedState) (right : MonitoredTracedState) : Prop :=
  MonitoredFilteredStateRelation parameter selected leftBase rightBase table
      left.1 right.1 ∧
    left.2 = right.2

noncomputable abbrev sourceDirectTracedHashVerifierImpl
    (hashInput : HashInput) : StateT SourceTracedState ProbComp HashOutput :=
  StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (randomOracle hashInput).run state.1

noncomputable abbrev filteredHighMonitoredUniformVerifierImpl
    (table : ChainValueIndex → Digest) (n : Nat) :
    StateT MonitoredTracedState ProbComp (unifSpec.Range n) :=
  StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((causalUniformImpl n).run causalState)).run)).run state.1

noncomputable def filteredHighMonitoredHashVerifierRun
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (state : MonitoredTracedState) :
    ProbComp (HashOutput × MonitoredTracedState) :=
  (fun result => (result.1, (result.2, state.2))) <$>
    monitoredTreeHashQuery keyHigh selected table hashInput state.1

theorem filteredHighMonitoredHashVerifierRun_eq
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (state : MonitoredTracedState) :
    filteredHighMonitoredHashVerifierRun keyHigh selected table hashInput state =
      ((fun result => (result.1, (result.2, state.2))) <$>
        monitoredTreeHashQuery keyHigh selected table hashInput state.1) := by
  rfl

structure FilteredHighMonitoredHashVerifierPackage
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) where
  impl : StateT MonitoredTracedState ProbComp HashOutput
  run_eq : ∀ state, impl.run state =
    filteredHighMonitoredHashVerifierRun keyHigh selected table hashInput state

noncomputable def filteredHighMonitoredHashVerifierPackage
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) :
    FilteredHighMonitoredHashVerifierPackage keyHigh selected table hashInput :=
  { impl := StateT.mk
      (filteredHighMonitoredHashVerifierRun keyHigh selected table hashInput)
    run_eq := by
      intro state
      exact StateT.run_mk _ state }

noncomputable def filteredHighMonitoredHashVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) :
    StateT MonitoredTracedState ProbComp HashOutput :=
  (filteredHighMonitoredHashVerifierPackage keyHigh selected table hashInput).impl

theorem filteredHighMonitoredHashVerifierImpl_run
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (state : MonitoredTracedState) :
    (filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput).run
        state =
      filteredHighMonitoredHashVerifierRun keyHigh selected table hashInput
        state := by
  exact (filteredHighMonitoredHashVerifierPackage keyHigh selected table
    hashInput).run_eq state

noncomputable def sourceDirectTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceTracedState ProbComp) :=
  fun input =>
    match input with
    | .inl n => StateT.mk fun state =>
        (fun result => (result.1, (result.2, state.2))) <$>
          (xmssRomImpl (.inl n)).run state.1
    | .inr hashInput => sourceDirectTracedHashVerifierImpl hashInput

theorem sourceDirectTracedVerifierImpl_query_run_eq
    (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (sourceDirectTracedVerifierImpl input).run (cache, trace) =
      (fun result => (result.1, (result.2, trace))) <$>
        (xmssRomImpl input).run cache := by
  rcases input with n | hashInput <;> rfl

theorem sourceDirectTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (simulateQ sourceDirectTracedVerifierImpl computation).run (cache, trace) =
      (fun result => (result.1, (result.2, trace))) <$>
        (simulateQ xmssRomImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query,
        map_bind]
      rw [sourceDirectTracedVerifierImpl_query_run_eq]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      exact ih head.1 head.2

noncomputable def filteredHighMonitoredVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl OracleWorld (StateT MonitoredTracedState ProbComp) :=
  fun input =>
    match input with
    | .inl n => filteredHighMonitoredUniformVerifierImpl table n
    | .inr hashInput => filteredHighMonitoredHashVerifierImpl keyHigh selected
        table hashInput

theorem relTriple_keepAttackerTrace_until_bad
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftTrace rightTrace : AttackerActionTrace) (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : ProbComp (α × MonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.bad)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$> leftComputation)
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  let wrapLeft := fun result : α × QueryCache HashSpec =>
    (result.1, (result.2, leftTrace))
  let wrapRight := fun result : α × MonitoredCausalState =>
    (result.1, (result.2, rightTrace))
  let post := fun leftResult : α × SourceTracedState =>
    fun rightResult : α × MonitoredTracedState =>
      (leftResult.1 = rightResult.1 ∧
        MonitoredTracedStateRelation parameter selected leftBase rightBase
          table leftResult.2 rightResult.2) ∨
      rightResult.2.1.bad
  have hprepared : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2, htrace⟩
    · exact Or.inr hbad
  simpa [wrapLeft, wrapRight, post] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_keepAttackerTrace_hash_until_bad
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftTrace rightTrace : AttackerActionTrace) (htrace : leftTrace = rightTrace)
    (hashInput : HashInput)
    (leftState : QueryCache HashSpec)
    (rightComputation : ProbComp (HashOutput × MonitoredCausalState))
    (hcouple : RelTriple
      ((randomOracle hashInput).run leftState) rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.bad)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$>
        ((randomOracle hashInput).run leftState))
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  exact relTriple_keepAttackerTrace_until_bad parameter selected leftBase
    rightBase table leftTrace rightTrace htrace
      ((randomOracle hashInput).run leftState) rightComputation hcouple

set_option maxHeartbeats 200000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_verifier_uniform_query
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (n : Nat) :
    RelTriple
      ((sourceDirectTracedVerifierImpl (.inl n)).run leftState)
      ((filteredHighMonitoredVerifierImpl (right.1.1, right.2) selected
        right.1.2 (.inl n)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hparameter := hrel.parameter_eq selected left right hleftSupport
    hrightSupport
  have hstateRight : MonitoredFilteredStateRelation
      right.1.1.secretKey.parameter selected left.cache right.1.1.cache
        right.1.2 leftState.1 rightState.1 := by
    simpa [hparameter] using hstate.1
  have hbase := relTriple_programmed_monitoredUniformQuery
    right.1.1.secretKey.parameter selected left.cache right.1.1.cache
      right.1.2 leftState.1 rightState.1 hstateRight n
  unfold sourceDirectTracedVerifierImpl filteredHighMonitoredVerifierImpl
  simpa [xmssRomImpl, unifFwdImpl, OracleComp.liftM_run_StateT,
    hparameter, map_eq_bind_pure_comp] using
      (relTriple_keepAttackerTrace_until_bad left.secretKey.parameter selected
        left.cache right.1.1.cache right.1.2 leftState.2 rightState.2 hstate.2
          ((xmssRomImpl (Sum.inl n)).run leftState.1)
          ((monitorCausalTrace right.1.2 (fun causalState =>
            (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
              ((causalUniformImpl n).run causalState)).run)).run rightState.1)
          (by simpa [xmssRomImpl, unifFwdImpl,
            OracleComp.liftM_run_StateT, hparameter] using hbase))


set_option maxHeartbeats 100000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (hashInput : HashInput) :
    RelTriple
      ((fun result => (result.1, (result.2, leftState.2))) <$>
        ((randomOracle hashInput).run leftState.1))
      (filteredHighMonitoredHashVerifierRun (right.1.1, right.2) selected
        right.1.2 hashInput rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  rw [filteredHighMonitoredHashVerifierRun_eq]
  apply relTriple_keepAttackerTrace_hash_until_bad
    left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
      leftState.2 rightState.2 hstate.2 hashInput leftState.1
  exact relTriple_programmed_monitoredTreeHashQuery selected left right hrel
    hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 hashInput

theorem relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query_impl
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (hashInput : HashInput) :
    RelTriple
      ((sourceDirectTracedHashVerifierImpl hashInput).run leftState)
      ((filteredHighMonitoredHashVerifierImpl (right.1.1, right.2) selected
        right.1.2 hashInput).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  rw [filteredHighMonitoredHashVerifierImpl_run]
  exact relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query
    selected left right hrel hleftSupport hrightSupport leftState rightState
      hstate hashInput


def VerifierQueryCouplingClaim
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (input : OracleWorld.Domain) : Prop :=
  match input with
  | .inl n => RelTriple
      ((sourceDirectTracedVerifierImpl (.inl n)).run leftState)
      ((filteredHighMonitoredVerifierImpl (right.1.1, right.2) selected
        right.1.2 (.inl n)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad)
  | .inr hashInput => RelTriple
      ((sourceDirectTracedHashVerifierImpl hashInput).run leftState)
      ((filteredHighMonitoredHashVerifierImpl (right.1.1, right.2) selected
        right.1.2 hashInput).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2 leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad)

set_option maxHeartbeats 200000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_verifier_query
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : OracleWorld.Domain) :
    VerifierQueryCouplingClaim selected left right leftState rightState input := by
  rcases input with n | hashInput
  · exact relTriple_sourceDirect_filteredHighMonitored_verifier_uniform_query
      selected left right hrel hleftSupport hrightSupport leftState rightState
        hstate n
  · exact relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query_impl
      selected left right hrel hleftSupport hrightSupport leftState rightState
        hstate hashInput

theorem filteredHighMonitoredUniformVerifier_preserves_bad
    (table : ChainValueIndex → Digest)
    (n : Nat)
    (state : MonitoredTracedState) (hbad : state.1.bad)
    (result : unifSpec.Range n × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredUniformVerifierImpl table n).run state)) :
  result.2.1.bad := by
  unfold filteredHighMonitoredUniformVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact monitorCausalTrace_preserves_bad table _ state.1 hbad baseResult
    hbaseResult


theorem filteredHighMonitoredHashVerifier_preserves_bad
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput)
    (state : MonitoredTracedState) (hbad : state.1.bad)
    (result : HashOutput × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredHashVerifierImpl keyHigh selected table
        hashInput).run state)) :
  result.2.1.bad := by
  rw [filteredHighMonitoredHashVerifierImpl_run] at hresult
  rw [filteredHighMonitoredHashVerifierRun_eq] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact monitorCausalTrace_preserves_bad table _ state.1 hbad baseResult
    hbaseResult

theorem filteredHighMonitoredUniformVerifier_preserves_traceConsistent
    (table : ChainValueIndex → Digest) (n : Nat)
    (state : MonitoredTracedState) (hconsistent : state.1.TraceConsistent table)
    (result : unifSpec.Range n × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredUniformVerifierImpl table n).run state)) :
    result.2.1.TraceConsistent table := by
  unfold filteredHighMonitoredUniformVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact monitorCausalTrace_preserves_traceConsistent table _ state.1 hconsistent
    baseResult hbaseResult

theorem filteredHighMonitoredHashVerifier_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (state : MonitoredTracedState)
    (hconsistent : state.1.TraceConsistent table)
    (result : HashOutput × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredHashVerifierImpl keyHigh selected table
        hashInput).run state)) :
    result.2.1.TraceConsistent table := by
  rw [filteredHighMonitoredHashVerifierImpl_run] at hresult
  rw [filteredHighMonitoredHashVerifierRun_eq, support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact monitorCausalTrace_preserves_traceConsistent table _ state.1 hconsistent
    baseResult hbaseResult

theorem filteredHighMonitoredVerifier_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl.PreservesInv
      (filteredHighMonitoredVerifierImpl keyHigh selected table)
      (fun candidate : MonitoredTracedState =>
        candidate.1.TraceConsistent table) := by
  intro input state hconsistent result hresult
  rcases input with n | hashInput
  · exact filteredHighMonitoredUniformVerifier_preserves_traceConsistent table n
      state hconsistent result hresult
  · exact filteredHighMonitoredHashVerifier_preserves_traceConsistent keyHigh
      selected table hashInput state hconsistent result hresult


set_option maxHeartbeats 200000 in
theorem filteredHighMonitoredVerifier_preserves_bad
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl.PreservesInv
      (filteredHighMonitoredVerifierImpl keyHigh selected table)
      (fun candidate : MonitoredTracedState => candidate.1.bad) := by
  intro input state hbad result hresult
  rcases input with n | hashInput
  · exact filteredHighMonitoredUniformVerifier_preserves_bad table n state hbad
      result hresult
  · exact filteredHighMonitoredHashVerifier_preserves_bad keyHigh selected table
      hashInput state hbad result hresult


theorem filteredHighMonitoredVerifier_simulation_preserves_bad
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : MonitoredTracedState) (hbad : state.1.bad)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        computation).run state)) :
    result.2.1.bad := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredVerifierImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState => candidate.1.bad)
    (filteredHighMonitoredVerifier_preserves_bad keyHigh selected table)
      computation state hbad result hresult

theorem filteredHighMonitoredVerifier_simulation_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : MonitoredTracedState) (hconsistent : state.1.TraceConsistent table)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        computation).run state)) :
    result.2.1.TraceConsistent table := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredVerifierImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState =>
      candidate.1.TraceConsistent table)
    (filteredHighMonitoredVerifier_preserves_traceConsistent keyHigh selected
      table) computation state hconsistent result hresult


set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_verifier
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (computation : OracleComp OracleWorld α)
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState) :
    RelTriple
      ((simulateQ sourceDirectTracedVerifierImpl computation).run leftState)
      ((simulateQ
        (filteredHighMonitoredVerifierImpl (right.1.1, right.2) selected
          right.1.2) computation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hstate⟩)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      rcases input with n | hashInput
      · apply relTriple_bind
          (relTriple_sourceDirect_filteredHighMonitored_verifier_uniform_query
            selected left right hrel hleftSupport hrightSupport leftState
              rightState hstate n)
        intro headLeft headRight hhead
        rcases hhead with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          rw [← hvalue]
          exact ih headLeft.1 headLeft.2 headRight.2 hstates
        · apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (filteredHighMonitoredVerifier_simulation_preserves_bad
                (right.1.1, right.2) selected right.1.2 (next headRight.1)
                  headRight.2 hbad))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2

      · apply relTriple_bind
          (relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query_impl
            selected left right hrel hleftSupport hrightSupport leftState
              rightState hstate hashInput)
        intro headLeft headRight hhead
        rcases hhead with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          rw [← hvalue]
          exact ih headLeft.1 headLeft.2 headRight.2 hstates
        · apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (filteredHighMonitoredVerifier_simulation_preserves_bad
                (right.1.1, right.2) selected right.1.2 (next headRight.1)
                  headRight.2 hbad))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2


theorem monitoredTracedStateRelation_initial
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected)) :
    MonitoredTracedStateRelation left.secretKey.parameter selected left.cache
      right.1.cache right.2 (left.cache, [])
      (⟨filteredCausalKeygenState selected right.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, []) := by
  refine ⟨monitoredFilteredStateRelation_initial
    left.secretKey.parameter selected left.cache right.1.cache right.2
      left.cache (filteredCausalKeygenState selected right.1) ?_ ?_, rfl⟩
  · exact programmedActual_filteredKeygen_stateRelation selected left right
      hrel hleftSupport hrightSupport
  · exact filteredCausalKeygenState_revealed selected right.1

theorem programmedActualKeygenCacheHighRelation_to_stable
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected)) :
    ProgrammedActualKeygenStableRelation selected left right.1 := by
  exact ⟨hrel.base,
    programmedWarmedFixedChainKeygen_support_treeCacheStable
      selected left hleftSupport,
    actualFixedChainKeygen_support_treeCacheStable
      selected right.1.1 hrightSupport⟩

theorem relTriple_appendAttackerAction_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftTrace rightTrace : AttackerActionTrace)
    (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp
      ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec))
    (rightComputation : ProbComp
      ((OracleWorld + SigningSpec).Range input × MonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.bad)) :
    RelTriple
      (do
        let result ← leftComputation
        pure (result.1,
          (result.2, leftTrace ++ attackerActionFragment input result.1)))
      (do
        let result ← rightComputation
        pure (result.1,
          (result.2, rightTrace ++ attackerActionFragment input result.1)))
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  let wrapLeft := fun result :
      (OracleWorld + SigningSpec).Range input × QueryCache HashSpec =>
    (result.1,
      (result.2, leftTrace ++ attackerActionFragment input result.1))
  let wrapRight := fun result :
      (OracleWorld + SigningSpec).Range input × MonitoredCausalState =>
    (result.1,
      (result.2, rightTrace ++ attackerActionFragment input result.1))
  let post := fun leftResult :
      (OracleWorld + SigningSpec).Range input × SourceTracedState =>
    fun rightResult :
      (OracleWorld + SigningSpec).Range input × MonitoredTracedState =>
    (leftResult.1 = rightResult.1 ∧
      MonitoredTracedStateRelation parameter selected leftBase rightBase table
        leftResult.2 rightResult.2) ∨
    rightResult.2.1.bad
  have hprepared : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · subst rightTrace
      exact Or.inl ⟨hgood.1, hgood.2,
        congrArg (fun output =>
          leftTrace ++ attackerActionFragment input output) hgood.1⟩
    · exact Or.inr hbad
  simpa [wrapLeft, wrapRight, post, map_eq_bind_pure_comp] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_actionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT MonitoredCausalState ProbComp))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.bad)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  unfold actionTracedStateImpl
  exact relTriple_appendAttackerAction_until_bad input parameter selected
    leftBase rightBase table leftState.2 rightState.2 htrace _ _ hcouple

theorem relTriple_sourceDirect_filteredHighMonitored_uniform
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (leftBase : QueryCache HashSpec)
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation
      keyHigh.1.secretKey.parameter selected leftBase keyHigh.1.cache table
        leftState rightState)
    (n : Nat) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl keyHigh.1.publicKey
        keyHigh.1.secretKey (Sum.inl (Sum.inl n))).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table
        (Sum.inl (Sum.inl n))).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation keyHigh.1.secretKey.parameter selected
            leftBase keyHigh.1.cache table leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hcouple := relTriple_programmed_monitoredUniformQuery
    keyHigh.1.secretKey.parameter selected leftBase keyHigh.1.cache table
      leftState.1 rightState.1 hstate.1 n
  have hbase : RelTriple
      ((sourceDirectMappedAdversaryImpl keyHigh.1.publicKey
        keyHigh.1.secretKey (Sum.inl (Sum.inl n))).run leftState.1)
      ((filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        (Sum.inl (Sum.inl n))).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation keyHigh.1.secretKey.parameter selected
            leftBase keyHigh.1.cache table leftResult.2 rightResult.2) ∨
        rightResult.2.bad) := by
    simpa [sourceDirectMappedAdversaryImpl,
      filteredHighMonitoredBaseMappedAdversaryImpl,
      filteredHighMappedAdversaryRun,
      unloggedMappedAdversaryImpl_apply_inl, xmssRomImpl, unifFwdImpl,
      OracleComp.liftM_run_StateT] using hcouple
  have hlift := relTriple_actionTracedState_until_bad
    (Sum.inl (Sum.inl n)) keyHigh.1.secretKey.parameter selected leftBase
      keyHigh.1.cache table
      (sourceDirectMappedAdversaryImpl keyHigh.1.publicKey
        keyHigh.1.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_hash_of_probe
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult selected right.1.1
    hrightSupport
  have hparameter : right.1.1.secretKey.parameter =
      left.secretKey.parameter := by
    calc
      right.1.1.secretKey.parameter = right.1.1.publicKey.parameter :=
        (right.1.1.parameter_eq hrightKey).symm
      _ = left.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.base.1.2.1.symm
      _ = left.secretKey.parameter := left.parameter_eq hleftKey
  have hprobeRight : chainInputProbe? right.1.1.secretKey.parameter selected
      input = some (index, target) := by
    rw [hparameter]
    exact hprobe
  have hcouple := relTriple_programmed_monitoredHashQueryWithHigh_until_hit
    selected left right hrel hleftSupport hrightSupport leftState.1
      rightState.1 hstate.1 input index target hprobe
  have hcomputation : ∀ causalState,
      filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
            causalState =
        filteredProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
            causalState (some (index, target)) := by
    intro causalState
    rw [filteredTreeHashComputationAtFromHigh_eq_chain _ _ _ _ _ _
      (filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
        (chainValueHighTableOfEdges right.2) right.1.1.secretKey selected input
          causalState (index, target) hprobeRight)]
    unfold filteredTreeChainHashComputation
    rfl
  have hbase : RelTriple
      ((sourceDirectMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState.1)
      ((filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.bad) := by
    simpa [sourceDirectMappedAdversaryImpl,
      filteredHighMonitoredBaseMappedAdversaryImpl,
      filteredHighMappedAdversaryRun,
      filteredTreeProbingAttackerHashQueryAtFromHigh,
      unloggedMappedAdversaryImpl_apply_inl, xmssRomImpl,
      hprobeRight, hcomputation] using hcouple
  have hlift := relTriple_actionTracedState_until_bad
    (Sum.inl (Sum.inr input)) left.secretKey.parameter selected left.cache
      right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_hash_of_leafProbe
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : leafInputProbe? left.secretKey.parameter selected input =
      some (index, target)) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hcouple := relTriple_programmed_monitoredTreeLeafQuery selected left
    right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
      input index target hprobe
  have hbase : RelTriple
      ((sourceDirectMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState.1)
      ((filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.bad) := by
    simpa [sourceDirectMappedAdversaryImpl,
      filteredHighMonitoredBaseMappedAdversaryImpl,
      filteredHighMappedAdversaryRun,
      unloggedMappedAdversaryImpl_apply_inl, xmssRomImpl] using hcouple
  have hlift := relTriple_actionTracedState_until_bad
    (Sum.inl (Sum.inr input)) left.secretKey.parameter selected left.cache
      right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_hash_of_no_probes
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : HashInput)
    (hchain : chainInputProbe? left.secretKey.parameter selected input = none)
    (hleaf : leafInputProbe? left.secretKey.parameter selected input = none) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hcouple := relTriple_programmed_monitoredTreeOrdinaryQuery selected left
    right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
      input hchain hleaf
  have hbase : RelTriple
      ((sourceDirectMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState.1)
      ((filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.bad) := by
    simpa [sourceDirectMappedAdversaryImpl,
      filteredHighMonitoredBaseMappedAdversaryImpl,
      filteredHighMappedAdversaryRun,
      unloggedMappedAdversaryImpl_apply_inl, xmssRomImpl] using hcouple
  have hlift := relTriple_actionTracedState_until_bad
    (Sum.inl (Sum.inr input)) left.secretKey.parameter selected left.cache
      right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_hash
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : HashInput) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inl (Sum.inr input))).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inl (Sum.inr input))).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  cases hchain : chainInputProbe? left.secretKey.parameter selected input with
  | some probe =>
      rcases probe with ⟨index, target⟩
      exact relTriple_sourceDirect_filteredHighMonitored_hash_of_probe selected
        left right hrel.base hleftSupport hrightSupport leftState rightState
          hstate input index target hchain
  | none =>
      cases hleaf : leafInputProbe? left.secretKey.parameter selected input with
      | some probe =>
          rcases probe with ⟨index, target⟩
          exact
            relTriple_sourceDirect_filteredHighMonitored_hash_of_leafProbe
              selected left right hrel hleftSupport hrightSupport leftState
                rightState hstate input index target hleaf
      | none =>
          exact
            relTriple_sourceDirect_filteredHighMonitored_hash_of_no_probes
              selected left right hrel hleftSupport hrightSupport leftState
                rightState hstate input hchain hleaf

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_signing
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (request : SignRequest) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inr request)).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inr request)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hstable := programmedActualKeygenCacheHighRelation_to_stable
    selected left right hrel hleftSupport hrightSupport
  have hcouple := relTriple_programmed_monitoredSigningQuery selected left
    right.1 hstable hleftSupport hrightSupport leftState.1 rightState.1
      hstate.1 request
  have hbase := hcouple
  have hlift := relTriple_actionTracedState_until_bad (Sum.inr request)
    left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa only [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_action
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey
        input).run leftState)
      ((filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | input
    · have hparameter := hrel.parameter_eq selected left right hleftSupport
        hrightSupport
      have hstateRight : MonitoredTracedStateRelation
          right.1.1.secretKey.parameter selected left.cache right.1.1.cache
            right.1.2 leftState rightState := by
        simpa [hparameter] using hstate
      simpa [hparameter, sourceDirectTracedMappedAdversaryImpl,
        sourceDirectMappedAdversaryImpl, actionTracedStateImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        filteredHighMonitoredMappedAdversaryImpl,
        filteredHighMonitoredBaseMappedAdversaryImpl] using
        (relTriple_sourceDirect_filteredHighMonitored_uniform
          (right.1.1, right.2) selected right.1.2 left.cache leftState
            rightState hstateRight n)
    · exact relTriple_sourceDirect_filteredHighMonitored_hash selected left
        right hrel hleftSupport hrightSupport leftState rightState hstate input
  · exact relTriple_sourceDirect_filteredHighMonitored_signing selected left
      right hrel.base hleftSupport hrightSupport leftState rightState hstate
        request

theorem filteredHighMonitoredBaseMappedAdversaryImpl_preserves_bad
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredCausalState) (hbad : state.bad)
    (result : (OracleWorld + SigningSpec).Range input × MonitoredCausalState)
    (hresult : result ∈ support
      ((filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state)) :
    result.2.bad := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · apply monitorCausalTrace_preserves_bad table _ state hbad result
      simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult
    · apply monitorCausalTrace_preserves_bad table _ state hbad result
      simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult
  · apply monitorCausalTrace_preserves_bad table _ state hbad result
    simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult

theorem filteredHighMonitoredMappedAdversaryImpl_preserves_bad
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredTracedState) (hbad : state.1.bad)
    (result : (OracleWorld + SigningSpec).Range input × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input).run
        state)) :
    result.2.1.bad := by
  unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact filteredHighMonitoredBaseMappedAdversaryImpl_preserves_bad keyHigh
    selected table input state.1 hbad baseResult hbaseResult

theorem filteredHighMonitoredBaseMappedAdversaryImpl_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredCausalState) (hconsistent : state.TraceConsistent table)
    (result : (OracleWorld + SigningSpec).Range input × MonitoredCausalState)
    (hresult : result ∈ support
      ((filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state)) :
    result.2.TraceConsistent table := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · apply monitorCausalTrace_preserves_traceConsistent table _ state hconsistent
      simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult
    · apply monitorCausalTrace_preserves_traceConsistent table _ state hconsistent
      simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult
  · apply monitorCausalTrace_preserves_traceConsistent table _ state hconsistent
    simpa [filteredHighMonitoredBaseMappedAdversaryImpl] using hresult

theorem filteredHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl.PreservesInv
      (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (fun candidate : MonitoredTracedState =>
        candidate.1.TraceConsistent table) := by
  intro input state hconsistent result hresult
  unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact filteredHighMonitoredBaseMappedAdversaryImpl_preserves_traceConsistent
    keyHigh selected table input state.1 hconsistent baseResult hbaseResult

theorem filteredHighMonitoredAdversary_simulation_preserves_traceConsistent
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredTracedState) (hconsistent : state.1.TraceConsistent table)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
          computation).run state)) :
    result.2.1.TraceConsistent table := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState =>
      candidate.1.TraceConsistent table)
    (filteredHighMonitoredMappedAdversaryImpl_preserves_traceConsistent keyHigh
      selected table) computation state hconsistent result hresult

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_adversary
    (adversary : Adversary Concrete.cappedScheme)
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState) :
    RelTriple
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey)
          (adversary.main left.publicKey)).run leftState)
      ((simulateQ
        (filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
          selected right.1.2) (adversary.main left.publicKey)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right
    (sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey)
    (filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2) selected
      right.1.2)
    (MonitoredTracedStateRelation left.secretKey.parameter selected left.cache
      right.1.1.cache right.1.2)
    (fun state : MonitoredTracedState => state.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_sourceDirect_filteredHighMonitored_action selected left right
        hrel hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult =>
      filteredHighMonitoredMappedAdversaryImpl_preserves_bad
        (right.1.1, right.2) selected right.1.2 input state hbad result hresult)
    (adversary.main left.publicKey) leftState rightState hstate


noncomputable def sourceDirectTracedDetailedExecution
    (adversary : Adversary Concrete.cappedScheme)
    (keyView : ProgrammedFixedChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceTracedState) := do
  let handled ← (simulateQ
    (sourceDirectTracedMappedAdversaryImpl keyView.publicKey keyView.secretKey)
      (adversary.main keyView.publicKey)).run (keyView.cache, [])
  let verified ← (simulateQ sourceDirectTracedVerifierImpl
    (Concrete.cappedScheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

noncomputable def filteredHighMonitoredDetailedExecution
    (adversary : Adversary Concrete.cappedScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    ProbComp ((Forgery × Bool) × MonitoredTracedState) := do
  let initial : MonitoredTracedState :=
    (⟨filteredCausalKeygenState selected keyHigh.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let handled ← (simulateQ
    (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (adversary.main keyHigh.1.publicKey)).run initial
  let verified ← (simulateQ
    (filteredHighMonitoredVerifierImpl keyHigh selected table)
    (Concrete.cappedScheme.verify keyHigh.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

theorem filteredHighMonitoredDetailedExecution_traceConsistent
    (adversary : Adversary Concrete.cappedScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (result : (Forgery × Bool) × MonitoredTracedState)
    (hresult : result ∈ support
      (filteredHighMonitoredDetailedExecution adversary keyHigh selected
        table)) :
    result.2.1.TraceConsistent table := by
  unfold filteredHighMonitoredDetailedExecution at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hresult⟩ := hresult
  have hhandledConsistent :=
    filteredHighMonitoredAdversary_simulation_preserves_traceConsistent
      keyHigh selected table (adversary.main keyHigh.1.publicKey)
      (⟨filteredCausalKeygenState selected keyHigh.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, [])
      (monitoredCausalState_initial_traceConsistent table
        (filteredCausalKeygenState selected keyHigh.1)) handled hhandled
  rw [mem_support_bind_iff] at hresult
  obtain ⟨verified, hvertified, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact filteredHighMonitoredVerifier_simulation_preserves_traceConsistent
    keyHigh selected table
    (Concrete.cappedScheme.verify keyHigh.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
    handled.2 hhandledConsistent verified hvertified

def sourceDirectExecutionResult
    (keyView : ProgrammedFixedChainKeygenView)
    (execution : (Forgery × Bool) × SourceTracedState) :
    (GameOutcome × QueryCache HashSpec) × AttackerActionTrace :=
  ((actionTraceOutcome keyView.publicKey keyView.secretKey
      (execution.1, execution.2.2), execution.2.1), execution.2.2)

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedDetailedExecution_eq_actionTraced
    (adversary : Adversary Concrete.cappedScheme)
    (keyView : ProgrammedFixedChainKeygenView) :
    sourceDirectExecutionResult keyView <$>
        sourceDirectTracedDetailedExecution adversary keyView =
      detailedGameAfterKeygenWithActionTrace adversary keyView.publicKey
        keyView.secretKey keyView.cache := by
  unfold sourceDirectTracedDetailedExecution
    detailedGameAfterKeygenWithActionTrace
    sourceActionTracedDetailedGameAfterKeygen
  rw [sourceDirectTracedMappedAdversaryImpl_run_eq]
  simp only [List.nil_append, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro handled
  simp only [Function.comp_apply, pure_bind]
  rw [sourceDirectTracedVerifierImpl_run_eq]
  simp [sourceDirectExecutionResult, map_eq_bind_pure_comp]

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_detailedExecution
    (adversary : Adversary Concrete.cappedScheme)
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected)) :
    RelTriple
      (sourceDirectTracedDetailedExecution adversary left)
      (filteredHighMonitoredDetailedExecution adversary
        (right.1.1, right.2) selected right.1.2)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.1.bad) := by
  have hinitial := monitoredTracedStateRelation_initial selected left right.1
    (programmedActualKeygenCacheHighRelation_to_stable selected left right
      hrel.base hleftSupport hrightSupport)
    hleftSupport hrightSupport
  unfold sourceDirectTracedDetailedExecution
    filteredHighMonitoredDetailedExecution
  rw [← hrel.base.base.1.2.1]
  apply relTriple_bind
    (relTriple_sourceDirect_filteredHighMonitored_adversary adversary selected
      left right hrel hleftSupport hrightSupport (left.cache, [])
        (⟨filteredCausalKeygenState selected right.1.1,
          some AdaptiveRevealMonitor.State.empty, []⟩, []) hinitial)
  intro leftHandled rightHandled hhandled
  rcases hhandled with hgood | hbad
  · obtain ⟨hforgery, hstates⟩ := hgood
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_sourceDirect_filteredHighMonitored_verifier selected left right
        hrel hleftSupport hrightSupport
        (Concrete.cappedScheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)
        leftHandled.2 rightHandled.2 hstates)
    intro leftVerified rightVerified hverified
    apply relTriple_pure_pure
    rcases hverified with hverifiedGood | hverifiedBad
    · exact Or.inl ⟨congrArg (Prod.mk leftHandled.1) hverifiedGood.1,
        hverifiedGood.2⟩
    · exact Or.inr hverifiedBad
  · apply relTriple_bind
      (relTriple_prod
        (fun _result _hresult => True.intro)
        (filteredHighMonitoredVerifier_simulation_preserves_bad
          (right.1.1, right.2) selected right.1.2
          (Concrete.cappedScheme.verify left.publicKey rightHandled.1.epoch
            rightHandled.1.message rightHandled.1.signature)
          rightHandled.2 hbad))
    intro leftVerified rightVerified hverified
    apply relTriple_pure_pure
    exact Or.inr hverified.2


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem uniformCoupledWarmedFixedChainKeygenWithHigh_support_actual
    (selected : ChainIndex)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hright : right ∈ support
      (uniformCoupledWarmedFixedChainKeygenWithHigh selected)) :
    right.1.1 ∈ support (actualFixedChainKeygen selected) := by
  change right.1.1 ∈ support
    (XmssSecurity.actualFixedChainKeygen selected)
  unfold uniformCoupledWarmedFixedChainKeygenWithHigh at hright
  rw [mem_support_bind_iff] at hright
  obtain ⟨base, _hbase, hright⟩ := hright
  rw [mem_support_bind_iff] at hright
  obtain ⟨keyHigh, hkeyHigh, hpure⟩ := hright
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  have hrightFirst : right.1.1 = keyHigh.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hpure
  rw [hrightFirst]
  have hprojected : keyHigh.1 ∈ support
      (Prod.fst <$> coupledWarmedFixedChainKeygenWithHigh selected) := by
    rw [support_map]
    exact ⟨keyHigh, hkeyHigh, rfl⟩
  rw [mem_support_iff_evalDist_apply_ne_zero] at hprojected ⊢
  rw [evalDist_coupledWarmedFixedChainKeygenWithHigh_fst_eq_actual selected]
    at hprojected
  exact hprojected

abbrev SourceDirectTracedProgramResult :=
  ProgrammedFixedChainKeygenView ×
    ((Forgery × Bool) × SourceTracedState)

abbrev FilteredHighMonitoredProgramResult :=
  ((ProgrammedFixedChainKeygenView × (ChainValueIndex → Digest)) ×
    (ChainEdgeIndex → Digest)) ×
      ((Forgery × Bool) × MonitoredTracedState)

def filteredHighMonitoredProgramProjection
    (result : FilteredHighMonitoredProgramResult) :
    (ChainValueIndex → Digest) ×
      (FilteredHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      ((result.2.1, result.2.2.2), result.2.2.1.causal)),
      result.2.2.1.trace))

noncomputable def sourceDirectTracedProgram
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex) :
    ProbComp SourceDirectTracedProgramResult := do
  let keyView ← programmedWarmedFixedChainKeygen selected
  let execution ← sourceDirectTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceDirectProgramResult
    (result : SourceDirectTracedProgramResult) :
    FixedChainActionTracedResult :=
  let execution := sourceDirectExecutionResult result.1 result.2
  ((result.1, execution.1), execution.2)

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedProgram_eq_highProgrammedWarmedDetailedGame
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex) :
    sourceDirectProgramResult <$> sourceDirectTracedProgram adversary selected =
      highProgrammedWarmedDetailedGame adversary selected := by
  unfold sourceDirectTracedProgram highProgrammedWarmedDetailedGame
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceDirectTracedDetailedExecution_eq_actionTraced]
  simp [sourceDirectProgramResult, map_eq_bind_pure_comp]

noncomputable def filteredHighMonitoredProgram
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex) :
    ProbComp FilteredHighMonitoredProgramResult := do
  let keyHigh ← uniformCoupledWarmedFixedChainKeygenWithHigh selected
  let execution ← filteredHighMonitoredDetailedExecution adversary
    (keyHigh.1.1, keyHigh.2) selected keyHigh.1.2
  pure (keyHigh, execution)

def SourceFilteredHighMonitoredProgramRelation
    (selected : ChainIndex)
    (left : SourceDirectTracedProgramResult)
    (right : FilteredHighMonitoredProgramResult) : Prop :=
  ProgrammedActualKeygenTreeCacheHighRelation selected left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      MonitoredTracedStateRelation left.1.secretKey.parameter selected
        left.1.cache right.1.1.1.cache right.1.1.2
          left.2.2 right.2.2) ∨
    right.2.2.1.bad) ∧
    right.2.2.1.TraceConsistent right.1.1.2

theorem sourceFilteredHighMonitoredProgramRelation_bad_implies_observedHit
    (selected : ChainIndex) (left : SourceDirectTracedProgramResult)
    (right : FilteredHighMonitoredProgramResult)
    (hrel : SourceFilteredHighMonitoredProgramRelation selected left right)
    (hbad : right.2.2.1.bad) :
    RevealProbeOracleSimulation.ObservedHit
      (filteredHighMonitoredProgramProjection right) := by
  exact MonitoredCausalState.bad_implies_runObserved right.1.1.2 right.2.2.1
    hrel.2.2 hbad

set_option maxRecDepth 1000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_program
    (adversary : Adversary Concrete.cappedScheme) (selected : ChainIndex) :
    RelTriple
      (sourceDirectTracedProgram adversary selected)
      (filteredHighMonitoredProgram adversary selected)
      (SourceFilteredHighMonitoredProgramRelation selected) := by
  unfold sourceDirectTracedProgram filteredHighMonitoredProgram
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_programmedWarmedFixedChainKeygen_uniformHigh_tree selected))
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightActual :=
    uniformCoupledWarmedFixedChainKeygenWithHigh_support_actual selected right
      hrightSupport
  apply relTriple_bind (relTriple_with_support
    (relTriple_sourceDirect_filteredHighMonitored_detailedExecution adversary
      selected left right hrel hleftSupport hrightActual))
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution.1,
    filteredHighMonitoredDetailedExecution_traceConsistent adversary
      (right.1.1, right.2) selected right.1.2 rightExecution
        hexecution.2.2⟩

end XmssSecurity.CappedChain
