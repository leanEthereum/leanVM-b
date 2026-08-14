import XmssSecurity.CausalWarmedHighIndependence
import XmssSecurity.CausalDirectReduction
import XmssSecurity.CausalTreeCacheCorrespondence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance eagerHighSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

set_option maxRecDepth 1000000 in
theorem evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
    (chain : ChainIndex) :
    evalDist (do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
      pure ((keyHigh.1, base), keyHigh.2)) =
    evalDist (coupledWarmedFixedChainKeygenWithBaseHigh chain) := by
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

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_uniformHigh
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        pure ((keyHigh.1, base), keyHigh.2))
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
  replayLeaves : LeafReplayOutputsCorrespond parameter left.secret
    right.1.1.secret left.cache right.1.1.cache

set_option maxHeartbeats 2400000 in
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
  obtain ⟨hvalues, leftEndpoints, rightEndpoints, hcache, hreplay⟩ :=
    htreeRelation
  have hleftReplay := treeValues_support_replay parameter
    (unflattenSecret leftMaterial.1.2) allTreeValueIndices
      leftMaterial.2.2 leftTree hleftTreeSupport
  have hrightReplay := treeValues_support_replay parameter
    (unflattenSecret rightMaterial.1.2) allTreeValueIndices
      rightMaterial.2.2 rightTree hrightTreeSupport
  have hroot := globalTreeValuesReplay_eq_root parameter
    (unflattenSecret leftMaterial.1.2) (unflattenSecret rightMaterial.1.2)
      leftTree.2 rightTree.2 leftTree.1 hleftReplay
        (hvalues ▸ hrightReplay)
  have hauth : ∀ epoch,
      Concrete.CacheReplay.authenticationPath leftTree.2
          ⟨parameter, unflattenSecret leftMaterial.1.2⟩ epoch =
        Concrete.CacheReplay.authenticationPath rightTree.2
          ⟨parameter, unflattenSecret rightMaterial.1.2⟩ epoch := by
    intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      (unflattenSecret leftMaterial.1.2) (unflattenSecret rightMaterial.1.2)
        leftTree.2 rightTree.2 leftTree.1 hleftReplay
          (hvalues ▸ hrightReplay) epoch
  have hleftCacheLe := treeValues_cache_le parameter
    (unflattenSecret leftMaterial.1.2) allTreeValueIndices
      leftMaterial.2.2 leftTree hleftTreeSupport
  apply relTriple_pure_pure
  refine ⟨?_, hcache.retained, hreplay⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨⟨htable, ?_, hvalues, hleftReplay, hrightReplay,
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

structure ProgrammedActualKeygenTreeCacheHighRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) : Prop where
  base : ProgrammedActualKeygenCacheHighRelation chain left right
  retained : HashCachesAgreeOn
    (TreeRetainedHashInput left.secretKey.parameter chain)
    left.cache right.1.1.cache
  replayLeaves : LeafReplayOutputsCorrespond left.secretKey.parameter
    left.secretKey.chainStart right.1.1.secretKey.chainStart
    left.cache right.1.1.cache

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
  rw [hparameter]
  unfold Concrete.CacheReplay.oneTimePublicKey
  rw [secret_eq_of_outsideChain_eq selected left.secretKey.chainStart
      right.1.1.secretKey.chainStart hrel.base.base.1.2.2.1 epoch candidate hne,
    Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
      left.secretKey.parameter selected candidate hne left.cache
        right.1.1.cache hrel.base.base.2 epoch]

set_option maxRecDepth 100000 in
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
  · simpa [CoupledWarmedKeygenView.toProgrammedView] using hview.replayLeaves

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
      (do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let keyHigh ← coupledWarmedFixedChainKeygenWithHigh chain
        pure ((keyHigh.1, base), keyHigh.2))
      (ProgrammedActualKeygenTreeCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_right
    (evalDist_uniform_coupledWarmedFixedChainKeygenWithHigh_eq_baseHigh
      chain).symm
  exact relTriple_programmedWarmedFixedChainKeygen_withBaseHigh_tree chain

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

noncomputable def filteredTreeProbingAttackerHashQueryAtFromHigh
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState) :=
  match chainInputProbe? secretKey.parameter selected input with
  | some probe => filteredProbingAttackerHashQueryAtFromHigh high secretKey
      selected input state (some probe)
  | none =>
      match leafInputProbe? secretKey.parameter selected input with
      | none => filteredProbingAttackerHashQueryAtFromHigh high secretKey
          selected input state none
      | some probe =>
          let answer := if LeafInputMatchesOutside secretKey state.keygenCache
              selected input then
            match state.keygenCache
                (keygenLeafTargetInput secretKey state.keygenCache input) with
              | some output => pure (output, state)
              | none => (causalHashQuery input).run state
          else
            (causalHashQuery input).run state
          match state.revealed probe.1 with
          | some value => if value = probe.2 then answer
              else (causalHashQuery input).run state
          | none => do
              let _ ← RevealProbeOracleSimulation.probeQuery probe.1 probe.2
              answer

theorem filteredTreeProbingAttackerHashQueryAtFromHigh_eq_of_chainProbe
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : ChainValueIndex × Digest)
    (hprobe : chainInputProbe? secretKey.parameter selected input =
      some probe) :
    filteredTreeProbingAttackerHashQueryAtFromHigh high secretKey selected
        input state =
      filteredProbingAttackerHashQueryAtFromHigh high secretKey selected
        input state (some probe) := by
  simp [filteredTreeProbingAttackerHashQueryAtFromHigh, hprobe]

noncomputable def filteredHighMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => causalUniformImpl n
    | .inl (.inr hashInput) => StateT.mk fun state =>
        filteredTreeProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state
    | .inr request => StateT.mk fun state =>
        filteredCausalSigningQuery keyHigh.1 selected request state

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

noncomputable def filteredHighVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl n => causalUniformImpl n
    | .inr hashInput => StateT.mk fun state =>
        filteredTreeProbingAttackerHashQueryAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state

noncomputable def filteredHighDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
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
    (Concrete.scheme.verify keyHigh.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
  pure ((handled.1, verified), handled.2)

abbrev FilteredHighDirectResult :=
  (ProgrammedFixedChainKeygenView × (ChainEdgeIndex → Digest)) ×
    FilteredDirectExecution

noncomputable def filteredHighDirectProgram
    (adversary : Adversary Concrete.scheme) (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredHighDirectResult := do
  let keyHigh ← RevealProbeOracleSimulation.liftProbComp
    (coupledWarmedFixedChainKeygenWithHigh selected)
  let execution ← (filteredHighDetailedGameAfterKeygen adversary keyHigh
    selected).run (filteredCausalKeygenState selected keyHigh.1)
  pure (keyHigh, execution)

noncomputable def boundedFilteredHighDirectProgram
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredHighDirectResult :=
  RevealProbeOracleSimulation.enforceProbeBound queries
    (filteredHighDirectProgram adversary selected)

theorem boundedFilteredHighDirectProgram_isProbeQueryBoundP
    (queries : Nat) (adversary : Adversary Concrete.scheme)
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

abbrev MonitoredTracedState := MonitoredCausalState × AttackerActionTrace

noncomputable def filteredHighMonitoredBaseMappedAdversaryImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT MonitoredCausalState ProbComp) :=
  fun input =>
    match input with
    | .inl (.inl n) => monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((causalUniformImpl n).run causalState)).run)
    | .inl (.inr hashInput) => monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (filteredTreeProbingAttackerHashQueryAtFromHigh
            (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
              hashInput causalState)).run)
    | .inr request => monitorCausalTrace table (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (filteredCausalSigningQuery keyHigh.1 selected request
            causalState)).run)

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

set_option maxRecDepth 100000 in
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
      filteredTreeProbingAttackerHashQueryAtFromHigh,
      unloggedMappedAdversaryImpl_apply_inl, xmssRomImpl,
      hprobeRight] using hcouple
  have hlift := relTriple_actionTracedState_until_bad
    (Sum.inl (Sum.inr input)) left.secretKey.parameter selected left.cache
      right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

set_option maxRecDepth 100000 in
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
  have hbase : RelTriple
      ((sourceDirectMappedAdversaryImpl left.publicKey left.secretKey
        (Sum.inr request)).run leftState.1)
      ((filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2 (Sum.inr request)).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∨
        rightResult.2.bad) := by
    simpa [sourceDirectMappedAdversaryImpl,
      filteredHighMonitoredBaseMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr] using hcouple
  have hlift := relTriple_actionTracedState_until_bad (Sum.inr request)
    left.secretKey.parameter selected left.cache right.1.1.cache right.1.2
      (sourceDirectMappedAdversaryImpl left.publicKey left.secretKey)
      (filteredHighMonitoredBaseMappedAdversaryImpl (right.1.1, right.2)
        selected right.1.2)
      leftState rightState hstate.2 hbase
  simpa [sourceDirectTracedMappedAdversaryImpl,
    filteredHighMonitoredMappedAdversaryImpl] using hlift

end XmssSecurity
