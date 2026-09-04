import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalNonRootRisk

/-!
# Root-aware comparison probe

The delayed comparison schedule executes the root-aware candidate selected from one outer hash
query. When the ordinary structural planner already selected a candidate this is the existing
planned suffix. Otherwise an encoding-domain layer-root guess is installed as one proof-only probe
before the same probe-free action.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def rootAwareCandidateForPlan?
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) : Option Probe :=
  match plan.candidate? with
  | some candidate => some candidate
  | none => decodeEncodingLayerRootCandidate? parameter input

theorem rootAwareCandidateForPlan?_purePlan
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) :
    rootAwareCandidateForPlan? parameter input
        (purePlanProbingHashQuery parameter input state) =
      rootAwarePlannedCandidate? parameter input state := by
  rfl

noncomputable def probingHashQueryAfterRootAwarePlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  executeCandidate? (rootAwareCandidateForPlan? parameter input plan)
  match plan.action with
  | .ordinary => splitHashQuery (.ordinary input)
  | .resolve coordinate => resolveKnownInput parameter coordinate input

theorem probingHashQueryAfterRootAwarePlan_eq_afterPlan_of_candidate
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery)
    (candidate : Probe) (hcandidate : plan.candidate? = some candidate) :
    probingHashQueryAfterRootAwarePlan parameter input plan =
      probingHashQueryAfterPlan parameter input plan := by
  unfold probingHashQueryAfterRootAwarePlan probingHashQueryAfterPlan
    executePlannedHashQuery rootAwareCandidateForPlan?
  rw [hcandidate]
  cases plan.action <;> rfl

theorem probingHashQueryAfterRootAwarePlan_eq_probe_then_afterPlan
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery)
    (candidate : Probe) (hplan : plan.candidate? = none)
    (hdecode : decodeEncodingLayerRootCandidate? parameter input = some candidate) :
    probingHashQueryAfterRootAwarePlan parameter input plan = (do
      probe candidate
      probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterRootAwarePlan probingHashQueryAfterPlan
    executePlannedHashQuery rootAwareCandidateForPlan?
  rw [hplan, hdecode]
  cases plan.action <;> rfl

theorem rootAwarePlannedCandidate?_isLayerRoot_of_plan_none
    {parameter : PublicParameter} {input : HashInput}
    {plan : PlannedHashQuery}
    {candidate : Probe} (hplan : plan.candidate? = none)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate) :
    candidate.IsLayerRoot := by
  unfold rootAwareCandidateForPlan? at hcandidate
  rw [hplan] at hcandidate
  exact decodeEncodingLayerRootCandidate?_some_isLayerRoot hcandidate

theorem rootAwarePlannedCandidate?_hasParent_of_plan_none
    {parameter : PublicParameter} {input : HashInput}
    {plan : PlannedHashQuery}
    {candidate : Probe} (hplan : plan.candidate? = none)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate) :
    candidate.HasStructuralParent := by
  unfold rootAwareCandidateForPlan? at hcandidate
  rw [hplan] at hcandidate
  exact encodingLayerRootCandidateAt_hasStructuralParent
    ((decodeEncodingLayerRootCandidate?_eq_some_iff parameter input candidate).mp hcandidate)

theorem executeCandidate?_isProbeBound_one (candidate? : Option Probe)
    (cache : SplitHashCache) :
    ((executeCandidate? candidate?).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  cases candidate? with
  | none => simp [executeCandidate?]
  | some candidate =>
      change ((probe candidate).run cache).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
      unfold probe
      simp only [StateT.run_liftM]
      exact LazyRevealProbe.probeQuery_isProbeBound candidate.coordinate candidate.candidate

theorem probingHashQueryAfterRootAwarePlan_isProbeBound
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery) (cache : SplitHashCache) :
    ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probingHashQueryAfterRootAwarePlan
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
  · exact executeCandidate?_isProbeBound_one
      (rootAwareCandidateForPlan? parameter input plan) cache
  · intro result _hresult
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree (.ordinary input) result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem preservesPublishedValues_probingHashQueryAfterRootAwarePlan
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery) :
    PreservesPublishedValues
      (probingHashQueryAfterRootAwarePlan parameter input plan) := by
  unfold probingHashQueryAfterRootAwarePlan
  apply (preservesPublishedValues_executeCandidate
    (rootAwareCandidateForPlan? parameter input plan)).bind
  intro _
  cases plan.action with
  | ordinary => exact preservesPublishedValues_splitHashQuery_ordinary input
  | resolve coordinate => exact preservesPublishedValues_resolveKnownInput parameter coordinate input

set_option maxRecDepth 100000 in
theorem probingHashQuery_eq_plan_then_afterPlan
    (parameter : PublicParameter) (input : HashInput) :
    probingHashQuery parameter input = (do
      let plan ← planProbingHashQuery parameter input
      probingHashQueryAfterPlan parameter input plan) := by
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
            candidate hprobe (by
              rintro ⟨lay, tree, leafIdx, heq⟩
              simp [hposition] at heq)
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact probingHashQuery_eq_plan_then_afterPlan_leaf parameter input candidate lay
                tree leafIdx hprobe hposition
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
                candidate hprobe (by
                  rintro ⟨lay, tree, leafIdx, heq⟩
                  simp [hposition] at heq)
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input
            hprobe (by
              rintro ⟨lay, tree, level, nodeIdx, heq⟩
              simp [hposition] at heq)
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              exact probingHashQuery_eq_plan_then_afterPlan_node parameter input lay tree level
                nodeIdx hprobe hposition
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input
                hprobe (by
                  rintro ⟨lay, tree, level, nodeIdx, heq⟩
                  simp [hposition] at heq)

noncomputable def rootAwareProbingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  let plan ← planProbingHashQuery parameter input
  probingHashQueryAfterRootAwarePlan parameter input plan

theorem rootAwareProbingHashQuery_isProbeBound
    (parameter : PublicParameter) (input : HashInput) (cache : SplitHashCache) :
    ((rootAwareProbingHashQuery parameter input).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold rootAwareProbingHashQuery
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
  · exact planProbingHashQuery_probeFree parameter input cache
  · intro result _hresult
    exact probingHashQueryAfterRootAwarePlan_isProbeBound parameter input result.1 result.2

noncomputable def rootAwareProbingHashImpl (parameter : PublicParameter) :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun input => rootAwareProbingHashQuery parameter input

noncomputable def rootAwareProbingRomImpl (parameter : PublicParameter) :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + rootAwareProbingHashImpl parameter

theorem rootAwareProbingRomImpl_step_isProbeBound
    (parameter : PublicParameter) (query : OracleWorld.Domain) (cache : SplitHashCache) :
    ((rootAwareProbingRomImpl parameter query).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate))
        (if query matches .inr _ then 1 else 0) := by
  cases query with
  | inl n =>
      simpa [rootAwareProbingRomImpl] using splitUniformImpl_probeFree n cache
  | inr input =>
      change ((rootAwareProbingHashQuery parameter input).run cache).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
      exact rootAwareProbingHashQuery_isProbeBound parameter input cache

noncomputable def rootAwareMaskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  rootAwareProbingRomImpl parameter + maskedSigningImpl parameter root ftsSecret

theorem rootAwareMaskedExpandedAdversaryImpl_step_isProbeBound
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache) :
    ((rootAwareMaskedExpandedAdversaryImpl parameter root ftsSecret query).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate))
        (if IsOuterHash query then 1 else 0) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          simpa [rootAwareMaskedExpandedAdversaryImpl, rootAwareProbingRomImpl,
            IsOuterHash] using splitUniformImpl_probeFree n cache
      | inr input =>
          change ((rootAwareProbingHashQuery parameter input).run cache).IsQueryBoundP
            (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
          exact rootAwareProbingHashQuery_isProbeBound parameter input cache
  | inr message =>
      simpa [rootAwareMaskedExpandedAdversaryImpl, maskedSigningImpl, IsOuterHash] using
        maskedSign_probeFree parameter root ftsSecret message cache

theorem simulateQ_rootAwareMaskedExpandedAdversaryImpl_run_isProbeBound
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash q)
    (cache : SplitHashCache) :
    ((simulateQ (rootAwareMaskedExpandedAdversaryImpl parameter root ftsSecret)
      computation).run cache).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  apply hbound.simulateQ_run_StateT_of_step
    (q := LazyRevealProbe.IsProbe (Coordinate := Coordinate))
  exact rootAwareMaskedExpandedAdversaryImpl_step_isProbeBound parameter root ftsSecret

noncomputable def rootAwareCleanRetainedRun
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedGameResult × SplitHashCache) := do
  let rootResult ← maskedPublishedTreeRoot.run emptySplitHashCache
  let restResult ←
    (simulateQ
      (rootAwareMaskedExpandedAdversaryImpl parameter rootResult.1 ftsSecret)
      (retainedGameRestComputation adversary ⟨rootResult.1, parameter⟩)).run rootResult.2
  pure ((rootResult.1, restResult.1), restResult.2)

set_option maxRecDepth 100000 in
theorem rootAwareCleanRetainedRun_isProbeBound
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    (rootAwareCleanRetainedRun adversary parameter ftsSecret).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  unfold rootAwareCleanRetainedRun
  have htail : ∀ rootResult ∈ support (maskedPublishedTreeRoot.run emptySplitHashCache),
      (do
        let restResult ←
          (simulateQ
            (rootAwareMaskedExpandedAdversaryImpl parameter rootResult.1 ftsSecret)
            (retainedGameRestComputation adversary ⟨rootResult.1, parameter⟩)).run rootResult.2
        pure ((rootResult.1, restResult.1), restResult.2)).IsQueryBoundP
          (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
    intro rootResult _hroot
    change ((fun restResult => ((rootResult.1, restResult.1), restResult.2)) <$>
      (simulateQ
        (rootAwareMaskedExpandedAdversaryImpl parameter rootResult.1 ftsSecret)
        (retainedGameRestComputation adversary ⟨rootResult.1, parameter⟩)).run
          rootResult.2).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q
    rw [OracleComp.isQueryBoundP_map_iff]
    exact simulateQ_rootAwareMaskedExpandedAdversaryImpl_run_isProbeBound parameter
      rootResult.1 ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.1, parameter⟩) q
      (hbound rootResult.1) rootResult.2
  simpa only [Nat.zero_add] using OracleComp.isQueryBoundP_bind
    (n := 0) (m := q) (maskedPublishedTreeRoot_probeFree emptySplitHashCache) htail

theorem probEvent_rootAwareCleanRetainedRun_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    Pr[fun hit : Bool => hit = true |
        LazyRevealProbe.experiment
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
          (rootAwareCleanRetainedRun adversary parameter ftsSecret)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  LazyRevealProbe.experiment_empty_probability_le q
    (rootAwareCleanRetainedRun adversary parameter ftsSecret)

theorem probEvent_sampledRootAwareCleanRetainedRun_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (rootAwareCleanRetainedRun adversary parameter ftsSecret)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledRunThenFinalizeClean_empty_none_le
    (rootAwareCleanRetainedRun adversary parameter ftsSecret) q
    (rootAwareCleanRetainedRun_isProbeBound adversary parameter ftsSecret q hbound)

end SphincsSecurity.Concrete.OtsProbeSimulation
