import SphincsSecurity.Proof.OtsProbeResolvedBoundaryFirstFire

/-!
# Private structural boundary outcome

This file factors the private structural projection of the detailed boundary game through a plain
Boolean interpreter. The projection is exact and retains the first-fire classification.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def classifyDirectPrivateObserve
    (_table : OtsSecretIndex → HashOutput)
    (_observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (_fuel : Nat) (_value : alpha) :
    ProbComp Bool := by
  classical
  exact if PrivateStructuralHit context then
      pure true
    else
      pure false

theorem evalDist_private_classifyDirectObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        classifyDirectObserve table observe context fuel value) =
      evalDist (classifyDirectPrivateObserve table observe context fuel value) := by
  unfold classifyDirectObserve classifyDirectPrivateObserve
  by_cases hprivate : PrivateStructuralHit context
  · simp [hprivate, DirectBoundaryOutcome.privateStructural]
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte, Functor.map_map]
      have hprojection :
          (fun output : Bool => (DirectBoundaryOutcome.ofFailed output).privateStructural) =
            fun _ => false := by
        funext output
        cases output <;> rfl
      rw [hprojection]
      change evalDist ((fun _ : Bool => false) <$> observe context fuel value) =
        evalDist (pure false : ProbComp Bool)
      simp only [map_eq_bind_pure_comp]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (observe context fuel value) (by simp) (pure false)
    · simp [hcompletable, DirectBoundaryOutcome.privateStructural]

noncomputable def finishDirectDetailedPrivateObserve
    (observe : DeferredContext → Nat → alpha → ProbComp Bool) :
    DirectDetailedResult alpha → ProbComp Bool
  | .stopped .privateStructuralHit => pure true
  | .stopped _ => pure false
  | .done result => observe result.context result.remaining result.value

noncomputable def classifyDirectDetailedPrivateObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp Bool := by
  classical
  exact if PrivateStructuralHit context then
      pure true
    else if DeferredCompletable table context then
      observe context fuel value
    else
      pure false

set_option maxRecDepth 100000 in
theorem probEvent_resolve_then_classifyDirectDetailedPrivateObserve_le
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (position : Position) (candidate : Digest)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (fuel : Nat) (value : alpha) (bound : ℝ≥0∞)
    (hclean : ¬PrivateStructuralHit context)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (hobserve : ∀ resolved : DeferredResolution,
      let nextContext : DeferredContext :=
        { resolved.toDeferredContext with
          state := resolved.state.addPending (.position position) candidate }
      ¬PrivateStructuralHit nextContext → DeferredCompletable table nextContext →
        Pr[= true | observe nextContext fuel value] ≤ bound) :
    Pr[= true | do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure false
      | some resolved =>
          classifyDirectDetailedPrivateObserve table observe
            { resolved.toDeferredContext with
              state := resolved.state.addPending (.position position) candidate }
            fuel value] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + bound := by
  classical
  let nextContext : DeferredResolution → DeferredContext := fun resolved =>
    { resolved.toDeferredContext with
      state := resolved.state.addPending (.position position) candidate }
  let fires : Option DeferredResolution → Prop
    | none => False
    | some resolved => PrivateStructuralHit (nextContext resolved)
  let continuation : Option DeferredResolution → ProbComp Bool
    | none => pure false
    | some resolved =>
        classifyDirectDetailedPrivateObserve table observe
          (nextContext resolved) fuel value
  rw [← probEvent_eq_eq_probOutput]
  refine (probEvent_bind_le_probEvent_add
    (mx := resolveDeferredPositionValue position context)
    (my := continuation)
    (q := fun hit : Bool => hit = true)
    (p := fires)
    (ε := bound) ?_).trans ?_
  · intro resolved _hresolved hmiss
    cases resolved with
    | none => simp [continuation]
    | some resolved =>
        have hnotPrivate : ¬PrivateStructuralHit (nextContext resolved) := by
          simpa [fires] using hmiss
        unfold continuation classifyDirectDetailedPrivateObserve
        simp only [hnotPrivate, ↓reduceIte]
        by_cases hcompletable : DeferredCompletable table (nextContext resolved)
        · simpa [hcompletable] using hobserve resolved hnotPrivate hcompletable
        · simp [hcompletable]
  · have hsource :
        Pr[fires | resolveDeferredPositionValue position context] ≤
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      have houtcome : resolveThenPrivateProbeOutcome context position candidate =
          (fun resolved => decide (fires resolved)) <$>
            resolveDeferredPositionValue position context := by
        unfold resolveThenPrivateProbeOutcome
        simp only [map_eq_bind_pure_comp]
        apply bind_congr
        intro resolved
        cases resolved <;> simp [fires, nextContext]
      exact calc
        Pr[fires | resolveDeferredPositionValue position context] =
            Pr[= true | resolveThenPrivateProbeOutcome context position candidate] := by
          rw [houtcome, ← probEvent_eq_eq_probOutput, probEvent_map]
          exact OracleComp.probEvent_congr' (fun resolved _ => by simp) rfl
        _ ≤ _ := probEvent_resolveThenPrivateProbeOutcome_le context position candidate
          hclean hhidden hprivate
    simpa [add_comm] using add_le_add_right hsource bound

theorem evalDist_private_classifyDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hproject : evalDist (DirectBoundaryOutcome.privateStructural <$>
        detailedObserve context fuel value) =
      evalDist (observe context fuel value)) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        classifyDirectDetailedObserve table detailedObserve context fuel value) =
      evalDist (classifyDirectDetailedPrivateObserve table observe context fuel value) := by
  unfold classifyDirectDetailedObserve classifyDirectDetailedPrivateObserve
  by_cases hprivate : PrivateStructuralHit context
  · simp [hprivate, DirectBoundaryOutcome.privateStructural]
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simpa [hcompletable] using hproject
    · simp [hcompletable, DirectBoundaryOutcome.privateStructural]

noncomputable def canonicalizeDirectDetailedPrivateObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp Bool := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure true
    else if PublishedValues context.state then
      classifyDirectDetailedPrivateObserve table observe
        (canonicalizeMaterializedValues table context) fuel value
    else
      pure false

theorem evalDist_private_canonicalizeDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hproject : evalDist (DirectBoundaryOutcome.privateStructural <$>
        detailedObserve (canonicalizeMaterializedValues table context) fuel value) =
      evalDist (observe (canonicalizeMaterializedValues table context) fuel value)) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        canonicalizeDirectDetailedObserve table detailedObserve context fuel value) =
      evalDist (canonicalizeDirectDetailedPrivateObserve table observe context fuel value) := by
  unfold canonicalizeDirectDetailedObserve canonicalizeDirectDetailedPrivateObserve
  by_cases hprivate : PrivateStructuralHit (canonicalizeMaterializedValues table context)
  · simp [hprivate, DirectBoundaryOutcome.privateStructural]
  · simp only [hprivate, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_private_classifyDirectDetailedObserve table detailedObserve observe
        (canonicalizeMaterializedValues table context) fuel value hproject
    · simp [hpublished, DirectBoundaryOutcome.privateStructural]

noncomputable def runDirectDetailedPrivateObserve
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp Bool :=
  runDirectResolvedDetailedFromTable context fuel table computation >>=
    finishDirectDetailedPrivateObserve observe

theorem evalDist_runDirectDetailedPrivateObserve_bind
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (observe : DeferredContext → Nat → β → ProbComp Bool)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist
      (runDirectDetailedPrivateObserve observe context fuel table (left >>= next)) =
    evalDist (runDirectResolvedDetailedFromTable context fuel table left >>=
      finishDirectDetailedPrivateObserve
        (fun nextContext remaining value =>
          runDirectDetailedPrivateObserve observe nextContext remaining table
            (next value))) := by
  unfold runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result =>
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        left context fuel table result hresult
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
        left context fuel table result hconsistent hstarts hdirect
      simp [finishDirectDetailedPrivateObserve, hcore.1]

theorem evalDist_private_runDirectDetailedObserve
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (hproject : ∀ result,
      DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable context fuel table computation) →
        evalDist (DirectBoundaryOutcome.privateStructural <$>
            detailedObserve result.context result.remaining result.value) =
          evalDist (observe result.context result.remaining result.value)) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        runDirectDetailedObserve detailedObserve context fuel table computation) =
      evalDist (runDirectDetailedPrivateObserve observe context fuel table computation) := by
  unfold runDirectDetailedObserve runDirectDetailedPrivateObserve
  rw [map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | stopped reason =>
      cases reason <;> rfl
  | done result =>
      exact hproject result hresult

noncomputable def directDetailedBoundaryPrivateObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec alpha =>
      (DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool) →
        DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp Bool)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      runDirectDetailedPrivateObserve
        (canonicalizeDirectDetailedPrivateObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2))
        context fuel table ((impl query).run cache))
    computation observe context fuel table cache

set_option maxRecDepth 100000 in
theorem evalDist_private_directDetailedBoundaryObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (detailedObserve : DeferredContext → Nat → (alpha × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (hobserve : ∀ context fuel value,
      evalDist (DirectBoundaryOutcome.privateStructural <$>
          detailedObserve context fuel value) =
        evalDist (observe context fuel value))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        directDetailedBoundaryObserve impl computation detailedObserve context fuel table cache) =
      evalDist (directDetailedBoundaryPrivateObserve impl computation observe
        context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryObserve, OracleComp.construct_pure,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_pure]
      exact hobserve context fuel (value, cache)
  | query_bind query next ih =>
      rw [directDetailedBoundaryObserve, OracleComp.construct_query_bind,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_query_bind]
      apply evalDist_private_runDirectDetailedObserve
      intro result _hresult
      apply evalDist_private_canonicalizeDirectDetailedObserve
      exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
        result.remaining result.value.2

noncomputable def directDetailedVerifierFinishPrivateObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    ProbComp Bool :=
  runDirectDetailedPrivateObserve
    (classifyDirectPrivateObserve table (fun _ _ _ => pure false))
    context fuel table ((canonicalVerifierFinish parameter root value.1).run value.2)

theorem evalDist_private_directDetailedVerifierFinishObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        directDetailedVerifierFinishObserve table parameter root context fuel value) =
      evalDist (directDetailedVerifierFinishPrivateObserve table parameter root
        context fuel value) := by
  unfold directDetailedVerifierFinishObserve directDetailedVerifierFinishPrivateObserve
  apply evalDist_private_runDirectDetailedObserve
  intro result _hresult
  exact evalDist_private_classifyDirectObserve table (resolvedFinalizationObserve table)
    result.context result.remaining result.value

noncomputable def allDirectDetailedRetainedRestPrivateObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryPrivateObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
    (directDetailedVerifierFinishPrivateObserve table parameter value.1)
    context fuel table value.2

theorem evalDist_private_allDirectDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        allDirectDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (allDirectDetailedRetainedRestPrivateObserve adversary parameter table
        ftsSecret context fuel value) := by
  unfold allDirectDetailedRetainedRestObserve allDirectDetailedRetainedRestPrivateObserve
  apply evalDist_private_directDetailedBoundaryObserve
  intro nextContext remaining nextValue
  exact evalDist_private_directDetailedVerifierFinishObserve table parameter value.1
    nextContext remaining nextValue

noncomputable def allDirectBoundaryDetailedRetainedPrivate
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedPrivateObserve
    (allDirectDetailedRetainedRestPrivateObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_private_allDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        allDirectBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel) =
      evalDist (allDirectBoundaryDetailedRetainedPrivate adversary parameter table
        ftsSecret fuel) := by
  unfold allDirectBoundaryDetailedRetainedOutcome allDirectBoundaryDetailedRetainedPrivate
  apply evalDist_private_runDirectDetailedObserve
  intro result _hresult
  exact evalDist_private_allDirectDetailedRetainedRestObserve adversary parameter table ftsSecret
    result.context result.remaining result.value

noncomputable def sampledAllDirectBoundaryDetailedRetainedPrivate
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  allDirectBoundaryDetailedRetainedPrivate adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_private_sampledAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel) =
      evalDist (sampledAllDirectBoundaryDetailedRetainedPrivate adversary parameter
        ftsSecret fuel) := by
  unfold sampledAllDirectBoundaryDetailedRetainedOutcome
    sampledAllDirectBoundaryDetailedRetainedPrivate
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_private_allDirectBoundaryDetailedRetainedOutcome adversary parameter table
    ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_privateStructuralFailure_sampledAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= .privateStructuralFailure |
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] =
      Pr[= true |
        sampledAllDirectBoundaryDetailedRetainedPrivate adversary parameter ftsSecret fuel] := by
  rw [probEvent_privateStructuralFailure_eq_map_privateStructural]
  exact OracleComp.probOutput_congr rfl
    (evalDist_private_sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter
      ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
