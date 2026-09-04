import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonSampling

/-!
# Sampling commute through the detailed selector

Revealed coordinates grow monotonically through the permissive interpreter and selector. This
discharges the administrative already-revealed branch before the one-cell factorization is lifted
through the target-independent outer computation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem revealed_subset_of_mem_runPermissiveFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (hresult : some result ∈ support
      (runPermissiveFromTable state fuel table computation)) :
    state.revealed ⊆ result.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runPermissiveFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact Finset.Subset.rfl
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runPermissiveFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel htail
      | hashOutput =>
          rw [runPermissiveFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel htail
      | ensure coordinate =>
          rw [runPermissiveFromTable_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel hresult
      | probe coordinate candidate =>
          rw [runPermissiveFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () state remaining hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () (state.addPending coordinate candidate) remaining hresult
      | peek coordinate =>
          rw [runPermissiveFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hresult
      | publish coordinate =>
          rw [runPermissiveFromTable_publish_query_bind] at hresult
          exact (Finset.subset_insert coordinate state.revealed).trans
            (ih () (state.publish coordinate) fuel hresult)
      | reveal coordinate =>
          rw [runPermissiveFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output state fuel hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih (table ⟨lay, tree, leafIdx, chainIdx⟩)
                    (state.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)) fuel hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, htail⟩ := hresult
                  exact ih output (state.materialize (.position position) output) fuel htail

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem revealed_subset_of_mem_permissiveDetailedRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    state.revealed ⊆ selection.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact Finset.Subset.rfl
      · simp [hselected] at hselection
  | query_bind query next ih =>
      rw [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind] at hselection
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hselection
        simp at hselection
        subst selection
        exact Finset.Subset.rfl
      · simp only [hselected, ↓reduceDIte] at hselection
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at hselection
                obtain ⟨result, hresult, htail⟩ := hselection
                cases result with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                | some result =>
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                    exact (revealed_subset_of_mem_runPermissiveFromTable
                      ((splitUniformImpl n).run cache) state fuel table result hresult).trans
                      (ih result.value.1 candidates result.state result.remaining result.value.2
                        htail)
            | inr input =>
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  simp at hselection
                  subst selection
                  exact Finset.Subset.rfl
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte] at hselection
                  rw [mem_support_bind_iff] at hselection
                  obtain ⟨result, hresult, htail⟩ := hselection
                  cases result with
                  | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                  | some result =>
                      simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                      exact (revealed_subset_of_mem_runPermissiveFromTable
                        (permissiveRootAwarePublicAction parameter input table state cache)
                        state fuel table result hresult).trans
                        (ih result.value.1 nextCandidates result.state result.remaining
                          result.value.2 htail)
        | inr message =>
            rw [mem_support_bind_iff] at hselection
            obtain ⟨result, hresult, htail⟩ := hselection
            cases result with
            | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at htail
            | some result =>
                simp only [finishPermissiveDetailedPrivateOrdinalSelection] at htail
                exact (revealed_subset_of_mem_runPermissiveFromTable
                  ((maskedSign parameter root ftsSecret message).run cache)
                  state fuel table result hresult).trans
                  (ih result.value.1 candidates result.state result.remaining result.value.2 htail)

theorem unrevealedLayerRootPosition_ne_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (htarget : Coordinate.position target ∈ state.revealed)
    (selection : Option PermissivePrivateOrdinalSelection)
    (hselection : selection ∈ support
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ some target := by
  cases selection with
  | none => simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some selection =>
      intro heq
      rw [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff] at heq
      obtain ⟨selected, hselected, _hcandidate, hunrevealed⟩ := heq
      cases hselected
      exact hunrevealed
        (revealed_subset_of_mem_permissiveDetailedRootAwareOrdinalSelection ordinal parameter root
          ftsSecret computation candidates state fuel table cache selection hselection htarget)

def PermissiveTargetFiberRel (target : Position) :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop :=
  fun left right =>
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left = some target →
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target

theorem relTriple_permissiveDetailedRootAwareOrdinalSelection_targetFiber_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates left fuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates right fuel table cache)
      (PermissiveTargetFiberRel target) := by
  apply relTriple_post_mono
    (relTriple_permissiveDetailedRootAwareOrdinalSelection_of_stateRel ordinal parameter root
      ftsSecret computation candidates candidates left right fuel table cache rfl hstate)
  intro leftSelection rightSelection hselection hleft
  rw [hselection.positionFiber_eq] at hleft
  exact hleft

theorem relTriple_sample_preload_runPermissive_finishDetailed
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe →
        ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0)
    (hpreloaded : ∀ nextState remaining value nextCache,
      nextState.values (.position target) = none →
      RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          leftObserve (preloadPositionValue target output nextState) remaining value nextCache
            candidates)
        (rightObserve nextState remaining value nextCache candidates)
        (PermissiveTargetFiberRel target))
    (hsynchronized : ∀ left right remaining value cache,
      PermissiveStateRel left right →
      RelTriple
        (leftObserve left remaining value cache candidates)
        (rightObserve right remaining value cache candidates)
        (PermissiveTargetFiberRel target)) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        runPermissiveFromTable (preloadPositionValue target output state) fuel table computation >>=
          finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates)
      (runPermissiveFromTable state fuel table computation >>=
        finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates)
      (PermissiveTargetFiberRel target) := by
  apply relTriple_sample_preload_runPermissiveFromTable_then target computation state fuel table
    (finishPermissiveDetailedPrivateOrdinalSelection leftObserve candidates)
    (finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates)
    (PermissiveTargetFiberRel target) hvalue hnoPeek
  · intro nextState remaining result nextTable hnextValue
    rcases result with ⟨value, nextCache⟩
    simp only [finishPermissiveDetailedPrivateOrdinalSelection]
    exact hpreloaded nextState remaining value nextCache hnextValue
  · intro left right hresult
    cases left with
    | none =>
        cases right with
        | none => simp [finishPermissiveDetailedPrivateOrdinalSelection,
            PermissiveTargetFiberRel]
        | some right => exact False.elim hresult
    | some left =>
        cases right with
        | none => exact False.elim hresult
        | some right =>
            rcases hresult with ⟨hstate, hremaining, hvalue, htable⟩
            have hvalueEq := congrArg Prod.fst hvalue
            have hcacheEq := congrArg Prod.snd hvalue
            simp only [finishPermissiveDetailedPrivateOrdinalSelection]
            rw [← hremaining, ← hvalueEq, ← hcacheEq]
            exact hsynchronized left.state right.state left.remaining left.value.1
              left.value.2 hstate

theorem relTriple_sample_preload_selector_targetFiber_of_initial_revealed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hrevealed : Coordinate.position target ∈ state.revealed) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetFiberRel target) := by
  have hbase := relTriple_true
    (LazyRevealProbe.sampleHashOutput >>= fun output =>
      permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates (preloadPositionValue target output state) fuel table cache)
    (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
      candidates state fuel table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun selection =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ some target)
      (by
        intro selection hselection
        rw [mem_support_bind_iff] at hselection
        obtain ⟨output, _houtput, htail⟩ := hselection
        exact unrevealedLayerRootPosition_ne_of_initial_revealed ordinal parameter root ftsSecret
          computation candidates (preloadPositionValue target output state) fuel table cache target
          (by simpa using hrevealed) selection htail)
  apply relTriple_post_mono hleft
  intro left right hrelation hfiber
  exact False.elim (hrelation.2 hfiber)

theorem permissiveRootAwarePlan_preload_hidden
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) :
    permissiveRootAwarePlan parameter input table (preloadPositionValue target output state) =
      permissiveRootAwarePlan parameter input table state := by
  unfold permissiveRootAwarePlan
  exact purePlanProbingHashQuery_eq_of_values_eq
    (materializedCanonicalContext_values_preload_hidden table state target output hhidden)
    parameter input

theorem permissiveRootAwareCandidates_preload_hidden
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (candidates : List Probe) :
    permissiveRootAwareCandidates parameter input table
        (preloadPositionValue target output state) candidates =
      permissiveRootAwareCandidates parameter input table state candidates := by
  unfold permissiveRootAwareCandidates
  rw [permissiveRootAwarePlan_preload_hidden target output state hhidden]

theorem permissiveRootAwarePublicAction_preload_hidden
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    permissiveRootAwarePublicAction parameter input table
        (preloadPositionValue target output state) cache =
      permissiveRootAwarePublicAction parameter input table state cache := by
  unfold permissiveRootAwarePublicAction
  have hvalues :=
    materializedCanonicalContext_values_preload_hidden table state target output hhidden
  have hplan := permissiveRootAwarePlan_preload_hidden target output state hhidden parameter
    input table
  calc
    _ = permissiveRootAwarePublicActionWithPlan parameter input
          (materializedCanonicalContext table state).state
          (permissiveRootAwarePlan parameter input table
            (preloadPositionValue target output state)) cache :=
      permissiveRootAwarePublicActionWithPlan_eq_of_values_eq parameter input hvalues _ cache
    _ = _ := by rw [hplan]

theorem permissiveTargetFiberRel_preload_sameSelection
    (target : Position) (candidate : Probe) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (output : HashOutput) :
    PermissiveTargetFiberRel target
      (some ⟨candidate, preloadPositionValue target output state, candidates⟩)
      (some ⟨candidate, state, candidates⟩) := by
  intro hleft
  rw [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff] at hleft ⊢
  obtain ⟨selected, hselected, hcandidate, hunrevealed⟩ := hleft
  cases Option.some.inj hselected
  exact ⟨⟨candidate, state, candidates⟩, rfl, hcandidate, by
    simpa only [preloadPositionValue_revealed] using hunrevealed⟩

theorem relTriple_sample_preload_pureSelection_targetFiber
    (target : Position) (candidate : Probe) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        pure (some ⟨candidate, preloadPositionValue target output state, candidates⟩))
      (pure (some ⟨candidate, state, candidates⟩) :
        ProbComp (Option PermissivePrivateOrdinalSelection))
      (PermissiveTargetFiberRel target) := by
  rw [show (pure (some ⟨candidate, state, candidates⟩) :
      ProbComp (Option PermissivePrivateOrdinalSelection)) =
        (pure () >>= fun _ => pure (some ⟨candidate, state, candidates⟩)) by simp]
  apply relTriple_bind
    (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
  intro output _ _
  exact relTriple_pure_pure
    (permissiveTargetFiberRel_preload_sameSelection target candidate candidates state output)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sample_preload_permissiveDetailedRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (hvalue : state.values (.position target) = none) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
          candidates (preloadPositionValue target output state) fuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)
      (PermissiveTargetFiberRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_selector_targetFiber_of_initial_revealed ordinal
          parameter root ftsSecret (pure value) candidates state fuel table cache target hrevealed
      · simp only [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetFiber target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          apply relTriple_of_evalDist_eq_left
            (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
              LazyRevealProbe.sampleHashOutput (by
                simp [LazyRevealProbe.sampleHashOutput]) (pure none))
          exact relTriple_pure_pure (by simp [PermissiveTargetFiberRel])
  | query_bind query next ih =>
      by_cases hrevealed : Coordinate.position target ∈ state.revealed
      · exact relTriple_sample_preload_selector_targetFiber_of_initial_revealed ordinal
          parameter root ftsSecret (liftM (OracleSpec.query query) >>= next) candidates state fuel
          table cache target hrevealed
      · simp_rw [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind]
        by_cases hselected : ordinal < candidates.length
        · simp only [hselected, ↓reduceDIte]
          exact relTriple_sample_preload_pureSelection_targetFiber target
            (candidates.get ⟨ordinal, hselected⟩) candidates state
        · simp only [hselected, ↓reduceDIte]
          cases query with
          | inl worldQuery =>
              cases worldQuery with
              | inl n =>
                  let observe : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  apply relTriple_sample_preload_runPermissive_finishDetailed target
                    ((splitUniformImpl n).run cache) state fuel table observe observe candidates
                    hvalue (splitUniformImpl_targetPeekFree target n cache)
                  · intro nextState remaining output nextCache hnextValue
                    simpa only [observe] using
                      ih output candidates nextState remaining nextCache hnextValue
                  · intro left right remaining output nextCache hstate
                    exact
                      relTriple_permissiveDetailedRootAwareOrdinalSelection_targetFiber_of_stateRel
                        ordinal parameter root ftsSecret (next output) candidates left right
                        remaining table nextCache target hstate
              | inr input =>
                  let nextCandidates :=
                    permissiveRootAwareCandidates parameter input table state candidates
                  by_cases hnextSelected : ordinal < nextCandidates.length
                  · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    rw [show (pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩) :
                        ProbComp (Option PermissivePrivateOrdinalSelection)) =
                      (pure () >>= fun _ => pure (some
                        ⟨(permissiveRootAwareCandidates parameter input table state candidates).get
                            ⟨ordinal, hnextSelected⟩,
                          state,
                          permissiveRootAwareCandidates parameter input table state candidates⟩)) by simp]
                    apply relTriple_bind
                      (relTriple_true LazyRevealProbe.sampleHashOutput (pure () : ProbComp Unit))
                    intro output _ _
                    rw [permissiveRootAwareCandidates_preload_hidden target output state hrevealed
                      parameter input table candidates]
                    have hnextSelected' : ordinal <
                        (permissiveRootAwareCandidates parameter input table state candidates).length :=
                      hnextSelected
                    rw [dif_pos hnextSelected']
                    exact relTriple_pure_pure
                      (permissiveTargetFiberRel_preload_sameSelection target
                        ((permissiveRootAwareCandidates parameter input table state candidates).get
                          ⟨ordinal, hnextSelected⟩)
                        (permissiveRootAwareCandidates parameter input table state candidates)
                        state output)
                  · simp_rw [permissiveRootAwareCandidates_preload_hidden target _ state hrevealed
                      parameter input table candidates]
                    simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                    simp_rw [permissiveRootAwarePublicAction_preload_hidden target _ state hrevealed
                      parameter input table cache]
                    let observe : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe →
                          ProbComp (Option PermissivePrivateOrdinalSelection) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        permissiveDetailedRootAwareOrdinalSelection ordinal parameter root
                          ftsSecret (next output) laterCandidates nextState remaining table nextCache
                    apply relTriple_sample_preload_runPermissive_finishDetailed target
                      (permissiveRootAwarePublicAction parameter input table state cache)
                      state fuel table observe observe nextCandidates hvalue
                      (permissiveRootAwarePublicAction_targetPeekFree target parameter input table
                        state cache)
                    · intro nextState remaining output nextCache hnextValue
                      simpa only [observe] using
                        ih output nextCandidates nextState remaining nextCache hnextValue
                    · intro left right remaining output nextCache hstate
                      exact
                        relTriple_permissiveDetailedRootAwareOrdinalSelection_targetFiber_of_stateRel
                          ordinal parameter root ftsSecret (next output) nextCandidates left right
                          remaining table nextCache target hstate
          | inr message =>
              let observe : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                  SplitHashCache → List Probe →
                    ProbComp (Option PermissivePrivateOrdinalSelection) :=
                fun nextState remaining output nextCache laterCandidates =>
                  permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
                    (next output) laterCandidates nextState remaining table nextCache
              apply relTriple_sample_preload_runPermissive_finishDetailed target
                ((maskedSign parameter root ftsSecret message).run cache) state fuel table
                observe observe candidates hvalue
                (maskedSign_targetPeekFree target parameter root ftsSecret message cache)
              · intro nextState remaining output nextCache hnextValue
                simpa only [observe] using
                  ih output candidates nextState remaining nextCache hnextValue
              · intro left right remaining output nextCache hstate
                exact
                  relTriple_permissiveDetailedRootAwareOrdinalSelection_targetFiber_of_stateRel
                    ordinal parameter root ftsSecret (next output) candidates left right remaining
                    table nextCache target hstate

end SphincsSecurity.Concrete.OtsProbeSimulation
