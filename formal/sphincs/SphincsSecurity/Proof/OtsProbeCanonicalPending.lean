import SphincsSecurity.Proof.OtsProbePrehitOpeningProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem pendingCoveredBy_of_mem_runResolvedFromTable
    (candidates : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    PendingCoveredBy candidates result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | probe coordinate digest =>
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runResolvedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hcovered htail hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () { context with state := context.state.addPending coordinate digest }
                  remaining (hcovered.addPending_of_mem ⟨coordinate, digest⟩ hmem) htail hresult
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hcovered (hbound.2 _) hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨option, _hresolve, htail⟩ := hresult
            cases option with
            | none => simp at htail
            | some resolved =>
                apply ih resolved.output _ fuel _ (hbound.2 resolved.output) htail
                exact hcovered.of_subset (Finset.filter_subset _ _)

theorem runResolvedFromTable_peekCoordinate
    (coordinate : Coordinate) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((peekCoordinate coordinate).run cache) =
      pure (some ⟨context, fuel, ((context.state.values coordinate).map truncateHash, cache), table⟩) := by
  change runResolvedFromTable context fuel table
    (LazyRevealProbe.peekQuery coordinate >>= fun result => pure (result.map truncateHash, cache)) = _
  rw [LazyRevealProbe.peekQuery, runResolvedFromTable_peek_query_bind]
  rfl

theorem runResolved_planFirstMissingInputCoordinate
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) :
    ∀ slot coordinates context fuel table cache,
      context.state = state →
      runResolvedFromTable context fuel table
          ((planFirstMissingInputCoordinate input slot coordinates).run cache) =
        pure (some ⟨context, fuel,
          (firstMissingInputCoordinatePlan state input slot coordinates, cache), table⟩) := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil =>
      intro context fuel table cache hstate
      simp [planFirstMissingInputCoordinate, firstMissingInputCoordinatePlan,
        runResolvedFromTable]
  | cons coordinate remaining ih =>
      intro context fuel table cache hstate
      rw [planFirstMissingInputCoordinate, StateT.run_bind,
        runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate]
      simp only [pure_bind]
      rw [hstate]
      cases hvalue : state.values coordinate with
      | none =>
          simp [hvalue, firstMissingInputCoordinatePlan,
            runResolvedFromTable]
      | some output =>
          change runResolvedFromTable context fuel table
            ((planFirstMissingInputCoordinate input (slot + 1) remaining).run cache) = _
          rw [ih (slot + 1) context fuel table cache hstate]
          simp [firstMissingInputCoordinatePlan, hvalue]

theorem runResolved_planLeafInputProbe
    (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runResolvedFromTable context fuel table
        ((planLeafInputProbe input candidate lay tree leafIdx).run cache) =
      pure (some ⟨context, fuel,
        (leafInputProbePlan state input candidate lay tree leafIdx, cache), table⟩) := by
  rw [planLeafInputProbe, StateT.run_bind,
    runResolvedFromTable_bind,
    runResolvedFromTable_peekCoordinate]
  simp only [pure_bind]
  rw [hstate]
  cases hvalue : state.values candidate.coordinate with
  | none =>
      simp [hvalue, leafInputProbePlan, runResolvedFromTable]
  | some output =>
      change runResolvedFromTable context fuel table
        ((planFirstMissingInputCoordinate input 0
          ((Position.leaf lay tree leafIdx).children.map Coordinate.position)).run cache) = _
      rw [runResolved_planFirstMissingInputCoordinate state input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)
        context fuel table cache hstate]
      simp [leafInputProbePlan, hvalue]

theorem runResolved_planProbingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runResolvedFromTable context fuel table
        ((planProbingHashQuery parameter input).run cache) =
      pure (some ⟨context, fuel,
        (purePlanProbingHashQuery parameter input state, cache), table⟩) := by
  unfold planProbingHashQuery purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runResolvedFromTable]
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              rw [StateT.run_bind,
                runResolvedFromTable_bind,
                runResolved_planLeafInputProbe state input candidate lay tree
                  leafIdx context fuel table cache hstate]
              simp [runResolvedFromTable]
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              simp [runResolvedFromTable]
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runResolvedFromTable]
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              rw [StateT.run_bind,
                runResolvedFromTable_bind,
                runResolved_planFirstMissingInputCoordinate state input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                  context fuel table cache hstate]
              simp [runResolvedFromTable]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              simp [runResolvedFromTable]

theorem runResolved_probingHashQuery_eq_afterPlan
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache) =
      runResolvedFromTable context fuel table ((probingHashQueryAfterPlan parameter input
        (purePlanProbingHashQuery parameter input context.state)).run cache) := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind, runResolvedFromTable_bind,
    runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl]
  simp only [pure_bind]

noncomputable def canonicalQueryCandidates (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) : List Probe :=
  match input with
  | .inl (.inr input) => (purePlanProbingHashQuery parameter input context.state).candidate?.toList
  | _ => []

theorem pendingCoveredBy_of_mem_canonicalChronologicalQuery
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (prior : List Probe)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hcovered : PendingCoveredBy prior context)
    (hresult : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)) :
    PendingCoveredBy (prior ++ canonicalQueryCandidates parameter input context) result.context := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some raw =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff, Option.some.injEq] at hcanonical
      subst result
      change PendingCoveredBy (prior ++ canonicalQueryCandidates parameter input context) raw.context
      have hprior : PendingCoveredBy (prior ++ canonicalQueryCandidates parameter input context) context :=
        hcovered.mono_candidates (List.sublist_append_left _ _)
      cases input with
      | inl query =>
          cases query with
          | inl n =>
              exact pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table raw hprior
                (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe _)
                  (splitUniformImpl_probeFree n cache)) hraw
          | inr input =>
              change some raw ∈ support (runResolvedFromTable context fuel table
                ((probingHashQuery parameter input).run cache)) at hraw
              rw [runResolved_probingHashQuery_eq_afterPlan] at hraw
              apply pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table raw hprior _ hraw
              apply probingHashQueryAfterPlan_probeBound
              intro candidate hcandidate
              apply List.mem_append_right
              simp [canonicalQueryCandidates, hcandidate]
      | inr message =>
          exact pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table raw hprior
            (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe _)
              (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache)) hraw

noncomputable def canonicalTraceCandidates (parameter : PublicParameter) (history : List CanonicalQuerySelection) : List Probe :=
  history.flatMap fun entry => canonicalQueryCandidates parameter entry.input entry.context

set_option maxRecDepth 100000 in
theorem pendingCoveredBy_of_mem_canonicalQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (prior : List Probe) (hcovered : PendingCoveredBy prior context)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (∀ ordinal entry, result.2[ordinal]? = some entry →
      PendingCoveredBy (prior ++ canonicalTraceCandidates parameter (result.2.take ordinal)) entry.context) ∧
    (∀ terminal, result.1 = some terminal →
      PendingCoveredBy (prior ++ canonicalTraceCandidates parameter result.2) terminal.context) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache prior result with
  | pure value =>
      simp only [runCanonicalQueryTrace, OracleComp.construct_pure] at hrun
      split_ifs at hrun <;> simp only [mem_support_pure_iff] at hrun <;> subst result
      · constructor
        · intro ordinal entry hentry
          simp at hentry
        · intro terminal hterminal
          simp only [Option.some.injEq] at hterminal
          subst terminal
          simpa [canonicalTraceCandidates] using hcovered
      · simp
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind] at hrun
      split_ifs at hrun with hcomplete
      · rw [mem_support_bind_iff] at hrun
        obtain ⟨stepOption, hstep, hrun⟩ := hrun
        cases stepOption with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at hrun
            subst result
            constructor
            · intro ordinal entry hentry
              cases ordinal with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                  subst entry
                  simpa [canonicalTraceCandidates] using hcovered
              | succ ordinal => simp at hentry
            · simp
        | some step =>
            rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff] at hpure
            subst result
            have hstepCovered := pendingCoveredBy_of_mem_canonicalChronologicalQuery parameter root ftsSecret
              input context fuel table cache prior step hcovered hstep
            have htailCovered := ih step.value.1 step.context step.remaining step.table step.value.2
              (prior ++ canonicalQueryCandidates parameter input context) hstepCovered tail htail
            constructor
            · intro ordinal entry hentry
              cases ordinal with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                  subst entry
                  simpa [canonicalTraceCandidates] using hcovered
              | succ ordinal =>
                  simp only [List.getElem?_cons_succ] at hentry
                  simpa [canonicalTraceCandidates, List.append_assoc] using htailCovered.1 ordinal entry hentry
            · intro terminal hterminal
              simpa [canonicalTraceCandidates, List.append_assoc] using htailCovered.2 terminal hterminal
      · simp only [mem_support_pure_iff] at hrun
        subst result
        simp

theorem pendingCoveredBy_of_mem_canonicalRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)) :
    ∀ ordinal entry, result.2[ordinal]? = some entry →
      PendingCoveredBy (canonicalTraceCandidates parameter (result.2.take ordinal)) entry.context := by
  rw [canonicalRetainedQueryTrace, mem_support_bind_iff] at hrun
  obtain ⟨rootOption, hroot, hrun⟩ := hrun
  cases rootOption with
  | none =>
      simp only [mem_support_pure_iff] at hrun
      subst result
      simp
  | some root =>
      rw [mem_support_bind_iff] at hrun
      obtain ⟨rest, hrest, hpure⟩ := hrun
      simp only [mem_support_pure_iff] at hpure
      subst result
      have hcovered := pendingCoveredBy_of_mem_runResolvedFromTable [] _ _ fuel table root pendingCoveredBy_empty
        (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe [])
          (maskedPublishedTreeRoot_probeFree emptySplitHashCache)) hroot
      have htrace := pendingCoveredBy_of_mem_canonicalQueryTrace parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩) root.context root.remaining root.table
        root.value.2 [] hcovered rest hrest
      simpa only [List.nil_append] using htrace.1

theorem canonicalQueryCandidates_length_le_hashCount
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) :
    (canonicalQueryCandidates parameter input context).length ≤ outerHashQueryCount input := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact le_rfl
      | inr input =>
          unfold canonicalQueryCandidates outerHashQueryCount
          cases (purePlanProbingHashQuery parameter input context.state).candidate? <;> simp
  | inr message => exact le_rfl

theorem canonicalTraceCandidates_length_le_hashCount
    (parameter : PublicParameter) (history : List CanonicalQuerySelection) :
    (canonicalTraceCandidates parameter history).length ≤ canonicalTraceHashCount history := by
  induction history with
  | nil => exact le_rfl
  | cons head tail ih =>
      simpa only [canonicalTraceCandidates, List.flatMap_cons, List.length_append,
        canonicalTraceHashCount, List.map_cons, List.sum_cons] using
        Nat.add_le_add (canonicalQueryCandidates_length_le_hashCount parameter head.input head.context) ih

theorem PendingCoveredBy.card_le
    {candidates : List Probe} {context : DeferredContext}
    (hcovered : PendingCoveredBy candidates context) :
    context.state.pending.card ≤ candidates.length := by
  classical
  have hsubset : context.state.pending ⊆
      (candidates.map fun candidate => (candidate.coordinate, candidate.candidate)).toFinset := by
    intro entry hentry
    obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered entry hentry
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨candidate, hcandidate, Prod.ext hcoordinate hdigest⟩
  exact (Finset.card_le_card hsubset).trans
    (by simpa only [List.length_map] using (List.toFinset_card_le
      (candidates.map fun candidate => (candidate.coordinate, candidate.candidate))))

theorem canonicalTraceHashCount_take_le
    (history : List CanonicalQuerySelection) (ordinal : Nat) :
    canonicalTraceHashCount (history.take ordinal) ≤ canonicalTraceHashCount history := by
  exact ((List.take_sublist _ _).map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem pending_card_le_of_coupled_canonicalRetainedTrace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hleft : left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right) :
    ∀ (ordinal : Nat) (entry : CanonicalQuerySelection),
      left.2[ordinal]? = some entry → entry.context.state.pending.card ≤ q := by
  intro ordinal entry hentry
  have hcovered := pendingCoveredBy_of_mem_canonicalRetainedQueryTrace
    adversary parameter table ftsSecret fuel left hleft ordinal entry hentry
  exact hcovered.card_le.trans ((canonicalTraceCandidates_length_le_hashCount parameter _).trans
    ((canonicalTraceHashCount_take_le _ _).trans (hrelation.hashCount_le.trans
      (prehitRetainedTraceHashCount_le adversary q hq parameter hparameter table ftsSecret hfts right hright))))

theorem candidate_source_of_mem_canonicalTraceCandidates_take
    (parameter : PublicParameter) (history : List CanonicalQuerySelection) (ordinal : Nat)
    (candidate : Probe) (hcandidate : candidate ∈ canonicalTraceCandidates parameter (history.take ordinal)) :
    ∃ earlier < ordinal, ∃ source, history[earlier]? = some source ∧
      candidate ∈ canonicalQueryCandidates parameter source.input source.context := by
  simp only [canonicalTraceCandidates, List.mem_flatMap] at hcandidate
  obtain ⟨source, hsource, hcandidate⟩ := hcandidate
  obtain ⟨earlier, hearlier⟩ := List.mem_iff_getElem?.mp hsource
  have hlt : earlier < ordinal := by
    obtain ⟨hindex, _heq⟩ := List.getElem?_eq_some_iff.mp hearlier
    have hlength := List.length_take_le ordinal history
    omega
  refine ⟨earlier, hlt, source, ?_, hcandidate⟩
  simpa only [List.getElem?_take, hlt, ↓reduceIte] using hearlier

theorem pending_candidate_source_of_canonicalRetainedTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (ordinal : Nat) (entry : CanonicalQuerySelection) (hentry : result.2[ordinal]? = some entry)
    (coordinate : Coordinate) (digest : Digest)
    (hpending : (coordinate, digest) ∈ entry.context.state.pending) :
    ∃ earlier < ordinal, ∃ source candidate,
      result.2[earlier]? = some source ∧
      candidate ∈ canonicalQueryCandidates parameter source.input source.context ∧
      candidate.coordinate = coordinate ∧ candidate.candidate = digest := by
  have hcovered := pendingCoveredBy_of_mem_canonicalRetainedQueryTrace
    adversary parameter table ftsSecret fuel result hrun ordinal entry hentry
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered (coordinate, digest) hpending
  obtain ⟨earlier, hlt, source, hsource, hcandidate⟩ :=
    candidate_source_of_mem_canonicalTraceCandidates_take parameter result.2 ordinal candidate hcandidate
  exact ⟨earlier, hlt, source, candidate, hsource, hcandidate, hcoordinate, hdigest⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
