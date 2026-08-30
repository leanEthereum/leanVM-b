import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinarySigner
import SphincsSecurity.Proof.QueryBound

/-!
# Adaptive ordinary boundary refinement

This file lifts the one-query ordinary refinement through the complete adaptive computation and its
terminal verifier.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

theorem FinalizationContextLE.canonicalize_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) :
    FinalizationContextLE table (canonicalizeMaterializedValues table left) right where
  view := (FinalizationViewLE.of_eq
    (finalizationViewEq_canonicalize_left table left hcontext.leftValid
      hcontext.view.leftStarts hcontext.view.leftClean)).trans hcontext.view
  leftValid := canonicalizeMaterializedValues_valid table left hcontext.leftValid
    hcontext.view.leftClean
  rightValid := hcontext.rightValid
  rightCompletable := hcontext.rightCompletable

theorem valuesLE_canonicalizeMaterializedValues_left
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) :
    LazyRevealProbe.ValuesLE
      (canonicalizeMaterializedValues table context).state context.state := by
  intro coordinate output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    have hknown := hpublished coordinate hrevealed
    cases horiginal : context.state.values coordinate with
    | none => exact False.elim (hknown horiginal)
    | some original =>
        have hresolved : resolvedCompletionValue table context coordinate = some original := by
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ original horiginal
              simp [resolvedCompletionValue, heq]
          | position position =>
              simp [resolvedCompletionValue, DeferredContext.positionValue, horiginal]
        rw [hresolved] at hvalue
        have heq : original = output := Option.some.inj hvalue
        rwa [heq] at horiginal
  · simp [hrevealed] at hvalue

theorem OrdinaryMaterializedRunEq.canonicalize_left
    {table : OtsSecretIndex → HashOutput}
    {left right : ResolvedRunResult (α × SplitHashCache)}
    (hrelation : OrdinaryMaterializedRunEq table left right) :
    OrdinaryMaterializedRunEq table
      { left with
        context := canonicalizeMaterializedValues table left.context }
      right where
  value_eq := hrelation.value_eq
  context_le := hrelation.context_le.canonicalize_left
  remaining_le := hrelation.remaining_le
  left_table := hrelation.left_table
  right_table := hrelation.right_table
  cache_eq := hrelation.cache_eq
  revealed_eq := by
    rw [canonicalizeMaterializedValues_revealed]
    exact hrelation.revealed_eq
  values_le := (valuesLE_canonicalizeMaterializedValues_left table left.context
    hrelation.context_le.view.leftStarts hrelation.left_published).trans hrelation.values_le
  left_published := hrelation.left_published.to_canonicalizedMaterializedValues
  right_materialized := hrelation.right_materialized

theorem PrivateStructuralHit.canonicalizeMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hprivate : PrivateStructuralHit context)
    (hpublished : PublishedValues context.state) :
    PrivateStructuralHit (canonicalizeMaterializedValues table context) := by
  rcases hprivate with ⟨position, output, hhidden, hvalue, hhit⟩
  have hnotRevealed : Coordinate.position position ∉ context.state.revealed := by
    intro hrevealed
    exact (hpublished (.position position) hrevealed) hhidden
  refine ⟨position, output, ?_, hvalue, ?_⟩
  · change publicMaterializedValues table context (.position position) = none
    simp [publicMaterializedValues, hnotRevealed]
  · change truncateHash output ∈ context.state.pendingAt (.position position)
    exact hhit

theorem privateStructuralHit_canonicalizeMaterializedValues_iff
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hpublished : PublishedValues context.state) :
    PrivateStructuralHit (canonicalizeMaterializedValues table context) ↔
      ∃ position output,
        Coordinate.position position ∉ context.state.revealed ∧
          context.values position = some output ∧
          context.state.hitAt (.position position) output := by
  constructor
  · rintro ⟨position, output, hhidden, hprivate, hhit⟩
    refine ⟨position, output, ?_, hprivate, ?_⟩
    · intro hrevealed
      have hknown := hpublished (.position position) hrevealed
      unfold canonicalizeMaterializedValues publicMaterializedValues at hhidden
      simp only [hrevealed, ↓reduceIte] at hhidden
      cases hvalue : context.state.values (.position position) with
      | none => exact hknown hvalue
      | some value =>
          simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue] at hhidden
    · change truncateHash output ∈ context.state.pendingAt (.position position)
      exact hhit
  · rintro ⟨position, output, hnotRevealed, hprivate, hhit⟩
    refine ⟨position, output, ?_, hprivate, ?_⟩
    · change publicMaterializedValues table context (.position position) = none
      simp [publicMaterializedValues, hnotRevealed]
    · change truncateHash output ∈ context.state.pendingAt (.position position)
      exact hhit

theorem privateStructuralHit_canonicalize_directDeferredContext_iff
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hpublished : PublishedValues state) :
    PrivateStructuralHit
        (canonicalizeMaterializedValues table (directDeferredContext state)) ↔
      ∃ position output,
        Coordinate.position position ∉ state.revealed ∧
          state.values (.position position) = some output ∧
          state.hitAt (.position position) output := by
  rw [privateStructuralHit_canonicalizeMaterializedValues_iff table
    (directDeferredContext state) hpublished]
  rfl

theorem privateStructuralHit_canonicalize_presample_materialize_addPending_iff
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (output : HashOutput) (candidate : Digest)
    (hpublished : PublishedValues context.state)
    (hhidden : context.state.values (.position position) = none)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    let nextContext : DeferredContext :=
      { state := ((context.state.clearPending (.position position)).materialize
          (.position position) output).addPending (.position position) candidate
        values := context.values.install position output }
    PrivateStructuralHit (canonicalizeMaterializedValues table nextContext) ↔
      truncateHash output = candidate := by
  dsimp only
  let baseState := (context.state.clearPending (.position position)).materialize
    (.position position) output
  let nextContext : DeferredContext :=
    { state := baseState.addPending (.position position) candidate
      values := context.values.install position output }
  have hnotRevealed : Coordinate.position position ∉ context.state.revealed := by
    intro hrevealed
    exact (hpublished (.position position) hrevealed) hhidden
  have hbasePublished : PublishedValues baseState := by
    apply PublishedValues.materialize
    simpa [PublishedValues, LazyRevealProbe.State.clearPending] using hpublished
  have hnextPublished : PublishedValues nextContext.state := by
    simpa [nextContext, PublishedValues, LazyRevealProbe.State.addPending] using
      hbasePublished
  rw [privateStructuralHit_canonicalizeMaterializedValues_iff table nextContext
    hnextPublished]
  constructor
  · rintro ⟨other, otherOutput, hotherHidden, hotherPrivate, hotherHit⟩
    by_cases heq : other = position
    · subst other
      have houtput : otherOutput = output := by
        have hvalue : some output = some otherOutput := by
          simpa [nextContext, DeferredStructuralValues.install] using hotherPrivate
        exact (Option.some.inj hvalue).symm
      subst otherOutput
      have hbaseMiss : ¬baseState.hitAt (.position position) output := by
        change ¬((context.state.clearPending (.position position)).clearPending
          (.position position)).hitAt (.position position) output
        exact not_hitAt_clearPending_self
          (context.state.clearPending (.position position)) (.position position) output
      exact (hitAt_addPending_self_iff baseState (.position position) candidate output).1
        hotherHit |>.resolve_left hbaseMiss
    · exfalso
      apply hclean
      rw [privateStructuralHit_canonicalizeMaterializedValues_iff table context hpublished]
      refine ⟨other, otherOutput, ?_, ?_, ?_⟩
      · simpa [nextContext, baseState, LazyRevealProbe.State.addPending,
          LazyRevealProbe.State.materialize, LazyRevealProbe.State.clearPending] using
          hotherHidden
      · simpa [nextContext, DeferredStructuralValues.install,
          Function.update_of_ne heq] using hotherPrivate
      · have hcoordinate : Coordinate.position position ≠ .position other := by
          intro hsame
          exact heq (Coordinate.position.inj hsame).symm
        have hbaseHit : baseState.hitAt (.position other) otherOutput := by
          change (baseState.addPending (.position position) candidate).hitAt
            (.position other) otherOutput at hotherHit
          rw [hitAt_addPending_of_ne baseState (.position position)
            (.position other) candidate otherOutput hcoordinate] at hotherHit
          exact hotherHit
        change ((context.state.clearPending (.position position)).clearPending
          (.position position)).hitAt (.position other) otherOutput at hbaseHit
        have honce := (hitAt_clearPending_of_ne
          (context.state.clearPending (.position position)) (.position position)
          (.position other) otherOutput hcoordinate.symm).mp hbaseHit
        exact (hitAt_clearPending_of_ne context.state (.position position)
          (.position other) otherOutput hcoordinate.symm).mp honce
  · intro hcandidate
    refine ⟨position, output, ?_, ?_, ?_⟩
    · simpa [nextContext, baseState, LazyRevealProbe.State.addPending,
        LazyRevealProbe.State.materialize, LazyRevealProbe.State.clearPending] using
        hnotRevealed
    · simp [nextContext, DeferredStructuralValues.install]
    · exact (hitAt_addPending_self_iff baseState (.position position) candidate output).2
        (Or.inr hcandidate)

theorem probEvent_privateStructuralHit_canonicalize_presample_materialize_addPending_le
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (candidate : Digest)
    (hpublished : PublishedValues context.state)
    (hhidden : context.state.values (.position position) = none)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    Pr[fun output : HashOutput =>
        let nextContext : DeferredContext :=
          { state := ((context.state.clearPending (.position position)).materialize
              (.position position) output).addPending (.position position) candidate
            values := context.values.install position output }
        PrivateStructuralHit (canonicalizeMaterializedValues table nextContext) |
      LazyRevealProbe.sampleHashOutput] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun output : HashOutput => truncateHash output = candidate |
        LazyRevealProbe.sampleHashOutput] := by
      apply OracleComp.probEvent_congr'
      · intro output _houtput
        exact privateStructuralHit_canonicalize_presample_materialize_addPending_iff
          table context position output candidate hpublished hhidden hclean
      · rfl
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      unfold LazyRevealProbe.sampleHashOutput
      exact SphincsSecurity.probEvent_uniform_truncateHash_eq candidate
    _ ≤ _ := by
      rw [show Fintype.card Digest = 2 ^ digestBits by simp]

noncomputable def resolveThenMaterializedPrivateProbeOutcome
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (candidate : Digest) : ProbComp Bool := by
  classical
  exact do
    let resolved ← resolveDeferredPositionValue position context
    match resolved with
    | none => pure false
    | some resolved =>
        let nextContext : DeferredContext :=
          { resolved.toDeferredContext with
            state := (resolved.state.materialize (.position position) resolved.output).addPending
              (.position position) candidate }
        pure (decide (PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext)))

theorem probEvent_resolveThenMaterializedPrivateProbeOutcome_le
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (candidate : Digest)
    (hpublished : PublishedValues context.state)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context)) :
    Pr[= true |
        resolveThenMaterializedPrivateProbeOutcome table context position candidate] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  have hrun : resolveThenMaterializedPrivateProbeOutcome table context position candidate = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then pure false
      else
        let nextContext : DeferredContext :=
          { state := ((context.state.clearPending (.position position)).materialize
              (.position position) output).addPending (.position position) candidate
            values := context.values.install position output }
        pure (decide (PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext)))) := by
    rw [resolveThenMaterializedPrivateProbeOutcome,
      resolveDeferredPositionValue_fresh position context hhidden hprivate]
    simp only [bind_assoc]
    apply bind_congr
    intro output
    by_cases holdHit : context.state.hitAt (.position position) output
    · simp [holdHit]
    · simp [holdHit]
  rw [hrun, ← probEvent_eq_eq_probOutput]
  refine (probEvent_bind_le_probEvent_add
    (mx := LazyRevealProbe.sampleHashOutput)
    (my := fun output =>
      if context.state.hitAt (.position position) output then pure false
      else
        let nextContext : DeferredContext :=
          { state := ((context.state.clearPending (.position position)).materialize
              (.position position) output).addPending (.position position) candidate
            values := context.values.install position output }
        pure (decide (PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext))))
    (q := fun hit : Bool => hit = true)
    (p := fun output : HashOutput =>
      let nextContext : DeferredContext :=
        { state := ((context.state.clearPending (.position position)).materialize
            (.position position) output).addPending (.position position) candidate
          values := context.values.install position output }
      PrivateStructuralHit (canonicalizeMaterializedValues table nextContext))
    (ε := 0) ?_).trans ?_
  · intro output _houtput hmiss
    by_cases holdHit : context.state.hitAt (.position position) output
    · simp [holdHit]
    · simp [holdHit, hmiss]
  · simpa only [add_zero] using
      probEvent_privateStructuralHit_canonicalize_presample_materialize_addPending_le
        table context position candidate hpublished hhidden hclean

noncomputable def classifyCanonicalMaterializedPrivateObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) : ProbComp Bool := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure true
    else if DeferredCompletable table context then
      observe context fuel value
    else
      pure false

noncomputable def classifyCanonicalMaterializedOrdinaryObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) : ProbComp Bool := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure false
    else if DeferredCompletable table context then
      observe context fuel value
    else
      pure true

noncomputable def classifyCanonicalMaterializedObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure .privateStructuralFailure
    else if DeferredCompletable table context then
      observe context fuel value
    else
      pure .ordinaryFailure

theorem evalDist_private_classifyCanonicalMaterializedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hproject : evalDist (DirectBoundaryOutcome.privateStructural <$>
        detailedObserve context fuel value) =
      evalDist (observe context fuel value)) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        classifyCanonicalMaterializedObserve table detailedObserve context fuel value) =
      evalDist
        (classifyCanonicalMaterializedPrivateObserve table observe context fuel value) := by
  unfold classifyCanonicalMaterializedObserve
    classifyCanonicalMaterializedPrivateObserve
  by_cases hprivate : PrivateStructuralHit
      (canonicalizeMaterializedValues table context)
  · simp [hprivate, DirectBoundaryOutcome.privateStructural]
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simpa [hcompletable] using hproject
    · simp [hcompletable, DirectBoundaryOutcome.privateStructural]

theorem evalDist_ordinary_classifyCanonicalMaterializedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hproject : evalDist (DirectBoundaryOutcome.ordinary <$>
        detailedObserve context fuel value) =
      evalDist (observe context fuel value)) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        classifyCanonicalMaterializedObserve table detailedObserve context fuel value) =
      evalDist
        (classifyCanonicalMaterializedOrdinaryObserve table observe context fuel value) := by
  unfold classifyCanonicalMaterializedObserve
    classifyCanonicalMaterializedOrdinaryObserve
  by_cases hprivate : PrivateStructuralHit
      (canonicalizeMaterializedValues table context)
  · simp [hprivate, DirectBoundaryOutcome.ordinary]
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simpa [hcompletable] using hproject
    · simp [hcompletable, DirectBoundaryOutcome.ordinary]

theorem probEvent_resolve_then_classifyCanonicalMaterializedPrivateObserve_le
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (position : Position) (candidate : Digest)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (fuel : Nat) (value : alpha) (bound : ℝ≥0∞)
    (hpublished : PublishedValues context.state)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context))
    (hobserve : ∀ resolved : DeferredResolution,
      let nextContext : DeferredContext :=
        { resolved.toDeferredContext with
          state := (resolved.state.materialize (.position position) resolved.output).addPending
            (.position position) candidate }
      ¬PrivateStructuralHit (canonicalizeMaterializedValues table nextContext) →
        DeferredCompletable table nextContext →
        Pr[= true | observe nextContext fuel value] ≤ bound) :
    Pr[= true | do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure false
      | some resolved =>
          let nextContext : DeferredContext :=
            { resolved.toDeferredContext with
              state := (resolved.state.materialize (.position position) resolved.output).addPending
                (.position position) candidate }
          classifyCanonicalMaterializedPrivateObserve table observe nextContext fuel value] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + bound := by
  classical
  let nextContext : DeferredResolution → DeferredContext := fun resolved =>
    { resolved.toDeferredContext with
      state := (resolved.state.materialize (.position position) resolved.output).addPending
        (.position position) candidate }
  let fires : Option DeferredResolution → Prop
    | none => False
    | some resolved =>
        PrivateStructuralHit (canonicalizeMaterializedValues table (nextContext resolved))
  let continuation : Option DeferredResolution → ProbComp Bool
    | none => pure false
    | some resolved =>
        classifyCanonicalMaterializedPrivateObserve table observe
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
        have hnotPrivate :
            ¬PrivateStructuralHit
              (canonicalizeMaterializedValues table (nextContext resolved)) := by
          simpa [fires] using hmiss
        unfold continuation classifyCanonicalMaterializedPrivateObserve
        simp only [hnotPrivate, ↓reduceIte]
        by_cases hcompletable : DeferredCompletable table (nextContext resolved)
        · simpa [hcompletable] using hobserve resolved hnotPrivate hcompletable
        · simp [hcompletable]
  · have hsource :
        Pr[fires | resolveDeferredPositionValue position context] ≤
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      have houtcome :
          resolveThenMaterializedPrivateProbeOutcome table context position candidate =
            (fun resolved => decide (fires resolved)) <$>
              resolveDeferredPositionValue position context := by
        unfold resolveThenMaterializedPrivateProbeOutcome
        simp only [map_eq_bind_pure_comp]
        apply bind_congr
        intro resolved
        cases resolved <;> simp [fires, nextContext]
      exact calc
        Pr[fires | resolveDeferredPositionValue position context] =
            Pr[= true |
              resolveThenMaterializedPrivateProbeOutcome table context position candidate] := by
          rw [houtcome, ← probEvent_eq_eq_probOutput, probEvent_map]
          exact OracleComp.probEvent_congr' (fun resolved _ => by simp) rfl
        _ ≤ _ := probEvent_resolveThenMaterializedPrivateProbeOutcome_le
          table context position candidate hpublished hhidden hprivate hclean
    simpa [add_comm] using add_le_add_right hsource bound

noncomputable def directDetailedBoundaryCanonicalMaterializedPrivateObserve
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
        (classifyCanonicalMaterializedPrivateObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2))
        context fuel table ((impl query).run cache))
    computation observe context fuel table cache

noncomputable def directDetailedBoundaryCanonicalMaterializedOrdinaryObserve
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
      runDirectDetailedOrdinaryObserve
        (classifyCanonicalMaterializedOrdinaryObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2))
        context fuel table ((impl query).run cache))
    computation observe context fuel table cache

noncomputable def directDetailedBoundaryCanonicalMaterializedObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (observe : DeferredContext → Nat →
      (alpha × SplitHashCache) → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec alpha =>
      (DeferredContext → Nat →
        (alpha × SplitHashCache) → ProbComp DirectBoundaryOutcome) →
        DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp DirectBoundaryOutcome)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      runDirectDetailedObserve
        (classifyCanonicalMaterializedObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2))
        context fuel table ((impl query).run cache))
    computation observe context fuel table cache

set_option maxRecDepth 100000 in
theorem evalDist_private_directDetailedBoundaryCanonicalMaterializedObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (detailedObserve : DeferredContext → Nat →
      (alpha × SplitHashCache) → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (hobserve : ∀ context fuel value,
      evalDist (DirectBoundaryOutcome.privateStructural <$>
          detailedObserve context fuel value) =
        evalDist (observe context fuel value))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        directDetailedBoundaryCanonicalMaterializedObserve impl computation detailedObserve
          context fuel table cache) =
      evalDist (directDetailedBoundaryCanonicalMaterializedPrivateObserve impl computation
        observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryCanonicalMaterializedObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_pure]
      exact hobserve context fuel (value, cache)
  | query_bind query next ih =>
      rw [directDetailedBoundaryCanonicalMaterializedObserve,
        OracleComp.construct_query_bind,
        directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind]
      apply evalDist_private_runDirectDetailedObserve
      intro result _hresult
      apply evalDist_private_classifyCanonicalMaterializedObserve
      exact ih result.value.1 result.context result.remaining result.value.2

set_option maxRecDepth 100000 in
theorem evalDist_ordinary_directDetailedBoundaryCanonicalMaterializedObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (detailedObserve : DeferredContext → Nat →
      (alpha × SplitHashCache) → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (hobserve : ∀ context fuel value,
      evalDist (DirectBoundaryOutcome.ordinary <$>
          detailedObserve context fuel value) =
        evalDist (observe context fuel value))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        directDetailedBoundaryCanonicalMaterializedObserve impl computation detailedObserve
          context fuel table cache) =
      evalDist (directDetailedBoundaryCanonicalMaterializedOrdinaryObserve impl computation
        observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryCanonicalMaterializedObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryCanonicalMaterializedOrdinaryObserve,
        OracleComp.construct_pure]
      exact hobserve context fuel (value, cache)
  | query_bind query next ih =>
      rw [directDetailedBoundaryCanonicalMaterializedObserve,
        OracleComp.construct_query_bind,
        directDetailedBoundaryCanonicalMaterializedOrdinaryObserve,
        OracleComp.construct_query_bind]
      apply evalDist_ordinary_runDirectDetailedObserve
      intro result _hresult
      apply evalDist_ordinary_classifyCanonicalMaterializedObserve
      exact ih result.value.1 result.context result.remaining result.value.2

set_option maxRecDepth 100000 in
theorem directDetailedBoundaryCanonicalMaterializedPrivateObserve_bind
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (left : OracleComp spec alpha) (next : alpha → OracleComp spec beta)
    (observe : DeferredContext → Nat → (beta × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    directDetailedBoundaryCanonicalMaterializedPrivateObserve impl (left >>= next)
        observe context fuel table cache =
      directDetailedBoundaryCanonicalMaterializedPrivateObserve impl left
        (fun nextContext remaining value =>
          directDetailedBoundaryCanonicalMaterializedPrivateObserve impl (next value.1)
            observe nextContext remaining table value.2)
        context fuel table cache := by
  induction left using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp [directDetailedBoundaryCanonicalMaterializedPrivateObserve]
  | query_bind query continuation ih =>
      rw [bind_assoc, directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind,
        directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind]
      apply bind_congr
      intro result
      cases result with
      | stopped reason => cases reason <;> rfl
      | done result =>
          simp only [finishDirectDetailedPrivateObserve]
          unfold classifyCanonicalMaterializedPrivateObserve
          by_cases hprivate : PrivateStructuralHit
              (canonicalizeMaterializedValues table result.context)
          · simp [hprivate]
          · simp only [hprivate, ↓reduceIte]
            by_cases hcompletable : DeferredCompletable table result.context
            · simp only [hcompletable, ↓reduceIte]
              exact ih result.value.1 result.context result.remaining result.value.2
            · simp [hcompletable]

set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryCanonicalMaterializedPrivateObserve_le
    {iota : Type} {spec : OracleSpec iota}
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (isCharged : iota → Prop) [DecidablePred isCharged]
    (computation : OracleComp spec alpha)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (epsilon terminalBound : ℝ≥0∞)
    (hstep : ∀ query nextContext remaining nextCache nextObserve,
      ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext) →
      DeferredCompletable table nextContext →
      (∀ result : ResolvedRunResult (spec.Range query × SplitHashCache),
        DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable nextContext remaining table
            ((impl query).run nextCache)) →
        ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table result.context) →
        DeferredCompletable table result.context →
        Pr[= true | nextObserve result.context result.remaining result.value] ≤
          (result.remaining : ℝ≥0∞) * epsilon + terminalBound) →
      Pr[= true |
        runDirectDetailedPrivateObserve
          (classifyCanonicalMaterializedPrivateObserve table nextObserve)
          nextContext remaining table ((impl query).run nextCache)] ≤
        (remaining : ℝ≥0∞) * epsilon + terminalBound)
    (hremaining : ∀ query nextContext remaining nextCache result,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable nextContext remaining table
          ((impl query).run nextCache)) →
      remaining ≤ result.remaining + if isCharged query then 1 else 0)
    (hterminal : ∀ nextContext remaining value nextCache,
      ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext) →
      DeferredCompletable table nextContext →
      Pr[= true | observe nextContext remaining (value, nextCache)] ≤ terminalBound)
    (hbound : computation.IsQueryBoundP isCharged fuel)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context))
    (hcompletable : DeferredCompletable table context) :
    Pr[= true |
      directDetailedBoundaryCanonicalMaterializedPrivateObserve impl computation observe
        context fuel table cache] ≤
      (fuel : ℝ≥0∞) * epsilon + terminalBound := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp only [directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_pure]
      exact (hterminal context fuel value cache hclean hcompletable).trans
        (le_add_left le_rfl)
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind]
      apply hstep query context fuel cache
      · exact hclean
      · exact hcompletable
      · intro result hresult hnextClean hnextCompletable
        apply ih result.value.1 result.context result.remaining result.value.2
        · apply (hbound.2 result.value.1).mono
          have hfuel := hremaining query context fuel cache result hresult
          by_cases hcharged : isCharged query
          · simp only [hcharged, ↓reduceIte] at hfuel
            have hpositive : 0 < fuel := by
              rcases hbound.1 with hnotCharged | hpositive
              · exact (hnotCharged hcharged).elim
              · exact hpositive
            simpa [hcharged] using (show fuel - 1 ≤ result.remaining by omega)
          · simp only [hcharged, ↓reduceIte, add_zero] at hfuel
            simpa [hcharged] using hfuel
        · exact hnextClean
        · exact hnextCompletable

theorem remaining_le_of_done_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache))) :
    fuel ≤ result.remaining + if IsOuterHash query then 1 else 0 := by
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
    ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
    context fuel table result hresult
  have hraw := raw_done_of_mem_runDirectResolvedFromTable
    ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
    context fuel table result hdirect
  exact LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
    context.state result.context.state fuel result.remaining
    (if IsOuterHash query then 1 else 0)
    ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
    result.value
    (maskedExpandedAdversaryImpl_step_isProbeBound parameter root ftsSecret query cache)
    hraw

set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryCanonicalMaterializedPrivateObserve_maskedExpanded_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (epsilon terminalBound : ℝ≥0∞)
    (hstep : ∀ query nextContext remaining nextCache nextObserve,
      ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext) →
      DeferredCompletable table nextContext →
      (∀ result : ResolvedRunResult
          ((OracleWorld + SigningSpec).Range query × SplitHashCache),
        DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable nextContext remaining table
            ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run nextCache)) →
        ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table result.context) →
        DeferredCompletable table result.context →
        Pr[= true | nextObserve result.context result.remaining result.value] ≤
          (result.remaining : ℝ≥0∞) * epsilon + terminalBound) →
      Pr[= true |
        runDirectDetailedPrivateObserve
          (classifyCanonicalMaterializedPrivateObserve table nextObserve)
          nextContext remaining table
          ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run nextCache)] ≤
        (remaining : ℝ≥0∞) * epsilon + terminalBound)
    (hterminal : ∀ nextContext remaining value nextCache,
      ¬PrivateStructuralHit
          (canonicalizeMaterializedValues table nextContext) →
      DeferredCompletable table nextContext →
      Pr[= true | observe nextContext remaining (value, nextCache)] ≤ terminalBound)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        computation).IsQueryBoundP (· matches Sum.inr _) fuel)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hclean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context))
    (hcompletable : DeferredCompletable table context) :
    Pr[= true |
      directDetailedBoundaryCanonicalMaterializedPrivateObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation observe
        context fuel table cache] ≤
      (fuel : ℝ≥0∞) * epsilon + terminalBound := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp only [directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_pure]
      exact (hterminal context fuel value cache hclean hcompletable).trans
        (le_add_left le_rfl)
  | query_bind query next ih =>
      rw [directDetailedBoundaryCanonicalMaterializedPrivateObserve,
        OracleComp.construct_query_bind]
      apply hstep query context fuel cache
      · exact hclean
      · exact hcompletable
      · rintro ⟨resultContext, resultRemaining, ⟨output, finalCache⟩, resultTable⟩
          hresult hnextClean hnextCompletable
        have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
          ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
          context fuel table
          ⟨resultContext, resultRemaining, (output, finalCache), resultTable⟩ hresult
        have hraw := raw_done_of_mem_runDirectResolvedFromTable
          ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
          context fuel table
          ⟨resultContext, resultRemaining, (output, finalCache), resultTable⟩ hdirect
        have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
          ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)
          context fuel table
          ⟨resultContext, resultRemaining, (output, finalCache), resultTable⟩
          hconsistent hstarts hdirect
        have hremaining := remaining_le_of_done_maskedExpandedAdversaryImpl
          parameter root ftsSecret query context fuel table cache
          ⟨resultContext, resultRemaining, (output, finalCache), resultTable⟩ hresult
        have htailBound :
            (simulateQ
              (SphincsSecurity.expandedAdversaryImpl
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey))
              (next output)).IsQueryBoundP
                (· matches Sum.inr _) resultRemaining := by
          cases query with
          | inl worldQuery =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              cases worldQuery with
              | inl n =>
                  exact (hbound.2 output).mono (by
                    simpa [IsOuterHash] using hremaining)
              | inr input =>
                  have htail :
                      (simulateQ
                        (SphincsSecurity.expandedAdversaryImpl
                          (⟨parameter, root,
                            tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
                        (next output)).IsQueryBoundP
                          (· matches Sum.inr _) (fuel - 1) := by
                    simpa [IsOuterHash] using hbound.2 output
                  apply htail.mono
                  change fuel ≤ resultRemaining + 1 at hremaining
                  omega
          | inr message =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
              change Option Signature at output
              change LazyRevealProbe.RawResult.done resultContext.state resultRemaining
                  (output, finalCache) ∈ support
                (LazyRevealProbe.runRaw context.state fuel
                  ((maskedSigningImpl parameter root ftsSecret message).run cache)) at hraw
              have houtput : output ∈ support
                  (scheme.sign
                    (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                      SecretKey) message) := by
                exact maskedSign_done_output_mem_support parameter root table ftsSecret
                  message context.state resultContext.state cache finalCache
                  fuel resultRemaining output hcore.2.2 (by
                    simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                      maskedSigningImpl] using hraw)
              exact (isQueryBoundP_of_bind hbound output houtput).mono (by
                simpa [IsOuterHash] using hremaining)
        apply ih output resultContext resultRemaining finalCache
        · exact htailBound
        · exact hcore.2.1
        · exact hcore.2.2
        · exact hnextClean
        · exact hnextCompletable

theorem publishedValues_of_done_runDirectResolvedDetailedFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hpreserves : PreservesPublishedValues computation)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table (computation.run cache))) :
    PublishedValues result.context.state := by
  apply hpreserves context.state cache fuel result.context.state result.remaining
    result.value.1 result.value.2 hpublished
  apply raw_done_of_mem_runDirectResolvedFromTable
    (computation.run cache) context fuel table result
  exact mem_support_runDirectResolvedFromTable_of_done_detailed
    (computation.run cache) context fuel table result hresult

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingRomImpl
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (query : OracleWorld.Domain)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        (((probingRomImpl parameter) query).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        (((probingRomImpl parameter) query).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases query with
  | inl n =>
      change RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((splitUniformImpl n).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
      unfold splitUniformImpl
      rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
        runDirectResolvedDetailedFromTable_uniform_query_bind,
        runDirectResolvedDetailedFromTable_uniform_query_bind]
      apply relTriple_bind (relTriple_refl
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table leftOutput
        left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
          hvalues hpublished hrightMaterialized
  | inr input =>
      exact relTriple_runDirectResolvedDetailed_probingHashQuery parameter table input
        left right leftFuel rightFuel leftCache rightCache hcontext hpositive hfuel hcache
          hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : IsOuterHash query → 0 < leftFuel)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          apply relTriple_stable_to_ordinary
          simpa [maskedExpandedAdversaryImpl, probingRomImpl] using
            ordinaryMaterializedStableCouples_splitUniformImpl table n left right leftFuel
              rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
              hrightMaterialized
      | inr input =>
          simpa [maskedExpandedAdversaryImpl] using
            relTriple_runDirectResolvedDetailed_probingRomImpl parameter table (.inr input)
              left right leftFuel rightFuel leftCache rightCache hcontext
              (hpositive (by simp [IsOuterHash])) hfuel hcache hrevealed hvalues hpublished
              hrightMaterialized
  | inr message =>
      apply relTriple_stable_to_ordinary
      simpa [maskedExpandedAdversaryImpl, maskedSigningImpl] using
        ordinaryMaterializedStableCouples_maskedSigningImpl table parameter root ftsSecret
          message left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
          hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem isQueryBoundP_expandedSigningTrace_all_tables_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (simulateQ
      (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
      (signingTraceComputation
        (adversary.main ⟨root, parameter⟩))).IsQueryBoundP
          (· matches Sum.inr _) q := by
  have hfull := isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter
    hparameter table ftsSecret hfts root
  unfold retainedGameRestComputation at hfull
  rw [simulateQ_bind] at hfull
  exact IsQueryBoundP.of_bind_left hfull

theorem ordinaryMaterializedStableCouples_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) :
    OrdinaryMaterializedStableCouples table maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (ordinaryMaterializedStableCouples_ensureTreeNode table topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact ordinaryMaterializedStableCouples_revealPublishedCoordinate table
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

theorem finalizationContextLE_empty
    (table : OtsSecretIndex → HashOutput) :
    FinalizationContextLE table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) := by
  have hright : directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) =
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues } := by
    rfl
  rw [hright]
  refine
    { view := FinalizationViewLE.refl table _ DeferredContext.valid_empty
        (startTableAgrees_empty table) ?_
      leftValid := DeferredContext.valid_empty
      rightValid := DeferredContext.valid_empty
      rightCompletable := deferredCompletable_empty table }
  intro coordinate output _hvalue
  simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
    LazyRevealProbe.State.empty]

def BoolImp (left right : Bool) : Prop := left = true → right = true

theorem relTriple_any_true_of_evalDist_eq_true
    (left right : ProbComp Bool)
    (hright : evalDist right = evalDist (pure true : ProbComp Bool)) :
    RelTriple left right BoolImp := by
  have hbase := relTriple_true left (pure true : ProbComp Bool)
  have hsupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  have himp : RelTriple left (pure true : ProbComp Bool) BoolImp := by
    apply relTriple_post_mono hsupport
    intro leftValue rightValue hrelation _hleft
    simpa using hrelation.2
  exact relTriple_of_evalDist_eq_right hright.symm himp

theorem relTriple_false_any (right : ProbComp Bool) :
    RelTriple (pure false : ProbComp Bool) right BoolImp := by
  have hbase := relTriple_true (pure false : ProbComp Bool) right
  have hsupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value ∈ support (pure false : ProbComp Bool))
      (fun value hvalue => hvalue)
  apply relTriple_post_mono hsupport
  intro leftValue rightValue hrelation hleft
  have hfalse : leftValue = false := by
    simpa using hrelation.2
  rw [hfalse] at hleft
  contradiction

set_option maxRecDepth 100000 in
theorem relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewLE table left right) :
    RelTriple
      (Option.isNone <$> finalizeResolvedCoordinates coordinates left table)
      (Option.isNone <$> finalizeResolvedCoordinates coordinates right table)
      BoolImp := by
  induction coordinates generalizing left right with
  | nil =>
      simp [finalizeResolvedCoordinates, BoolImp]
  | cons coordinate remaining ih =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
          have hleftClean : ¬left.state.hitAt index.coordinate (table index) :=
            hview.leftClean index.coordinate (table index) (by
              simp [index, resolvedCompletionValue, OtsSecretIndex.coordinate])
          have hrightClean : ¬right.state.hitAt index.coordinate (table index) :=
            hview.rightClean index.coordinate (table index) (by
              simp [index, resolvedCompletionValue, OtsSecretIndex.coordinate])
          change RelTriple
            (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) left table)
            (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) right table)
            BoolImp
          rw [finalizeResolvedCoordinates_cons_chainStart_of_clean table index remaining left
              hview.leftStarts hleftClean,
            finalizeResolvedCoordinates_cons_chainStart_of_clean table index remaining right
              hview.rightStarts hrightClean]
          exact ih (left.completeResolved index.coordinate (table index))
            (right.completeResolved index.coordinate (table index))
            (hview.completeStart index)
      | position position =>
          cases hvalue : resolvedCompletionValue table left (.position position) with
          | some output =>
              have hrightValue :
                  resolvedCompletionValue table right (.position position) = some output := by
                rw [← hview.valueEq]
                exact hvalue
              have hleftClean := hview.leftClean (.position position) output hvalue
              have hrightClean := hview.rightClean (.position position) output hrightValue
              rw [finalizeResolvedCoordinates_cons_position_of_known_clean table position
                  remaining left hview.leftConsistent output
                  (by simpa [resolvedCompletionValue] using hvalue) hleftClean,
                finalizeResolvedCoordinates_cons_position_of_known_clean table position
                  remaining right hview.rightConsistent output
                  (by simpa [resolvedCompletionValue] using hrightValue) hrightClean]
              exact ih (left.completeResolved (.position position) output)
                (right.completeResolved (.position position) output)
                (hview.completePosition position output)
          | none =>
              have hrightValue :
                  resolvedCompletionValue table right (.position position) = none := by
                rw [← hview.valueEq]
                exact hvalue
              rw [finalizeResolvedCoordinates_cons_position_of_unknown table position remaining
                  left (by simpa [resolvedCompletionValue] using hvalue),
                finalizeResolvedCoordinates_cons_position_of_unknown table position remaining
                  right (by simpa [resolvedCompletionValue] using hrightValue)]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
              intro leftOutput rightOutput houtput
              subst rightOutput
              by_cases hleftHit : left.state.hitAt (.position position) leftOutput
              · have hrightHit : right.state.hitAt (.position position) leftOutput := by
                  exact hview.pendingLE (.position position) hvalue hleftHit
                rw [if_pos hleftHit, if_pos hrightHit]
                exact relTriple_pure_pure (fun h => h)
              · by_cases hrightHit : right.state.hitAt (.position position) leftOutput
                · rw [if_neg hleftHit, if_pos hrightHit]
                  exact relTriple_any_true_of_evalDist_eq_true
                    (Option.isNone <$>
                      finalizeResolvedCoordinates remaining
                        (left.completeResolved (.position position) leftOutput) table)
                    (pure true) rfl
                · rw [if_neg hleftHit, if_neg hrightHit]
                  exact ih
                    (left.completeResolved (.position position) leftOutput)
                    (right.completeResolved (.position position) leftOutput)
                    (hview.completePosition position leftOutput)

set_option maxRecDepth 100000 in
theorem relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE_covered
    (table : OtsSecretIndex → HashOutput)
    (leftCoordinates rightCoordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewLE table left right)
    (hleftNodup : leftCoordinates.Nodup) (hrightNodup : rightCoordinates.Nodup)
    (hleftCovered : PendingCovered leftCoordinates left)
    (hrightCovered : PendingCovered rightCoordinates right) :
    RelTriple
      (Option.isNone <$> finalizeResolvedCoordinates leftCoordinates left table)
      (Option.isNone <$> finalizeResolvedCoordinates rightCoordinates right table)
      BoolImp := by
  classical
  let leftBase := leftCoordinates.toFinset.toList
  let rightBase := rightCoordinates.toFinset.toList
  let leftExtra := (rightCoordinates.toFinset \ leftCoordinates.toFinset).toList
  let rightExtra := (leftCoordinates.toFinset \ rightCoordinates.toFinset).toList
  have hleftBasePerm : leftBase.Perm leftCoordinates := by
    simpa [leftBase] using List.toFinset_toList hleftNodup
  have hrightBasePerm : rightBase.Perm rightCoordinates := by
    simpa [rightBase] using List.toFinset_toList hrightNodup
  have hleftBaseCovered : PendingCovered leftBase left := by
    intro entry hentry
    have hmem := hleftCovered entry hentry
    simpa [leftBase] using hmem
  have hrightBaseCovered : PendingCovered rightBase right := by
    intro entry hentry
    have hmem := hrightCovered entry hentry
    simpa [rightBase] using hmem
  have hleftDisjoint : leftExtra.Disjoint leftBase := by
    rw [List.disjoint_left]
    intro coordinate hleftExtra hleftBase
    simp only [leftExtra, Finset.mem_toList, Finset.mem_sdiff] at hleftExtra
    simp only [leftBase, Finset.mem_toList, List.mem_toFinset] at hleftBase
    exact hleftExtra.2 (by simpa using hleftBase)
  have hrightDisjoint : rightExtra.Disjoint rightBase := by
    rw [List.disjoint_left]
    intro coordinate hrightExtra hrightBase
    simp only [rightExtra, Finset.mem_toList, Finset.mem_sdiff] at hrightExtra
    simp only [rightBase, Finset.mem_toList, List.mem_toFinset] at hrightBase
    exact hrightExtra.2 (by simpa using hrightBase)
  have hleftAugNodup : (leftExtra ++ leftBase).Nodup :=
    List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) hleftDisjoint
  have hrightAugNodup : (rightExtra ++ rightBase).Nodup :=
    List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) hrightDisjoint
  have haugPerm : (leftExtra ++ leftBase).Perm (rightExtra ++ rightBase) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hleftAugNodup hrightAugNodup
    ext coordinate
    simp only [List.toFinset_append, leftExtra, rightExtra, leftBase, rightBase,
      Finset.toList_toFinset, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    by_cases hleft : coordinate ∈ leftCoordinates <;>
      by_cases hright : coordinate ∈ rightCoordinates <;> simp [hleft, hright]
  have hleftPermDist :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftBase left table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftCoordinates left table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm hleftBasePerm left table]
  have hrightPermDist :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightBase right table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightCoordinates right table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm hrightBasePerm right table]
  have hleftAug := evalDist_map_isNone_finalizeResolvedCoordinates_append_irrelevant
    table leftExtra leftBase left (Finset.nodup_toList _)
    (by
      intro coordinate hleftExtra
      simp only [leftExtra, Finset.mem_toList, Finset.mem_sdiff] at hleftExtra
      simp only [leftBase, Finset.mem_toList, List.mem_toFinset]
      simpa using hleftExtra.2)
    hleftBaseCovered hview.leftConsistent hview.leftStarts hview.leftClean
  have hrightAug := evalDist_map_isNone_finalizeResolvedCoordinates_append_irrelevant
    table rightExtra rightBase right (Finset.nodup_toList _)
    (by
      intro coordinate hrightExtra
      simp only [rightExtra, Finset.mem_toList, Finset.mem_sdiff] at hrightExtra
      simp only [rightBase, Finset.mem_toList, List.mem_toFinset]
      simpa using hrightExtra.2)
    hrightBaseCovered hview.rightConsistent hview.rightStarts hview.rightClean
  have hsameAug :=
    relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE table
      (leftExtra ++ leftBase) left right hview
  have hpermAug :
      evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (leftExtra ++ leftBase) right table) =
        evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (rightExtra ++ rightBase) right table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm haugPerm right table]
  have hleftToAug :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftCoordinates left table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates (leftExtra ++ leftBase) left table) :=
    hleftPermDist.symm.trans hleftAug.symm
  have hrightFromAug :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates (leftExtra ++ leftBase) right table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightCoordinates right table) :=
    hpermAug.trans (hrightAug.trans hrightPermDist)
  exact relTriple_of_evalDist_eq_right hrightFromAug
    (relTriple_of_evalDist_eq_left hleftToAug hsameAug)

set_option maxRecDepth 100000 in
theorem relTriple_finishResolvedRunIsNone_of_finalizationContextLE
    (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftValue rightValue : α)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (finishResolvedRunIsNone
        (some ⟨left, leftFuel, leftValue, table⟩))
      (finishResolvedRunIsNone
        (some ⟨right, rightFuel, rightValue, table⟩))
      BoolImp := by
  rw [finishResolvedRunIsNone_some_eq_finalize _ hcontext.leftCompletable,
    finishResolvedRunIsNone_some_eq_finalize _ hcontext.rightCompletable]
  exact relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE_covered
    table left.state.coordinates.toList right.state.coordinates.toList left right hcontext.view
      left.state.coordinates.nodup_toList right.state.coordinates.nodup_toList
      (pendingCovered_coordinates_toList left) (pendingCovered_coordinates_toList right)

set_option maxRecDepth 100000 in
theorem relTriple_classifyDirectOrdinaryObserve_resolvedFinalization_of_contextLE
    (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftValue rightValue : α)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
        left leftFuel leftValue)
      (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
        right rightFuel rightValue)
      BoolImp := by
  have hleftNotPrivate :=
    not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
  have hrightNotPrivate :=
    not_privateStructuralHit_of_deferredCompletable hcontext.rightCompletable
  simp only [classifyDirectOrdinaryObserve, hleftNotPrivate, hrightNotPrivate,
    hcontext.leftCompletable, hcontext.rightCompletable, ↓reduceIte,
    resolvedFinalizationObserve]
  exact relTriple_finishResolvedRunIsNone_of_finalizationContextLE table left right leftFuel
    rightFuel leftValue rightValue hcontext

theorem relTriple_finishDirectDetailedOrdinaryObserve_of_stableRunEq
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hrun : RelTriple leftRun rightRun
      (DirectDetailedOrdinaryStableRunEq table))
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support leftRun →
      DirectDetailedResult.done rightResult ∈ support rightRun →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve leftResult.context leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (leftRun >>= finishDirectDetailedOrdinaryObserve leftObserve)
      (rightRun >>= finishDirectDetailedOrdinaryObserve rightObserve)
      BoolImp := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrun
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_false_any
            (finishDirectDetailedOrdinaryObserve rightObserve rightResult)
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_true_of_evalDist_eq_true
                (leftObserve leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
          | fuelExhausted =>
              exact relTriple_any_true_of_evalDist_eq_true
                (leftObserve leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
      | done rightResult =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean leftResult rightResult hleftMem hrightMem hcleanRelation
          · exact relTriple_any_true_of_evalDist_eq_true
              (leftObserve leftResult.context leftResult.remaining leftResult.value)
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
              (hdoomed rightResult hrightMem hdoomedRelation)

set_option maxRecDepth 100000 in
theorem relTriple_runDirectDetailedOrdinaryObserve_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (leftObserve rightObserve : DeferredContext → Nat →
      (Digest × SplitHashCache) → ProbComp Bool)
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support
        (runDirectResolvedDetailedFromTable
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      DirectDetailedResult.done rightResult ∈ support
        (runDirectResolvedDetailedFromTable
          (directDeferredContext
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve leftResult.context leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable
          (directDeferredContext
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (runDirectDetailedOrdinaryObserve leftObserve
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      (runDirectDetailedOrdinaryObserve rightObserve
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      BoolImp := by
  apply relTriple_finishDirectDetailedOrdinaryObserve_of_stableRunEq table
  · exact ordinaryMaterializedStableCouples_maskedPublishedTreeRoot table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
      fuel fuel emptySplitHashCache emptySplitHashCache
      (finalizationContextLE_empty table) le_rfl rfl rfl
      (fun _ _ hvalue => hvalue) publishedValues_empty rfl
  · exact hclean
  · exact hdoomed

theorem evalDist_runDirectDetailedOrdinaryObserve_bind
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (observe : DeferredContext → Nat → β → ProbComp Bool)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist
      (runDirectDetailedOrdinaryObserve observe context fuel table (left >>= next)) =
    evalDist (runDirectResolvedDetailedFromTable context fuel table left >>=
        finishDirectDetailedOrdinaryObserve
          (fun nextContext remaining value =>
            runDirectDetailedOrdinaryObserve observe nextContext remaining table
              (next value))) := by
  unfold runDirectDetailedOrdinaryObserve
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
      simp [finishDirectDetailedOrdinaryObserve, hcore.1]

set_option maxRecDepth 100000 in
theorem relTriple_finishDirectDetailedOrdinaryObserve_of_runEq
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hrun : RelTriple leftRun rightRun (DirectDetailedOrdinaryRunEq table))
    (hleftPublished : ∀ result,
      DirectDetailedResult.done result ∈ support leftRun →
        PublishedValues result.context.state)
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support leftRun →
      DirectDetailedResult.done rightResult ∈ support rightRun →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve (canonicalizeMaterializedValues table leftResult.context)
          leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (leftRun >>= finishDirectDetailedOrdinaryObserve
        (canonicalizeDirectDetailedOrdinaryObserve table leftObserve))
      (rightRun >>= finishDirectDetailedOrdinaryObserve rightObserve)
      BoolImp := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrun
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_false_any
            (finishDirectDetailedOrdinaryObserve rightObserve rightResult)
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_true_of_evalDist_eq_true
                (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                  leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
          | fuelExhausted =>
              exact relTriple_any_true_of_evalDist_eq_true
                (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                  leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
      | done rightResult =>
          rcases hrelation with hcleanRelation | hprivateRelation | hdoomedRelation
          · have hcanonicalCompletable :=
              hcleanRelation.canonicalize_left.context_le.leftCompletable
            have hnotPrivate := not_privateStructuralHit_of_deferredCompletable
              hcanonicalCompletable
            simpa [finishDirectDetailedOrdinaryObserve,
              canonicalizeDirectDetailedOrdinaryObserve,
              classifyDirectDetailedOrdinaryObserve, hnotPrivate,
              hcleanRelation.left_published, hcanonicalCompletable] using
                hclean leftResult rightResult hleftMem hrightMem hcleanRelation
          · have hpublished := hleftPublished leftResult hleftMem
            have hcanonicalPrivate :=
              hprivateRelation.canonicalizeMaterializedValues (table := table) hpublished
            simp only [finishDirectDetailedOrdinaryObserve,
              canonicalizeDirectDetailedOrdinaryObserve, hcanonicalPrivate, ↓reduceIte]
            exact relTriple_false_any
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
          · exact relTriple_any_true_of_evalDist_eq_true
              (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                leftResult.context leftResult.remaining leftResult.value)
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
              (hdoomed rightResult hrightMem hdoomedRelation)

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context)
    (hmaterialized : context = directDeferredContext context.state)
    (hobserve : ∀ result,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      FinalizationDoomedRun table (some result) →
      result.context = directDeferredContext result.context.state →
      evalDist (observe result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (runDirectDetailedOrdinaryObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  unfold runDirectDetailedOrdinaryObserve
  calc
    _ = evalDist
        (runDirectResolvedDetailedFromTable context fuel table computation >>= fun _ =>
          pure true) := by
      apply evalDist_bind_congr
      intro result hresult
      have hshape : DirectDetailedMaterialized result := by
        rw [hmaterialized] at hresult
        exact directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
          computation context.state fuel table result hresult
      cases result with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => exact False.elim hshape
          | ordinaryHit => rfl
          | fuelExhausted => rfl
      | done result =>
          exact hobserve result hresult
            (finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
              computation context fuel result hdoomed hresult)
            hshape
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runDirectResolvedDetailedFromTable context fuel table computation)
      (by simp [runDirectResolvedDetailedFromTable]) (pure true)

set_option maxRecDepth 100000 in
theorem relTriple_directDetailedBoundaryOrdinaryObserve_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
              (fun query => query matches Sum.inr _) leftFuel)
    (hterminal : ∀ value nextLeft nextRight nextLeftFuel nextRightFuel
        nextLeftCache nextRightCache,
      FinalizationContextLE table nextLeft nextRight →
      nextLeftFuel ≤ nextRightFuel →
      ordinaryQueryCache nextLeftCache = ordinaryQueryCache nextRightCache →
      nextLeft.state.revealed = nextRight.state.revealed →
      LazyRevealProbe.ValuesLE nextLeft.state nextRight.state →
      PublishedValues nextLeft.state →
      nextRight = directDeferredContext nextRight.state →
      RelTriple
        (leftObserve nextLeft nextLeftFuel (value, nextLeftCache))
        (rightObserve nextRight nextRightFuel (value, nextRightCache)) BoolImp)
    (hdoomed : ∀ result : ResolvedRunResult (α × SplitHashCache),
      FinalizationDoomedRun table (some result) →
      result.context = directDeferredContext result.context.state →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (directDetailedBoundaryOrdinaryObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation leftObserve
        left leftFuel table leftCache)
      (runDirectDetailedOrdinaryObserve rightObserve right rightFuel table
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run rightCache)) BoolImp := by
  induction computation using OracleComp.inductionOn generalizing
      left right leftFuel rightFuel leftCache rightCache with
  | pure value =>
      simp only [directDetailedBoundaryOrdinaryObserve, OracleComp.construct_pure,
        simulateQ_pure, StateT.run_pure]
      simpa [runDirectDetailedOrdinaryObserve, runDirectResolvedDetailedFromTable_pure,
        finishDirectDetailedOrdinaryObserve] using
          hterminal value left right leftFuel rightFuel leftCache rightCache hcontext hfuel
            hcache hrevealed hvalues hpublished hrightMaterialized
  | query_bind input next ih =>
      rw [directDetailedBoundaryOrdinaryObserve, OracleComp.construct_query_bind]
      let leftNextObserve : DeferredContext → Nat →
          ((OracleWorld + SigningSpec).Range input × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          directDetailedBoundaryOrdinaryObserve
            (maskedExpandedAdversaryImpl parameter root ftsSecret) (next value.1)
            leftObserve nextContext remaining table value.2
      let rightNextObserve : DeferredContext → Nat →
          ((OracleWorld + SigningSpec).Range input × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          runDirectDetailedOrdinaryObserve rightObserve nextContext remaining table
            ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
              (next value.1)).run value.2)
      have hrightFactor :
          evalDist
            (runDirectDetailedOrdinaryObserve rightObserve right rightFuel table
              ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                (OracleSpec.query input >>= next)).run rightCache)) =
          evalDist
            (runDirectResolvedDetailedFromTable right rightFuel table
              ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run rightCache) >>=
                finishDirectDetailedOrdinaryObserve rightNextObserve) := by
        rw [simulateQ_query_bind, StateT.run_bind]
        exact evalDist_runDirectDetailedOrdinaryObserve_bind table right rightFuel
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run rightCache)
          (fun value =>
            (simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
              (next value.1)).run value.2)
          rightObserve hcontext.rightValid.valuesConsistent hcontext.view.rightStarts
      apply relTriple_of_evalDist_eq_right hrightFactor.symm
      apply relTriple_finishDirectDetailedOrdinaryObserve_of_runEq table
      · apply relTriple_runDirectResolvedDetailed_maskedExpandedAdversaryImpl
        · exact hcontext
        · intro houter
          cases input with
          | inl worldInput =>
              cases worldInput with
              | inl n => simp [IsOuterHash] at houter
              | inr hashInput =>
                  rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                    OracleComp.isQueryBoundP_query_bind_iff] at hbound
                  simpa using hbound.1
          | inr message => simp [IsOuterHash] at houter
        · exact hfuel
        · exact hcache
        · exact hrevealed
        · exact hvalues
        · exact hpublished
        · exact hrightMaterialized
      · intro result hresult
        exact publishedValues_of_done_runDirectResolvedDetailedFromTable
          (maskedExpandedAdversaryImpl parameter root ftsSecret input)
          (preservesPublishedValuesImpl_maskedExpandedAdversaryImpl parameter root ftsSecret
            input)
          left leftFuel table leftCache result hpublished hresult
      · rintro ⟨leftContext, leftRemaining, ⟨leftOutput, leftFinalCache⟩, leftTable⟩
          ⟨rightContext, rightRemaining, ⟨rightOutput, rightFinalCache⟩, rightTable⟩
          hleftMem hrightMem hrelation
        have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          left leftFuel table
            ⟨leftContext, leftRemaining, (leftOutput, leftFinalCache), leftTable⟩ hleftMem
        have hraw := raw_done_of_mem_runDirectResolvedFromTable
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          left leftFuel table
            ⟨leftContext, leftRemaining, (leftOutput, leftFinalCache), leftTable⟩ hdirect
        have hstepBound := maskedExpandedAdversaryImpl_step_isProbeBound parameter root
          ftsSecret input leftCache
        have hremaining := LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
          left.state leftContext.state leftFuel leftRemaining
          (if IsOuterHash input then 1 else 0)
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          (leftOutput, leftFinalCache) hstepBound hraw
        have htailBound :
            (simulateQ
              (SphincsSecurity.expandedAdversaryImpl
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey))
              (next leftOutput)).IsQueryBoundP
                (fun query => query matches Sum.inr _) leftRemaining := by
          cases input with
          | inl worldInput =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              cases worldInput with
              | inl n =>
                  exact (hbound.2 leftOutput).mono (by
                    simpa [IsOuterHash] using hremaining)
              | inr hashInput =>
                  have htail :
                      (simulateQ
                        (SphincsSecurity.expandedAdversaryImpl
                          (⟨parameter, root,
                            tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
                        (next leftOutput)).IsQueryBoundP
                          (fun query => query matches Sum.inr _) (leftFuel - 1) := by
                    simpa [IsOuterHash] using hbound.2 leftOutput
                  apply htail.mono
                  change leftFuel ≤ leftRemaining + 1 at hremaining
                  omega
          | inr message =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
              change Option Signature at leftOutput
              change LazyRevealProbe.RawResult.done leftContext.state
                  leftRemaining (leftOutput, leftFinalCache) ∈ support
                (LazyRevealProbe.runRaw left.state leftFuel
                  ((maskedSigningImpl parameter root ftsSecret message).run leftCache)) at hraw
              have houtput : leftOutput ∈ support
                  (scheme.sign
                    (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                      SecretKey) message) := by
                exact maskedSign_done_output_mem_support parameter root table ftsSecret
                  message left.state leftContext.state leftCache leftFinalCache
                  leftFuel leftRemaining leftOutput
                    hrelation.context_le.view.leftStarts (by
                      simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                        maskedSigningImpl] using hraw)
              exact (isQueryBoundP_of_bind hbound leftOutput houtput).mono (by
                simpa [IsOuterHash] using hremaining)
        simp only [rightNextObserve]
        have houtputEq : leftOutput = rightOutput := hrelation.value_eq
        rw [← houtputEq]
        exact ih leftOutput
            (canonicalizeMaterializedValues table leftContext) rightContext
            leftRemaining rightRemaining leftFinalCache rightFinalCache
            hrelation.canonicalize_left.context_le hrelation.remaining_le hrelation.cache_eq
            hrelation.canonicalize_left.revealed_eq hrelation.canonicalize_left.values_le
            hrelation.canonicalize_left.left_published hrelation.right_materialized htailBound
      · intro result hresult hdoomedRun
        exact evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed
          table
          ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
            (next result.value.1)).run result.value.2)
          rightObserve result.context result.remaining hdoomedRun.1.2 hdoomedRun.2
            (fun nextResult _ => hdoomed nextResult)

theorem not_privateStructuralHit_of_directDeferredContext
    (context : DeferredContext)
    (hmaterialized : context = directDeferredContext context.state) :
    ¬PrivateStructuralHit context := by
  intro hprivate
  rcases hprivate with ⟨position, output, hhidden, hvalue, _hhit⟩
  have hsame : context.values position = context.state.values (.position position) := by
    rw [hmaterialized]
    rfl
  rw [hsame, hhidden] at hvalue
  contradiction

noncomputable def retainedResolvedFinalizationOrdinaryObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) : ProbComp Bool :=
  classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
    context fuel ((root, value.1), value.2)

set_option maxRecDepth 100000 in
theorem relTriple_directDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) leftFuel) :
    RelTriple
      (directDetailedBoundaryOrdinaryObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret)
        (retainedGameRestComputation adversary ⟨root, parameter⟩)
        (retainedResolvedFinalizationOrdinaryObserve table root)
        left leftFuel table leftCache)
      (runDirectDetailedOrdinaryObserve
        (retainedResolvedFinalizationOrdinaryObserve table root)
        right rightFuel table
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).run rightCache))
      BoolImp := by
  apply relTriple_directDetailedBoundaryOrdinaryObserve_maskedExpandedAdversaryImpl
    parameter root table ftsSecret
  · exact hcontext
  · exact hfuel
  · exact hcache
  · exact hrevealed
  · exact hvalues
  · exact hpublished
  · exact hrightMaterialized
  · exact hbound
  · intro value nextLeft nextRight nextLeftFuel nextRightFuel nextLeftCache nextRightCache
      hnextContext _hnextFuel _hnextCache _hnextRevealed _hnextValues _hnextPublished
      _hnextMaterialized
    exact relTriple_classifyDirectOrdinaryObserve_resolvedFinalization_of_contextLE table
      nextLeft nextRight nextLeftFuel nextRightFuel
      ((root, value), nextLeftCache) ((root, value), nextRightCache) hnextContext
  · intro result hdoomed hmaterialized
    have hnotPrivate :=
      not_privateStructuralHit_of_directDeferredContext result.context hmaterialized
    simp [retainedResolvedFinalizationOrdinaryObserve,
      classifyDirectOrdinaryObserve, hnotPrivate, hdoomed.2.2.2]

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem directBoundaryObserve_bind
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (left : OracleComp spec α) (next : α → OracleComp spec β)
    (observe : DeferredContext → Nat → (β × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    directBoundaryObserve impl (left >>= next) observe context fuel table cache =
      directBoundaryObserve impl left
        (fun nextContext remaining value =>
          directBoundaryObserve impl (next value.1) observe
            nextContext remaining table value.2)
        context fuel table cache := by
  induction left using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp [directBoundaryObserve]
  | query_bind query continuation ih =>
      rw [bind_assoc, directBoundaryObserve, OracleComp.construct_query_bind,
        directBoundaryObserve, OracleComp.construct_query_bind]
      apply bind_congr
      intro result
      cases result with
      | none => rfl
      | some result =>
          unfold finishObserve canonicalizeObserve
          simp only
          by_cases hpublished : PublishedValues result.context.state
          · simp only [hpublished, ↓reduceIte]
            exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
              result.remaining result.value.2
          · simp [hpublished]

set_option maxRecDepth 100000 in
theorem runDirectResolvedFromTable_bind_general
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    runDirectResolvedFromTable context fuel table (left >>= next) =
      runDirectResolvedFromTable context fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            runDirectResolvedFromTable result.context result.remaining result.table
              (next result.value) := by
  induction left using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runDirectResolvedFromTable]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runDirectResolvedFromTable_uniform_query_bind,
            runDirectResolvedFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | hashOutput =>
          rw [bind_assoc, runDirectResolvedFromTable_hashOutput_query_bind,
            runDirectResolvedFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | ensure coordinate =>
          rw [bind_assoc, runDirectResolvedFromTable_ensure_query_bind,
            runDirectResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runDirectResolvedFromTable_probe_query_bind,
            runDirectResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining
      | peek coordinate =>
          rw [bind_assoc, runDirectResolvedFromTable_peek_query_bind,
            runDirectResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [bind_assoc, runDirectResolvedFromTable_publish_query_bind,
            runDirectResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [bind_assoc, runDirectResolvedFromTable_reveal_query_bind,
            runDirectResolvedFromTable_reveal_query_bind]
          cases hvalue : context.state.values coordinate with
          | some output =>
              exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
              | position position =>
                  simp only [bind_assoc]
                  apply bind_congr
                  intro resolved
                  cases resolved with
                  | none => rfl
                  | some resolved =>
                      exact ih resolved.output
                        { state := context.state.materialize (.position position) resolved.output
                          values := resolved.values }
                        fuel

set_option maxRecDepth 100000 in
theorem evalDist_failed_directDetailedBoundaryObserve_bind
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (left : OracleComp spec α) (next : α → OracleComp spec β)
    (detailedObserve : DeferredContext → Nat → (β × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (β × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe]
    (hobserve : ∀ nextContext remaining value,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      evalDist (DirectBoundaryOutcome.failed <$>
          detailedObserve nextContext remaining value) =
        evalDist (observe nextContext remaining value))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        directDetailedBoundaryObserve impl (left >>= next) detailedObserve
          context fuel table cache) =
      evalDist (DirectBoundaryOutcome.failed <$>
        directDetailedBoundaryObserve impl left
          (fun nextContext remaining value =>
            directDetailedBoundaryObserve impl (next value.1) detailedObserve
              nextContext remaining table value.2)
          context fuel table cache) := by
  let detailedNext : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome := fun nextContext remaining value =>
    directDetailedBoundaryObserve impl (next value.1) detailedObserve
      nextContext remaining table value.2
  let nextObserve : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool :=
    fun nextContext remaining value =>
      directBoundaryObserve impl (next value.1) observe
        nextContext remaining table value.2
  letI : ObserverDooms table nextObserve := ⟨by
    intro nextContext remaining value hnextConsistent hnextStarts hdoomed
    exact directBoundaryObserve_dooms impl (next value.1) observe nextContext remaining
      value.2 hnextConsistent hnextStarts hdoomed⟩
  calc
    _ = evalDist (directBoundaryObserve impl (left >>= next) observe
          context fuel table cache) :=
      evalDist_failed_directDetailedBoundaryObserve impl (left >>= next) detailedObserve observe
        hobserve context fuel cache hconsistent hstarts
    _ = evalDist (directBoundaryObserve impl left nextObserve
          context fuel table cache) := by
      rw [directBoundaryObserve_bind]
    _ = _ := by
      symm
      apply evalDist_failed_directDetailedBoundaryObserve impl left detailedNext nextObserve
      · intro nextContext remaining value hnextConsistent hnextStarts
        exact evalDist_failed_directDetailedBoundaryObserve impl (next value.1)
          detailedObserve observe hobserve nextContext remaining value.2 hnextConsistent
            hnextStarts
      · exact hconsistent
      · exact hstarts

set_option maxRecDepth 100000 in
theorem directBoundaryObserve_liftOracleWorldLeft
    (left : QueryImpl OracleWorld
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (right : QueryImpl SigningSpec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp OracleWorld α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    directBoundaryObserve (left + right) (liftOracleWorldLeft computation)
        observe context fuel table cache =
      directBoundaryObserve left computation observe context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp [liftOracleWorldLeft, directBoundaryObserve]
  | query_bind query next ih =>
      change directBoundaryObserve (left + right)
          (liftM ((OracleWorld + SigningSpec).query (.inl query)) >>= fun output =>
            liftOracleWorldLeft (next output))
          observe context fuel table cache =
        directBoundaryObserve left (liftM (OracleWorld.query query) >>= next)
          observe context fuel table cache
      rw [directBoundaryObserve, OracleComp.construct_query_bind,
        directBoundaryObserve, OracleComp.construct_query_bind]
      apply bind_congr
      intro result
      cases result with
      | none => rfl
      | some result =>
          unfold finishObserve canonicalizeObserve
          simp only
          by_cases hpublished : PublishedValues result.context.state
          · simp only [hpublished, ↓reduceIte]
            exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
              result.remaining result.value.2
          · simp [hpublished]

noncomputable def retainedResolvedFinalizationDetailedObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  classifyDirectObserve table (resolvedFinalizationObserve table)
    context fuel ((root, value.1), value.2)

noncomputable def retainedResolvedFinalizationObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) : ProbComp Bool :=
  resolvedFinalizationObserve table context fuel ((root, value.1), value.2)

instance retainedResolvedFinalizationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) (root : Digest) :
    ObserverDooms table (retainedResolvedFinalizationObserve table root) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact ObserverDooms.eq_true context fuel ((root, value.1), value.2)
      hconsistent hstarts hdoomed

noncomputable def granularDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationDetailedObserve table value.1)
    context fuel table value.2

noncomputable def granularRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directBoundaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationObserve table value.1)
    context fuel table value.2

instance granularRetainedRestObserve_observerDooms
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ObserverDooms table
      (granularRetainedRestObserve adversary parameter table ftsSecret) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact directBoundaryObserve_dooms
      (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
      (retainedResolvedFinalizationObserve table value.1)
      context fuel value.2 hconsistent hstarts hdoomed

noncomputable def granularDetailedVerifierFinishObserve
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryObserve
    (maskedExpandedAdversaryImpl parameter root ftsSecret)
    (do
      let verified ← liftOracleWorldLeft
        (scheme.verify ⟨root, parameter⟩ value.1.1.message value.1.1.signature)
      pure (value.1, verified))
    (retainedResolvedFinalizationDetailedObserve table root)
    context fuel table value.2

noncomputable def granularVerifierFinishObserve
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) : ProbComp Bool :=
  directBoundaryObserve
    (maskedExpandedAdversaryImpl parameter root ftsSecret)
    (do
      let verified ← liftOracleWorldLeft
        (scheme.verify ⟨root, parameter⟩ value.1.1.message value.1.1.signature)
      pure (value.1, verified))
    (retainedResolvedFinalizationObserve table root)
    context fuel table value.2

noncomputable def granularVerifierResultObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec)
    (context : DeferredContext) (fuel : Nat)
    (value : Bool × SplitHashCache) : ProbComp Bool :=
  retainedResolvedFinalizationObserve table root context fuel
    ((forgeryLog, value.1), value.2)

set_option maxRecDepth 100000 in
theorem granularVerifierFinishObserve_eq_body
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    granularVerifierFinishObserve parameter root table ftsSecret context fuel value =
      directBoundaryObserve (probingRomImpl parameter)
        (scheme.verify ⟨root, parameter⟩ value.1.1.message value.1.1.signature)
        (granularVerifierResultObserve table root value.1)
        context fuel table value.2 := by
  unfold granularVerifierFinishObserve
  rw [directBoundaryObserve_bind]
  change directBoundaryObserve
      (maskedExpandedAdversaryImpl parameter root ftsSecret)
      (liftOracleWorldLeft
        (scheme.verify ⟨root, parameter⟩ value.1.1.message value.1.1.signature))
      (granularVerifierResultObserve table root value.1)
      context fuel table value.2 = _
  unfold maskedExpandedAdversaryImpl
  rw [directBoundaryObserve_liftOracleWorldLeft]

set_option maxRecDepth 100000 in
theorem directVerifierFinishObserve_eq_body
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    directVerifierFinishObserve table parameter root context fuel value =
      runDirectResolvedObserve (granularVerifierResultObserve table root value.1)
        context fuel table
          ((simulateQ (probingRomImpl parameter)
            (scheme.verify ⟨root, parameter⟩ value.1.1.message
              value.1.1.signature)).run value.2) := by
  unfold directVerifierFinishObserve canonicalVerifierFinish runDirectResolvedObserve
    granularVerifierResultObserve retainedResolvedFinalizationObserve
  simp only [StateT.run_bind, StateT.run_pure]
  rw [runDirectResolvedFromTable_bind_general]
  simp only [bind_assoc]
  apply bind_congr
  intro result
  cases result <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_failed_granularDetailedVerifierFinishObserve
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        granularDetailedVerifierFinishObserve parameter root table ftsSecret
          context fuel value) =
      evalDist (granularVerifierFinishObserve parameter root table ftsSecret
        context fuel value) := by
  unfold granularDetailedVerifierFinishObserve granularVerifierFinishObserve
  apply evalDist_failed_directDetailedBoundaryObserve
  · intro nextContext remaining nextValue hnextConsistent hnextStarts
    unfold retainedResolvedFinalizationDetailedObserve
      retainedResolvedFinalizationObserve
    exact evalDist_failed_classifyDirectObserve table (resolvedFinalizationObserve table)
      nextContext remaining ((root, nextValue.1), nextValue.2)
        hnextConsistent hnextStarts
  · exact hconsistent
  · exact hstarts

instance granularVerifierFinishObserve_observerDooms
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ObserverDooms table
      (granularVerifierFinishObserve parameter root table ftsSecret) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact directBoundaryObserve_dooms
      (maskedExpandedAdversaryImpl parameter root ftsSecret)
      (do
        let verified ← liftOracleWorldLeft
          (scheme.verify ⟨root, parameter⟩ value.1.1.message value.1.1.signature)
        pure (value.1, verified))
      (retainedResolvedFinalizationObserve table root)
      context fuel value.2 hconsistent hstarts hdoomed

noncomputable def splitGranularDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
    (granularDetailedVerifierFinishObserve parameter value.1 table ftsSecret)
    context fuel table value.2

set_option maxRecDepth 100000 in
theorem evalDist_failed_granularDetailedRetainedRestObserve_eq_split
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        granularDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (DirectBoundaryOutcome.failed <$>
        splitGranularDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) := by
  unfold granularDetailedRetainedRestObserve splitGranularDetailedRetainedRestObserve
    retainedGameRestComputation granularDetailedVerifierFinishObserve
  apply evalDist_failed_directDetailedBoundaryObserve_bind
    (observe := retainedResolvedFinalizationObserve table value.1)
  · intro nextContext remaining nextValue hnextConsistent hnextStarts
    unfold retainedResolvedFinalizationDetailedObserve
      retainedResolvedFinalizationObserve
    exact evalDist_failed_classifyDirectObserve table (resolvedFinalizationObserve table)
      nextContext remaining ((value.1, nextValue.1), nextValue.2)
        hnextConsistent hnextStarts
  · exact hconsistent
  · exact hstarts

set_option maxRecDepth 100000 in
theorem evalDist_failed_granularDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        granularDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (granularRetainedRestObserve adversary parameter table ftsSecret
        context fuel value) := by
  unfold granularDetailedRetainedRestObserve granularRetainedRestObserve
  apply evalDist_failed_directDetailedBoundaryObserve
  · intro nextContext remaining nextValue hnextConsistent hnextStarts
    unfold retainedResolvedFinalizationDetailedObserve
      retainedResolvedFinalizationObserve
    exact evalDist_failed_classifyDirectObserve table (resolvedFinalizationObserve table)
      nextContext remaining ((value.1, nextValue.1), nextValue.2)
        hnextConsistent hnextStarts
  · exact hconsistent
  · exact hstarts

noncomputable def granularDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryOrdinaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table value.2

theorem evalDist_ordinary_granularDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        granularDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (granularDetailedRetainedRestOrdinaryObserve adversary parameter table
        ftsSecret context fuel value) := by
  unfold granularDetailedRetainedRestObserve
    granularDetailedRetainedRestOrdinaryObserve
  apply evalDist_ordinary_directDetailedBoundaryObserve
  intro nextContext remaining nextValue
  unfold retainedResolvedFinalizationDetailedObserve
    retainedResolvedFinalizationOrdinaryObserve
  exact evalDist_ordinary_classifyDirectObserve table (resolvedFinalizationObserve table)
    nextContext remaining ((value.1, nextValue.1), nextValue.2)

noncomputable def retainedResolvedFinalizationPrivateObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) : ProbComp Bool :=
  classifyDirectPrivateObserve table (resolvedFinalizationObserve table)
    context fuel ((root, value.1), value.2)

noncomputable def granularDetailedRetainedRestPrivateObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryPrivateObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateObserve table value.1)
    context fuel table value.2

theorem evalDist_private_granularDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        granularDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (granularDetailedRetainedRestPrivateObserve adversary parameter table
        ftsSecret context fuel value) := by
  unfold granularDetailedRetainedRestObserve
    granularDetailedRetainedRestPrivateObserve
  apply evalDist_private_directDetailedBoundaryObserve
  intro nextContext remaining nextValue
  unfold retainedResolvedFinalizationDetailedObserve
    retainedResolvedFinalizationPrivateObserve
  exact evalDist_private_classifyDirectObserve table (resolvedFinalizationObserve table)
    nextContext remaining ((value.1, nextValue.1), nextValue.2)

noncomputable def granularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (granularDetailedRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def splitGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (splitGranularDetailedRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxRecDepth 100000 in
theorem evalDist_failed_granularAllDirectBoundaryDetailedRetainedOutcome_eq_split
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) =
      evalDist (DirectBoundaryOutcome.failed <$>
        splitGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) := by
  let initial : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  unfold granularAllDirectBoundaryDetailedRetainedOutcome
    splitGranularAllDirectBoundaryDetailedRetainedOutcome runDirectDetailedObserve
  rw [map_bind, map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result =>
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result hresult
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result
          DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hdirect
      simp only [finishDirectDetailedObserve]
      exact evalDist_failed_granularDetailedRetainedRestObserve_eq_split adversary parameter
        table ftsSecret result.context result.remaining result.value hcore.2.1 hcore.2.2

noncomputable def granularAllDirectBoundaryRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool :=
  runDirectResolvedObserve
    (granularRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_failed_granularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) =
      evalDist (granularAllDirectBoundaryRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) := by
  let initial : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  unfold granularAllDirectBoundaryDetailedRetainedOutcome
    granularAllDirectBoundaryRetainedFinishIsNone
  apply evalDist_failed_runDirectDetailedObserve
  intro result hresult
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
    (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result hresult
  have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
    (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result
      DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hdirect
  exact evalDist_failed_granularDetailedRetainedRestObserve adversary parameter table ftsSecret
    result.context result.remaining result.value hcore.2.1 hcore.2.2

noncomputable def materializedDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table
    ((simulateQ (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (retainedGameRestComputation adversary ⟨value.1, parameter⟩)).run value.2)

noncomputable def granularAllDirectBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (granularDetailedRetainedRestOrdinaryObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_ordinary_granularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) =
      evalDist (granularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter table
        ftsSecret fuel) := by
  unfold granularAllDirectBoundaryDetailedRetainedOutcome
    granularAllDirectBoundaryDetailedRetainedOrdinary
  apply evalDist_ordinary_runDirectDetailedObserve
  intro result _hresult
  exact evalDist_ordinary_granularDetailedRetainedRestObserve adversary parameter table
    ftsSecret result.context result.remaining result.value

noncomputable def granularAllDirectBoundaryDetailedRetainedPrivate
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool :=
  runDirectDetailedPrivateObserve
    (granularDetailedRetainedRestPrivateObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_private_granularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) =
      evalDist (granularAllDirectBoundaryDetailedRetainedPrivate adversary parameter table
        ftsSecret fuel) := by
  unfold granularAllDirectBoundaryDetailedRetainedOutcome
    granularAllDirectBoundaryDetailedRetainedPrivate
  apply evalDist_private_runDirectDetailedObserve
  intro result _hresult
  exact evalDist_private_granularDetailedRetainedRestObserve adversary parameter table
    ftsSecret result.context result.remaining result.value

noncomputable def materializedBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (materializedDetailedRetainedRestOrdinaryObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def materializedCanonicalPrivateRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryCanonicalMaterializedPrivateObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (fun _ _ _ => pure false) context fuel table value.2

noncomputable def materializedCanonicalDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryCanonicalMaterializedObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (fun _ _ _ => pure .success) context fuel table value.2

noncomputable def materializedCanonicalOrdinaryRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryCanonicalMaterializedOrdinaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table value.2

noncomputable def materializedCanonicalFullDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryCanonicalMaterializedObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (fun nextContext remaining nextValue =>
      DirectBoundaryOutcome.ofFailed <$>
        retainedResolvedFinalizationOrdinaryObserve table value.1
          nextContext remaining nextValue)
    context fuel table value.2

noncomputable def materializedCanonicalPrivateRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedPrivateObserve
    (materializedCanonicalPrivateRetainedRestObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def materializedCanonicalDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (materializedCanonicalDetailedRetainedRestObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def materializedCanonicalOrdinaryRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (materializedCanonicalOrdinaryRetainedRestObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def materializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (materializedCanonicalFullDetailedRetainedRestObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_private_materializedCanonicalDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        materializedCanonicalDetailedRetained adversary parameter table ftsSecret fuel) =
      evalDist
        (materializedCanonicalPrivateRetained adversary parameter table ftsSecret fuel) := by
  unfold materializedCanonicalDetailedRetained materializedCanonicalPrivateRetained
  apply evalDist_private_runDirectDetailedObserve
  intro result _hresult
  unfold materializedCanonicalDetailedRetainedRestObserve
    materializedCanonicalPrivateRetainedRestObserve
  apply evalDist_private_directDetailedBoundaryCanonicalMaterializedObserve
  intro nextContext remaining value
  simp [DirectBoundaryOutcome.privateStructural]

theorem evalDist_private_materializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        materializedCanonicalFullDetailedRetained adversary parameter table
          ftsSecret fuel) =
      evalDist
        (materializedCanonicalPrivateRetained adversary parameter table ftsSecret fuel) := by
  unfold materializedCanonicalFullDetailedRetained materializedCanonicalPrivateRetained
  apply evalDist_private_runDirectDetailedObserve
  intro result _hresult
  unfold materializedCanonicalFullDetailedRetainedRestObserve
    materializedCanonicalPrivateRetainedRestObserve
  apply evalDist_private_directDetailedBoundaryCanonicalMaterializedObserve
  intro nextContext remaining value
  let observe := retainedResolvedFinalizationOrdinaryObserve table result.value.1
    nextContext remaining value
  have hprojection :
      (fun hit : Bool => (DirectBoundaryOutcome.ofFailed hit).privateStructural) =
        fun _ => false := by
    funext hit
    cases hit <;> rfl
  rw [Functor.map_map]
  rw [hprojection]
  change evalDist ((fun _ : Bool => false) <$> observe) =
    evalDist (pure false : ProbComp Bool)
  simp only [map_eq_bind_pure_comp]
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    observe (by simp [observe, retainedResolvedFinalizationOrdinaryObserve]) (pure false)

theorem evalDist_ordinary_materializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        materializedCanonicalFullDetailedRetained adversary parameter table
          ftsSecret fuel) =
      evalDist
        (materializedCanonicalOrdinaryRetained adversary parameter table ftsSecret fuel) := by
  unfold materializedCanonicalFullDetailedRetained materializedCanonicalOrdinaryRetained
  apply evalDist_ordinary_runDirectDetailedObserve
  intro result _hresult
  unfold materializedCanonicalFullDetailedRetainedRestObserve
    materializedCanonicalOrdinaryRetainedRestObserve
  apply evalDist_ordinary_directDetailedBoundaryCanonicalMaterializedObserve
  intro nextContext remaining value
  have hprojection :
      (fun hit : Bool => (DirectBoundaryOutcome.ofFailed hit).ordinary) = id := by
    funext hit
    cases hit <;> rfl
  rw [Functor.map_map]
  rw [hprojection]
  simp

noncomputable def sampledMaterializedCanonicalPrivateRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  materializedCanonicalPrivateRetained adversary parameter table ftsSecret fuel

noncomputable def sampledMaterializedCanonicalDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  materializedCanonicalDetailedRetained adversary parameter table ftsSecret fuel

noncomputable def sampledMaterializedCanonicalOrdinaryRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  materializedCanonicalOrdinaryRetained adversary parameter table ftsSecret fuel

noncomputable def sampledMaterializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  materializedCanonicalFullDetailedRetained adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_private_sampledMaterializedCanonicalDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        sampledMaterializedCanonicalDetailedRetained adversary parameter ftsSecret fuel) =
      evalDist
        (sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret fuel) := by
  unfold sampledMaterializedCanonicalDetailedRetained
    sampledMaterializedCanonicalPrivateRetained
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_private_materializedCanonicalDetailedRetained adversary parameter table
    ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_private_sampledMaterializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        sampledMaterializedCanonicalFullDetailedRetained adversary parameter
          ftsSecret fuel) =
      evalDist
        (sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret fuel) := by
  unfold sampledMaterializedCanonicalFullDetailedRetained
    sampledMaterializedCanonicalPrivateRetained
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_private_materializedCanonicalFullDetailedRetained adversary parameter table
    ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_ordinary_sampledMaterializedCanonicalFullDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        sampledMaterializedCanonicalFullDetailedRetained adversary parameter
          ftsSecret fuel) =
      evalDist
        (sampledMaterializedCanonicalOrdinaryRetained adversary parameter ftsSecret fuel) := by
  unfold sampledMaterializedCanonicalFullDetailedRetained
    sampledMaterializedCanonicalOrdinaryRetained
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_ordinary_materializedCanonicalFullDetailedRetained adversary parameter table
    ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_privateStructuralFailure_sampledMaterializedCanonicalDetailedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= .privateStructuralFailure |
        sampledMaterializedCanonicalDetailedRetained adversary parameter ftsSecret fuel] =
      Pr[= true |
        sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret fuel] := by
  rw [probEvent_privateStructuralFailure_eq_map_privateStructural]
  exact OracleComp.probOutput_congr rfl
      (evalDist_private_sampledMaterializedCanonicalDetailedRetained adversary parameter
        ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_failed_sampledMaterializedCanonicalFullDetailedRetained_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun outcome => outcome.failed = true |
        sampledMaterializedCanonicalFullDetailedRetained adversary parameter
          ftsSecret fuel] ≤
      Pr[= true |
          sampledMaterializedCanonicalOrdinaryRetained adversary parameter
            ftsSecret fuel] +
        Pr[= true |
          sampledMaterializedCanonicalPrivateRetained adversary parameter
            ftsSecret fuel] := by
  calc
    _ ≤ Pr[= .ordinaryFailure |
          sampledMaterializedCanonicalFullDetailedRetained adversary parameter
            ftsSecret fuel] +
        Pr[= .privateStructuralFailure |
          sampledMaterializedCanonicalFullDetailedRetained adversary parameter
            ftsSecret fuel] :=
      probEvent_failed_le_ordinary_add_private
        (sampledMaterializedCanonicalFullDetailedRetained adversary parameter
          ftsSecret fuel)
    _ = _ := by
      rw [probEvent_ordinaryFailure_eq_map_ordinary,
        probEvent_privateStructuralFailure_eq_map_privateStructural]
      apply congrArg₂ (· + ·)
      · exact OracleComp.probOutput_congr rfl
          (evalDist_ordinary_sampledMaterializedCanonicalFullDetailedRetained
            adversary parameter ftsSecret fuel)
      · exact OracleComp.probOutput_congr rfl
          (evalDist_private_sampledMaterializedCanonicalFullDetailedRetained
            adversary parameter ftsSecret fuel)

set_option maxRecDepth 100000 in
theorem fuel_le_remaining_of_done_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    fuel ≤ result.remaining := by
  have hdirect : some result ∈ support
      (runDirectResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) :=
    mem_support_runDirectResolvedFromTable_of_done_detailed
      (alpha := Digest × SplitHashCache)
      (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
      (context :=
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues })
      (fuel := fuel) (table := table) (result := result) hresult
  have hraw : LazyRevealProbe.RawResult.done result.context.state result.remaining result.value ∈
      support (LazyRevealProbe.runRaw
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (maskedPublishedTreeRoot.run emptySplitHashCache)) :=
    raw_done_of_mem_runDirectResolvedFromTable
      (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
      (context :=
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues })
      (fuel := fuel) (table := table) (result := result) hdirect
  have hremaining := LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    result.context.state fuel result.remaining 0
    (maskedPublishedTreeRoot.run emptySplitHashCache) result.value
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hraw
  simpa using hremaining

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllDirectBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    RelTriple
      (granularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret q)
      (materializedBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret q)
      BoolImp := by
  unfold granularAllDirectBoundaryDetailedRetainedOrdinary
    materializedBoundaryDetailedRetainedOrdinary
  apply relTriple_runDirectDetailedOrdinaryObserve_maskedPublishedTreeRoot table q
  · intro leftResult rightResult hleftMem _hrightMem hrelation
    have hremaining : q ≤ leftResult.remaining :=
      fuel_le_remaining_of_done_maskedPublishedTreeRoot
        table q leftResult hleftMem
    have hbound := isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter
      hparameter table ftsSecret hfts leftResult.value.1
    have htailBound := hbound.mono (by simpa using hremaining)
    have hroot : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    unfold granularDetailedRetainedRestOrdinaryObserve
      materializedDetailedRetainedRestOrdinaryObserve
    rw [← hroot]
    exact relTriple_directDetailedRetainedRestOrdinaryObserve adversary parameter
      leftResult.value.1 table ftsSecret leftResult.context rightResult.context
      leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
      hrelation.context_le hrelation.remaining_le hrelation.cache_eq hrelation.revealed_eq
      hrelation.values_le hrelation.left_published hrelation.right_materialized htailBound
  · intro result _hresult hdoomed
    unfold materializedDetailedRetainedRestOrdinaryObserve
    exact evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed table
      ((simulateQ (maskedExpandedAdversaryImpl parameter result.value.1 ftsSecret)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)).run
          result.value.2)
      (retainedResolvedFinalizationOrdinaryObserve table result.value.1)
      result.context result.remaining hdoomed.1.2 hdoomed.2
      (fun finalResult _hfinal hfinalDoomed hfinalMaterialized => by
        have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
          finalResult.context hfinalMaterialized
        simp [retainedResolvedFinalizationOrdinaryObserve,
          classifyDirectOrdinaryObserve, hnotPrivate, hfinalDoomed.2.2.2])

noncomputable def materializedFlatResolvedFinalizationOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table))
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (deferredCleanRetainedRun adversary parameter ftsSecret)

set_option maxRecDepth 100000 in
theorem deferredCleanRetainedRun_eq_retainedGameRest_bind
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    deferredCleanRetainedRun adversary parameter ftsSecret = (do
      let rootResult ← maskedPublishedTreeRoot.run emptySplitHashCache
      let restResult ←
        (simulateQ
          (maskedExpandedAdversaryImpl parameter rootResult.1 ftsSecret)
          (retainedGameRestComputation adversary ⟨rootResult.1, parameter⟩)).run
            rootResult.2
      pure ((rootResult.1, restResult.1), restResult.2)) := by
  rw [deferredCleanRetainedRun_eq_boundary_bind]
  apply bind_congr
  intro rootResult
  rw [simulateQ_maskedExpanded_retainedGameRestComputation]
  unfold canonicalVerifierFinish
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

set_option maxRecDepth 100000 in
theorem evalDist_materializedBoundaryDetailedRetainedOrdinary_eq_flat
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (materializedBoundaryDetailedRetainedOrdinary adversary parameter table
        ftsSecret fuel) =
      evalDist (materializedFlatResolvedFinalizationOrdinary adversary parameter table
        ftsSecret fuel) := by
  unfold materializedBoundaryDetailedRetainedOrdinary
    materializedDetailedRetainedRestOrdinaryObserve
    retainedResolvedFinalizationOrdinaryObserve
    materializedFlatResolvedFinalizationOrdinary
  rw [deferredCleanRetainedRun_eq_retainedGameRest_bind]
  rw [evalDist_runDirectDetailedOrdinaryObserve_bind]
  · apply evalDist_bind_congr
    intro result hresult
    cases result with
    | stopped reason => cases reason <;> rfl
    | done result =>
        simp only [finishDirectDetailedOrdinaryObserve]
        symm
        apply evalDist_runDirectDetailedOrdinaryObserve_bind
        · have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (directDeferredContext
              (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
            fuel table result hresult
          exact (resolvedCore_of_mem_runDirectResolvedFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (directDeferredContext
              (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
            fuel table result DeferredContext.valid_empty.valuesConsistent
              (startTableAgrees_empty table) hdirect).2.1
        · have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (directDeferredContext
              (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
            fuel table result hresult
          exact (resolvedCore_of_mem_runDirectResolvedFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (directDeferredContext
              (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
            fuel table result DeferredContext.valid_empty.valuesConsistent
              (startTableAgrees_empty table) hdirect).2.2
  · exact DeferredContext.valid_empty.valuesConsistent
  · exact startTableAgrees_empty table

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailedOrdinaryResolvedFinalization_materialized_eq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hconsistent : (directDeferredContext state).ValuesConsistent)
    (hstarts : StartTableAgrees state table) :
    evalDist
      (runDirectDetailedOrdinaryObserve
        (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table))
        (directDeferredContext state) fuel table computation) =
      evalDist
        (runDirectResolvedFromTable (directDeferredContext state) fuel table computation >>=
          finishResolvedRunIsNone) := by
  unfold runDirectDetailedOrdinaryObserve
  rw [← map_toOption_runDirectResolvedDetailedFromTable computation
    (directDeferredContext state) fuel table]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply evalDist_bind_congr
  intro result hresult
  have hmaterialized :=
    directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
      computation state fuel table result hresult
  cases result with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => contradiction
      | ordinaryHit => rfl
      | fuelExhausted => rfl
  | done result =>
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        computation (directDeferredContext state) fuel table result hresult
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable computation
        (directDeferredContext state) fuel table result hconsistent hstarts hdirect
      rcases result with ⟨resultContext, remaining, value, resultTable⟩
      dsimp only at hcore hmaterialized ⊢
      have htable : resultTable = table := hcore.1
      subst resultTable
      have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
        resultContext hmaterialized
      by_cases hcompletable : DeferredCompletable table resultContext
      · simp [finishDirectDetailedOrdinaryObserve, classifyDirectOrdinaryObserve,
          resolvedFinalizationObserve, DirectDetailedResult.toOption,
          hnotPrivate, hcompletable]
      · simp [finishDirectDetailedOrdinaryObserve, classifyDirectOrdinaryObserve,
          DirectDetailedResult.toOption, finishResolvedRunIsNone, finishResolvedRun,
          hnotPrivate, hcompletable]

noncomputable def sampledMaterializedBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  materializedBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret fuel

noncomputable def sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel

noncomputable def sampledSplitGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  splitGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel

noncomputable def sampledGranularAllDirectBoundaryRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryRetainedFinishIsNone adversary parameter table ftsSecret fuel

noncomputable def sampledGranularAllDirectBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret fuel

noncomputable def sampledGranularAllDirectBoundaryDetailedRetainedPrivate
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryDetailedRetainedPrivate adversary parameter table ftsSecret fuel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllDirectBoundaryDetailedRetainedOrdinary_materialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    RelTriple
      (sampledGranularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret q)
      (sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret q)
      BoolImp := by
  unfold sampledGranularAllDirectBoundaryDetailedRetainedOrdinary
    sampledMaterializedBoundaryDetailedRetainedOrdinary
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  exact relTriple_granularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
    leftTable ftsSecret q hq hparameter hfts

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledGranularAllDirectBoundaryDetailedRetainedOrdinary_le_materialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[= true |
        sampledGranularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
          ftsSecret q] ≤
      Pr[= true |
        sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
          ftsSecret q] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple
    (relTriple_sampledGranularAllDirectBoundaryDetailedRetainedOrdinary_materialized
      adversary parameter ftsSecret q hq hparameter hfts)
  intro leftValue rightValue himp hleft
  exact himp hleft

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_sampledMaterializedBoundaryDetailedRetainedOrdinary_eq_flat
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist
        (sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
          ftsSecret fuel) =
      evalDist (do
        let table ← sampleOtsHashTable
        materializedFlatResolvedFinalizationOrdinary adversary parameter table
          ftsSecret fuel) := by
  unfold sampledMaterializedBoundaryDetailedRetainedOrdinary
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro table
  exact evalDist_materializedBoundaryDetailedRetainedOrdinary_eq_flat adversary parameter
    table ftsSecret fuel

set_option maxRecDepth 100000 in
theorem evalDist_finishDirectRunIsNone_eq_true_of_missingChainStartHit
    (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) (fuel : Nat) (value : α)
    (hmissing : MissingChainStartHit table (directDeferredContext state)) :
    evalDist (finishDirectRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) =
      evalDist (pure true : ProbComp Bool) := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  have hstateValue : state.values index.coordinate = none := by
    simpa only [directDeferredContext] using hvalue
  have hmem : index.coordinate ∈ state.coordinates := by
    by_contra hnotMem
    exact (not_hitAt_of_not_mem_coordinates state index.coordinate (table index) hnotMem) hhit
  have hexpose := evalDist_finalizeCleanFromTable_finset_expose_missing
    index.coordinate state.coordinates state table hmem hstateValue
  unfold finishDirectRunIsNone finishCleanRunIsNone projectResolvedRunResult
  simp only [finishCleanRunFromTable, map_bind]
  simp only [directDeferredContext]
  rw [evalDist_bind, hexpose, ← evalDist_bind]
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  have hhitState : state.hitAt (.chainStart lay tree leafIdx chainIdx)
      (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
    simpa only [directDeferredContext, OtsSecretIndex.coordinate] using hhit
  simp [OtsSecretIndex.coordinate, completionOutputFromTable, hhitState]

set_option maxRecDepth 100000 in
theorem evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone_of_materialized
    (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) (fuel : Nat) (value : α)
    (hvalid : (directDeferredContext state).Valid)
    (hstarts : StartTableAgrees state table)
    (hcard : state.pending.card < Fintype.card Digest) :
    evalDist (finishResolvedRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) =
      evalDist (finishDirectRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) := by
  by_cases hcompletable : DeferredCompletable table (directDeferredContext state)
  · exact evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone
      state fuel value table hcompletable
  · have hcause := privateStructuralHit_or_missingChainStartHit_of_not_completable
      table (directDeferredContext state) hvalid hstarts hcard hcompletable
    have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
      (directDeferredContext state) rfl
    have hmissing : MissingChainStartHit table (directDeferredContext state) :=
      hcause.resolve_left hnotPrivate
    calc
      _ = evalDist (pure true : ProbComp Bool) := by
        simp [finishResolvedRunIsNone, finishResolvedRun, hcompletable]
      _ = _ :=
        (evalDist_finishDirectRunIsNone_eq_true_of_missingChainStartHit
          state table fuel value hmissing).symm

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_ordinary_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) =
      evalDist (sampledGranularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret fuel) := by
  unfold sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    sampledGranularAllDirectBoundaryDetailedRetainedOrdinary
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_ordinary_granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
    table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_private_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.privateStructural <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) =
      evalDist (sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
        ftsSecret fuel) := by
  unfold sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    sampledGranularAllDirectBoundaryDetailedRetainedPrivate
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_private_granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
    table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) =
      evalDist (sampledGranularAllDirectBoundaryRetainedFinishIsNone adversary parameter
        ftsSecret fuel) := by
  unfold sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    sampledGranularAllDirectBoundaryRetainedFinishIsNone
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_failed_granularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
    table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome_eq_split
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) =
      evalDist (DirectBoundaryOutcome.failed <$>
        sampledSplitGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) := by
  unfold sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    sampledSplitGranularAllDirectBoundaryDetailedRetainedOutcome
  rw [map_bind, map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_failed_granularAllDirectBoundaryDetailedRetainedOutcome_eq_split adversary
    parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun outcome => outcome.failed = true |
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] =
      Pr[= true |
        sampledGranularAllDirectBoundaryRetainedFinishIsNone adversary parameter
          ftsSecret fuel] := by
  calc
    _ = Pr[fun hit : Bool => hit = true | DirectBoundaryOutcome.failed <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] := by
      rw [probEvent_map]
      rfl
    _ = Pr[= true | DirectBoundaryOutcome.failed <$>
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] := probEvent_eq_eq_probOutput _ true
    _ = _ := OracleComp.probOutput_congr rfl
      (evalDist_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary
        parameter ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_ordinaryFailure_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= .ordinaryFailure |
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] =
      Pr[= true |
        sampledGranularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
          ftsSecret fuel] := by
  rw [probEvent_ordinaryFailure_eq_map_ordinary]
  exact OracleComp.probOutput_congr rfl
    (evalDist_ordinary_sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary
      parameter ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_privateStructuralFailure_sampledGranularAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= .privateStructuralFailure |
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] =
      Pr[= true |
        sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
          ftsSecret fuel] := by
  rw [probEvent_privateStructuralFailure_eq_map_privateStructural]
  exact OracleComp.probOutput_congr rfl
    (evalDist_private_sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary
      parameter ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome_le_materialized_add_private
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun outcome => outcome.failed = true |
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret q] ≤
      Pr[= true |
          sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
            ftsSecret q] +
        Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] := by
  calc
    _ ≤ Pr[= .ordinaryFailure |
          sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
            ftsSecret q] +
        Pr[= .privateStructuralFailure |
          sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
            ftsSecret q] :=
      probEvent_failed_le_ordinary_add_private
        (sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret q)
    _ = Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter
            ftsSecret q] +
        Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] := by
      rw [probEvent_ordinaryFailure_sampledGranularAllDirectBoundaryDetailedRetainedOutcome,
        probEvent_privateStructuralFailure_sampledGranularAllDirectBoundaryDetailedRetainedOutcome]
    _ ≤ _ := add_le_add
      (probEvent_sampledGranularAllDirectBoundaryDetailedRetainedOrdinary_le_materialized
        adversary parameter ftsSecret q hq hparameter hfts) le_rfl

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome_le_two_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (hmaterialized :
      Pr[= true |
          sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
            ftsSecret q] ≤
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (hprivate :
      Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] ≤
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun outcome => outcome.failed = true |
        sampledGranularAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret q] ≤
      ((2 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[= true |
          sampledMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
            ftsSecret q] +
        Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] :=
      probEvent_failed_sampledGranularAllDirectBoundaryDetailedRetainedOutcome_le_materialized_add_private
        adversary parameter ftsSecret q hq hparameter hfts
    _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add hmaterialized hprivate
    _ = _ := by
      push_cast
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation
