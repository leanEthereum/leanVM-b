import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdministrative
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedChain

/-!
# Adaptive selected-root lift

The first-stopped step relation is consumed without forgetting the shared continuation. Clean
steps recurse, failed materialized steps make the real indicator false, and a persistent missing
chain start contradicts successful finalization.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem cleanProbeObservation_materializedDeferredState_eq_of_position
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (position : Position) (candidate : Digest)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hrightMaterialized : right = directDeferredContext right.state) :
    cleanProbeObservation (materializedDeferredState left) (.position position) candidate =
      cleanProbeObservation right.state (.position position) candidate := by
  unfold cleanProbeObservation
  have hvalue := congrFun hcontext.view.valueEq (.position position)
  simp only [resolvedCompletionValue] at hvalue
  rw [hrightMaterialized] at hvalue
  simp only [directDeferredContext, directDeferredValues, DeferredContext.positionValue] at hvalue
  have hvalue' : left.positionValue position =
      right.state.values (.position position) := by
    cases hrightValue : right.state.values (.position position) <;>
      simpa [DeferredContext.positionValue, hrightValue] using hvalue
  simp only [materializedDeferredState_position, hvalue', materializedDeferredState_revealed,
    hrevealed]

theorem not_existingHiddenHit_cleanProbeObservation_materializedDeferredState
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (coordinate : Coordinate) (candidate : Digest)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hactual : ¬(cleanProbeObservation right.state coordinate candidate).ExistingHiddenHit) :
    ¬(cleanProbeObservation (materializedDeferredState left) coordinate candidate).ExistingHiddenHit := by
  cases coordinate with
  | position position =>
      rw [cleanProbeObservation_materializedDeferredState_eq_of_position table left right
        position candidate hcontext hrevealed hrightMaterialized]
      exact hactual
  | chainStart lay tree leafIdx chainIdx =>
      rintro ⟨hhidden, output, hvalue, hcandidate⟩
      apply hactual
      refine ⟨?_, output, ?_, hcandidate⟩
      · simpa [cleanProbeObservation, materializedDeferredState_revealed, hrevealed] using hhidden
      · have hleftValue : left.state.values
            (.chainStart lay tree leafIdx chainIdx) = some output := by
          simpa [cleanProbeObservation, materializedDeferredState_chainStart] using hvalue
        simpa [cleanProbeObservation] using hvalues _ output hleftValue

theorem materializedDeferredState_values_eq_of_chainValid
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hchainValid : ChainState.ValidFor (fun _ => True) right.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    (materializedDeferredState left).values = right.state.values := by
  funext coordinate
  cases coordinate with
  | position position =>
      have hvalue := congrFun hcontext.view.valueEq (.position position)
      rw [hrightMaterialized] at hvalue
      cases hrightValue : right.state.values (.position position) <;>
        simpa [resolvedCompletionValue, DeferredContext.positionValue,
          directDeferredContext, directDeferredValues, hrightValue] using hvalue
  | chainStart lay tree leafIdx chainIdx =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      cases hrightValue : right.state.values index.coordinate with
      | none =>
          have hleftValue : left.state.values index.coordinate = none := by
            by_contra hne
            obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hne
            have := hvalues index.coordinate output houtput
            rw [hrightValue] at this
            simp at this
          change left.state.values index.coordinate = right.state.values index.coordinate
          rw [hrightValue]
          exact hleftValue
      | some output =>
          have hrightRevealed : index.coordinate ∈ right.state.revealed :=
            (hchainValid index.coordinate (by simp [index, OtsSecretIndex.coordinate,
              IsChainCoordinate])).1 (by simp [hrightValue])
          have hleftRevealed : index.coordinate ∈ left.state.revealed := by
            rwa [hrevealed]
          have hleftKnown := hpublished index.coordinate hleftRevealed
          obtain ⟨leftOutput, hleftValue⟩ := Option.ne_none_iff_exists'.mp hleftKnown
          have hleftTable := hcontext.view.leftStarts index leftOutput hleftValue
          have hrightTable := hcontext.view.rightStarts index output (by
              rw [hrightMaterialized]
              simpa [directDeferredContext] using hrightValue)
          change left.state.values index.coordinate = right.state.values index.coordinate
          rw [hrightValue]
          exact hleftValue.trans (congrArg some (hleftTable.trans hrightTable.symm))

structure CompletionSafeStateLE
    (table : OtsSecretIndex → HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  values : left.values = right.values
  revealed : left.revealed = right.revealed
  pending : ∀ coordinate candidate,
    (coordinate, candidate) ∈ left.pending →
      (coordinate, candidate) ∈ right.pending ∨
        (∃ output, left.values coordinate = some output ∧
          candidate ≠ truncateHash output) ∨
        ∃ index : OtsSecretIndex,
          coordinate = index.coordinate ∧ candidate ≠ truncateHash (table index)

theorem CompletionSafeStateLE.refl
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) :
    CompletionSafeStateLE table state state :=
  ⟨rfl, rfl, fun _ _ hentry ↦ Or.inl hentry⟩

theorem CompletionSafeStateLE.ensure
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right) (coordinate : Coordinate) :
    CompletionSafeStateLE table (left.ensure coordinate) (right.ensure coordinate) := by
  exact ⟨hstate.values, hstate.revealed, hstate.pending⟩

theorem CompletionSafeStateLE.publish
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right) (coordinate : Coordinate) :
    CompletionSafeStateLE table (left.publish coordinate) (right.publish coordinate) := by
  refine ⟨hstate.values, ?_, hstate.pending⟩
  simp [LazyRevealProbe.State.publish, hstate.revealed]

theorem CompletionSafeStateLE.addPending
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (coordinate : Coordinate) (candidate : Digest) :
    CompletionSafeStateLE table
      (left.addPending coordinate candidate) (right.addPending coordinate candidate) := by
  refine ⟨hstate.values, hstate.revealed, ?_⟩
  intro other otherCandidate hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry ⊢
  rcases hentry with hnew | hold
  · exact Or.inl (Or.inl hnew)
  · rcases hstate.pending other otherCandidate hold with hright | hsafe
    · exact Or.inl (Or.inr hright)
    · exact Or.inr hsafe

theorem CompletionSafeStateLE.clearPending
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right) (coordinate : Coordinate) :
    CompletionSafeStateLE table
      (left.clearPending coordinate) (right.clearPending coordinate) := by
  refine ⟨hstate.values, hstate.revealed, ?_⟩
  intro other candidate hentry
  simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
    Finset.mem_filter] at hentry ⊢
  rcases hstate.pending other candidate hentry.1 with hright | hsafe
  · exact Or.inl ⟨hright, hentry.2⟩
  · exact Or.inr hsafe

theorem CompletionSafeStateLE.materialize
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (coordinate : Coordinate) (output : HashOutput) :
    CompletionSafeStateLE table
      (left.materialize coordinate output) (right.materialize coordinate output) := by
  refine ⟨?_, hstate.revealed, ?_⟩
  · simp [LazyRevealProbe.State.materialize, hstate.values]
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hstate.pending other candidate hentry.1 with hright | hsafe
    · exact Or.inl ⟨hright, hentry.2⟩
    · rcases hsafe with ⟨known, hknown, hmiss⟩ | hchain
      · right
        left
        by_cases heq : other = coordinate
        · exact (hentry.2 heq).elim
        · refine ⟨known, ?_, hmiss⟩
          simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hknown
      · exact Or.inr (Or.inr hchain)

theorem CompletionSafeStateLE.complete
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (coordinate : Coordinate) (output : HashOutput) :
    CompletionSafeStateLE table
      (left.complete coordinate output) (right.complete coordinate output) := by
  refine ⟨?_, hstate.revealed, ?_⟩
  · simp [LazyRevealProbe.State.complete, hstate.values]
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hstate.pending other candidate hentry.1 with hright | hsafe
    · exact Or.inl ⟨hright, hentry.2⟩
    · rcases hsafe with ⟨known, hknown, hmiss⟩ | hchain
      · right
        left
        by_cases heq : other = coordinate
        · exact (hentry.2 heq).elim
        · refine ⟨known, ?_, hmiss⟩
          simpa [LazyRevealProbe.State.complete, Function.update_of_ne heq] using hknown
      · exact Or.inr (Or.inr hchain)

theorem CompletionSafeStateLE.not_hitAt_left_of_right
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (coordinate : Coordinate) (output : HashOutput)
    (hleftValue : left.values coordinate = none)
    (hcompletion : ∀ index : OtsSecretIndex,
      coordinate = index.coordinate → output = table index)
    (hrightMiss : ¬right.hitAt coordinate output) :
    ¬left.hitAt coordinate output := by
  intro hleftHit
  have hentry : (coordinate, truncateHash output) ∈ left.pending := by
    rwa [← LazyRevealProbe.State.mem_pendingAt_iff]
  rcases hstate.pending coordinate (truncateHash output) hentry with
    hright | ⟨known, hknown, _hmiss⟩ | ⟨index, hcoordinate, hmiss⟩
  · apply hrightMiss
    rwa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff]
  · rw [hleftValue] at hknown
    simp at hknown
  · exact hmiss (congrArg truncateHash (hcompletion index hcoordinate))

theorem doomed_direct_addPending_of_stored
    {table : OtsSecretIndex → HashOutput}
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput)
    (hvalue : state.values coordinate = some output)
    (hstarts : StartTableAgrees state table) :
    DoomedResolvedContext table
      (directDeferredContext
        (state.addPending coordinate (truncateHash output))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro position stored hstored
    simpa [directDeferredContext, directDeferredValues] using hstored
  · intro index stored hstored
    apply hstarts index stored
    simpa [directDeferredContext, LazyRevealProbe.State.addPending] using hstored
  · rintro ⟨completion, hcompletion⟩
    have hcompletionValue : completion coordinate = output :=
      hcompletion.1 coordinate output (by
        simpa [directDeferredContext, LazyRevealProbe.State.addPending] using hvalue)
    have havoids := hcompletion.2.2.1 coordinate (truncateHash output) (by
      simp [directDeferredContext, LazyRevealProbe.State.addPending])
    exact havoids (by rw [hcompletionValue])

set_option maxRecDepth 100000 in
theorem relTriple_map_isSome_finalizeCleanFromTable_completionSafe
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate)
    (left right : LazyRevealProbe.State Coordinate)
    (hstate : CompletionSafeStateLE table left right) :
    RelTriple
      (Option.isSome <$> finalizeCleanFromTable coordinates right table)
      (Option.isSome <$> finalizeCleanFromTable coordinates left table)
      BoolImp := by
  induction coordinates generalizing left right with
  | nil => simp [finalizeCleanFromTable, BoolImp]
  | cons coordinate remaining ih =>
      rw [finalizeCleanFromTable.eq_def, finalizeCleanFromTable.eq_def]
      have hvalue : left.values coordinate = right.values coordinate :=
        congrFun hstate.values coordinate
      cases hrightValue : right.values coordinate with
      | some output =>
          have hleftValue : left.values coordinate = some output := by
            rw [hvalue, hrightValue]
          simp only [hrightValue, hleftValue]
          exact ih (left.clearPending coordinate) (right.clearPending coordinate)
            (hstate.clearPending coordinate)
      | none =>
          have hleftValue : left.values coordinate = none := by
            rw [hvalue, hrightValue]
          simp only [hrightValue, hleftValue]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              let output := table index
              change RelTriple
                (Option.isSome <$> if right.hitAt index.coordinate output then pure none else
                  finalizeCleanFromTable remaining (right.complete index.coordinate output) table)
                (Option.isSome <$> if left.hitAt index.coordinate output then pure none else
                  finalizeCleanFromTable remaining (left.complete index.coordinate output) table)
                BoolImp
              by_cases hrightHit : right.hitAt index.coordinate output
              · simp only [hrightHit, ↓reduceIte, map_pure]
                exact relTriple_false_any _
              · have hleftHit : ¬left.hitAt index.coordinate output :=
                  hstate.not_hitAt_left_of_right index.coordinate output hleftValue
                    (by
                      intro other hcoordinate
                      have heq : other = index :=
                        OtsSecretIndex.coordinate_injective hcoordinate.symm
                      subst other
                      rfl)
                    hrightHit
                simp only [hrightHit, hleftHit, ↓reduceIte]
                exact ih (left.complete index.coordinate output)
                  (right.complete index.coordinate output) (hstate.complete _ output)
          | position position =>
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
              intro leftOutput rightOutput houtput
              subst rightOutput
              by_cases hrightHit : right.hitAt (.position position) leftOutput
              · simp only [hrightHit, ↓reduceIte, map_pure]
                exact relTriple_false_any _
              · have hleftHit : ¬left.hitAt (.position position) leftOutput :=
                  hstate.not_hitAt_left_of_right (.position position) leftOutput hleftValue
                    (by intro index hcoordinate; cases hcoordinate) hrightHit
                simp only [hrightHit, hleftHit, ↓reduceIte]
                simpa [map_eq_bind_pure_comp] using
                  (ih (left.complete (.position position) leftOutput)
                    (right.complete (.position position) leftOutput)
                    (hstate.complete _ leftOutput))

set_option maxRecDepth 100000 in
theorem exists_successful_finalizeCleanFromTable
    (table : OtsSecretIndex → HashOutput) :
    ∀ (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate),
      coordinates.Nodup →
      (∀ entry ∈ state.pending, entry.1 ∈ coordinates) →
      ¬MissingChainStartHit table (directDeferredContext state) →
      (∀ position, state.values (.position position) = none →
        (state.pendingAt (.position position)).card < Fintype.card Digest) →
      ∃ final, some final ∈ support (finalizeCleanFromTable coordinates state table)
  | [], state, _hnodup, _hcovered, _hstart, _hcard => by
      exact ⟨(state, table), by simp [finalizeCleanFromTable]⟩
  | coordinate :: remaining, state, hnodup, hcovered, hstart, hcard => by
      have hnotMem : coordinate ∉ remaining := (List.nodup_cons.mp hnodup).1
      have nextCovered : ∀ (nextState : LazyRevealProbe.State Coordinate),
          nextState.pending ⊆ state.pending →
          (∀ entry ∈ nextState.pending, entry.1 ≠ coordinate) →
          ∀ entry ∈ nextState.pending, entry.1 ∈ remaining := by
        intro nextState hsubset haway entry hentry
        have horiginal := hcovered entry (hsubset hentry)
        simp only [List.mem_cons] at horiginal
        exact horiginal.resolve_left (fun heq ↦ haway entry hentry heq)
      have nextStart : ∀ (nextState : LazyRevealProbe.State Coordinate),
          nextState.pending ⊆ state.pending →
          (∀ other, other ≠ coordinate → nextState.values other = state.values other) →
          nextState.values coordinate ≠ none →
          ¬MissingChainStartHit table (directDeferredContext nextState) := by
        intro nextState hsubset hvalues hcoordinateValue
        rintro ⟨index, hvalue, hhit⟩
        by_cases heq : index.coordinate = coordinate
        · exact hcoordinateValue (by simpa [directDeferredContext, heq] using hvalue)
        · apply hstart
          refine ⟨index, ?_, ?_⟩
          · simpa only [directDeferredContext, hvalues index.coordinate heq] using hvalue
          · unfold LazyRevealProbe.State.hitAt at hhit ⊢
            rw [LazyRevealProbe.State.mem_pendingAt_iff]
            apply hsubset
            exact (LazyRevealProbe.State.mem_pendingAt_iff nextState index.coordinate
              (truncateHash (table index))).1 (by simpa only [directDeferredContext] using hhit)
      cases hvalue : state.values coordinate with
      | some output =>
          simp only [finalizeCleanFromTable, hvalue]
          apply exists_successful_finalizeCleanFromTable table remaining
            (state.clearPending coordinate)
          · exact hnodup.tail
          · apply nextCovered
            · intro entry hentry
              have hentry' : entry ∈ state.pending ∧ entry.1 ≠ coordinate := by
                simpa [LazyRevealProbe.State.clearPending,
                  LazyRevealProbe.State.pendingAway] using hentry
              exact hentry'.1
            · intro entry hentry
              have hentry' : entry ∈ state.pending ∧ entry.1 ≠ coordinate := by
                simpa [LazyRevealProbe.State.clearPending,
                  LazyRevealProbe.State.pendingAway] using hentry
              exact hentry'.2
          · apply nextStart (state.clearPending coordinate)
            · intro entry hentry
              have hentry' : entry ∈ state.pending ∧ entry.1 ≠ coordinate := by
                simpa [LazyRevealProbe.State.clearPending,
                  LazyRevealProbe.State.pendingAway] using hentry
              exact hentry'.1
            · intro other _hne
              rfl
            · simpa [LazyRevealProbe.State.clearPending, hvalue]
          · intro position hmissing
            apply (Finset.card_le_card ?_).trans_lt (hcard position (by
              simpa [LazyRevealProbe.State.clearPending] using hmissing))
            intro candidate hcandidate
            rw [LazyRevealProbe.State.mem_pendingAt_iff] at hcandidate ⊢
            have hentry : (Coordinate.position position, candidate) ∈ state.pending ∧
                Coordinate.position position ≠ coordinate := by
              simpa [LazyRevealProbe.State.clearPending,
                LazyRevealProbe.State.pendingAway] using hcandidate
            exact hentry.1
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [finalizeCleanFromTable, hvalue]
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              let output := table index
              have hmiss : ¬state.hitAt index.coordinate output := by
                intro hhit
                apply hstart
                exact ⟨index, by simpa [index, OtsSecretIndex.coordinate,
                  directDeferredContext] using hvalue, hhit⟩
              change ∃ final, some final ∈ support
                (if state.hitAt index.coordinate output then pure none else
                  finalizeCleanFromTable remaining (state.complete index.coordinate output) table)
              simp only [hmiss, ↓reduceIte]
              apply exists_successful_finalizeCleanFromTable table remaining
                (state.complete index.coordinate output)
              · exact hnodup.tail
              · apply nextCovered
                · intro entry hentry
                  have hentry' : entry ∈ state.pending ∧ entry.1 ≠ index.coordinate := by
                    simpa [LazyRevealProbe.State.complete,
                      LazyRevealProbe.State.pendingAway] using hentry
                  exact hentry'.1
                · intro entry hentry
                  have hentry' : entry ∈ state.pending ∧ entry.1 ≠ index.coordinate := by
                    simpa [LazyRevealProbe.State.complete,
                      LazyRevealProbe.State.pendingAway] using hentry
                  simpa [index, OtsSecretIndex.coordinate] using hentry'.2
              · apply nextStart (state.complete index.coordinate output)
                · intro entry hentry
                  have hentry' : entry ∈ state.pending ∧ entry.1 ≠ index.coordinate := by
                    simpa [LazyRevealProbe.State.complete,
                      LazyRevealProbe.State.pendingAway] using hentry
                  exact hentry'.1
                · intro other hne
                  have hne' : other ≠ index.coordinate := by
                    simpa [index, OtsSecretIndex.coordinate] using hne
                  simp [LazyRevealProbe.State.complete, Function.update_of_ne hne']
                · simp [LazyRevealProbe.State.complete, index, OtsSecretIndex.coordinate]
              · intro position hmissing
                have hne : Coordinate.position position ≠ index.coordinate := by
                  simp [index, OtsSecretIndex.coordinate]
                apply (Finset.card_le_card ?_).trans_lt (hcard position (by
                  simpa [LazyRevealProbe.State.complete, Function.update_of_ne hne] using
                    hmissing))
                intro candidate hcandidate
                rw [LazyRevealProbe.State.mem_pendingAt_iff] at hcandidate ⊢
                have hentry : (Coordinate.position position, candidate) ∈ state.pending ∧
                    Coordinate.position position ≠ index.coordinate := by
                  simpa [LazyRevealProbe.State.complete,
                    LazyRevealProbe.State.pendingAway] using hcandidate
                exact hentry.1
          | position position =>
              have hcoordinateCard := hcard position hvalue
              have hne : state.pendingAt (.position position) ≠ Finset.univ :=
                (Finset.card_lt_iff_ne_univ _).mp hcoordinateCard
              obtain ⟨candidate, hcandidate⟩ : ∃ candidate : Digest,
                  candidate ∉ state.pendingAt (.position position) := by
                by_contra hmissing
                push Not at hmissing
                exact hne (Finset.eq_univ_of_forall hmissing)
              let output := hashOutputOfDigest candidate
              have hmiss : ¬state.hitAt (.position position) output := by
                simpa [LazyRevealProbe.State.hitAt, output,
                  truncateHash_hashOutputOfDigest] using hcandidate
              simp only [finalizeCleanFromTable, hvalue]
              obtain ⟨final, hfinal⟩ := exists_successful_finalizeCleanFromTable table remaining
                (state.complete (.position position) output) hnodup.tail (by
                  apply nextCovered
                  · intro entry hentry
                    have hentry' : entry ∈ state.pending ∧
                        entry.1 ≠ Coordinate.position position := by
                      simpa [LazyRevealProbe.State.complete,
                        LazyRevealProbe.State.pendingAway] using hentry
                    exact hentry'.1
                  · intro entry hentry
                    have hentry' : entry ∈ state.pending ∧
                        entry.1 ≠ Coordinate.position position := by
                      simpa [LazyRevealProbe.State.complete,
                        LazyRevealProbe.State.pendingAway] using hentry
                    exact hentry'.2) (by
                  apply nextStart (state.complete (.position position) output)
                  · intro entry hentry
                    have hentry' : entry ∈ state.pending ∧
                        entry.1 ≠ Coordinate.position position := by
                      simpa [LazyRevealProbe.State.complete,
                        LazyRevealProbe.State.pendingAway] using hentry
                    exact hentry'.1
                  · intro other hne
                    simp [LazyRevealProbe.State.complete, Function.update_of_ne hne]
                  · simp [LazyRevealProbe.State.complete]) (by
                  intro other hmissing
                  by_cases heq : other = position
                  · subst other
                    simp [LazyRevealProbe.State.complete] at hmissing
                  · have hcoordinateNe : Coordinate.position other ≠
                        Coordinate.position position := by simpa using heq
                    apply (Finset.card_le_card ?_).trans_lt (hcard other (by
                      simpa [LazyRevealProbe.State.complete,
                        Function.update_of_ne hcoordinateNe] using hmissing))
                    intro otherCandidate hcandidate
                    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hcandidate ⊢
                    have hentry : (Coordinate.position other, otherCandidate) ∈ state.pending ∧
                        Coordinate.position other ≠ Coordinate.position position := by
                      simpa [LazyRevealProbe.State.complete,
                        LazyRevealProbe.State.pendingAway] using hcandidate
                    exact hentry.1)
              refine ⟨final, ?_⟩
              rw [mem_support_bind_iff]
              exact ⟨output, by simp [LazyRevealProbe.sampleHashOutput, output], by
                simpa [hmiss] using hfinal⟩

theorem CompletionSafeStateLE.not_missingChainStartHit_left_of_right
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (hright : ¬MissingChainStartHit table (directDeferredContext right)) :
    ¬MissingChainStartHit table (directDeferredContext left) := by
  rintro ⟨index, hleftValue, hleftHit⟩
  have hleftValue' : left.values index.coordinate = none := by
    simpa only [directDeferredContext] using hleftValue
  have hrightValue : right.values index.coordinate = none := by
    rw [← hstate.values]
    exact hleftValue'
  apply hright
  refine ⟨index, by simpa only [directDeferredContext] using hrightValue, ?_⟩
  by_contra hrightMiss
  exact (hstate.not_hitAt_left_of_right index.coordinate (table index) hleftValue'
    (by
      intro other hcoordinate
      have heq : other = index := OtsSecretIndex.coordinate_injective hcoordinate.symm
      subst other
      rfl)
    hrightMiss) hleftHit

theorem CompletionSafeStateLE.pendingAt_position_card_lt
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (position : Position) (hleftValue : left.values (.position position) = none)
    (hrightCard : right.pending.card < Fintype.card Digest) :
    (left.pendingAt (.position position)).card < Fintype.card Digest := by
  have hsubset : left.pendingAt (.position position) ⊆
      right.pendingAt (.position position) := by
    intro candidate hcandidate
    have hentry : (Coordinate.position position, candidate) ∈ left.pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff left (.position position) candidate).1 hcandidate
    rcases hstate.pending (.position position) candidate hentry with
      hright | ⟨output, hvalue, _hmiss⟩ | ⟨index, hcoordinate, _hmiss⟩
    · exact (LazyRevealProbe.State.mem_pendingAt_iff right (.position position) candidate).2
        hright
    · rw [hleftValue] at hvalue
      simp at hvalue
    · cases hcoordinate
  have hrightPendingAt : (right.pendingAt (.position position)).card ≤
      right.pending.card :=
    (right.pendingAt_card_le (.position position)).trans (Finset.card_filter_le _ _)
  exact lt_of_le_of_lt (Finset.card_le_card hsubset)
    (lt_of_le_of_lt hrightPendingAt hrightCard)

theorem exists_successful_finishObservedCleanRunFromTable_completionSafe
    {table : OtsSecretIndex → HashOutput}
    {left right : ObservedCleanRunResult α}
    (hstate : CompletionSafeStateLE table left.state right.state)
    (htable : left.table = table)
    (hrightStart : ¬MissingChainStartHit table (directDeferredContext right.state))
    (hrightCard : right.state.pending.card < Fintype.card Digest) :
    ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some left)) := by
  have hleftStart := hstate.not_missingChainStartHit_left_of_right hrightStart
  obtain ⟨final, hfinal⟩ := exists_successful_finalizeCleanFromTable table
    left.state.coordinates.toList left.state left.state.coordinates.nodup_toList (by
      intro entry hentry
      simp only [Finset.mem_toList, LazyRevealProbe.State.coordinates,
        Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨entry, hentry, rfl⟩) hleftStart (by
      intro position hvalue
      exact hstate.pendingAt_position_card_lt position hvalue hrightCard)
  rw [← htable] at hfinal
  rcases final with ⟨finalState, finalTable⟩
  refine ⟨⟨finalState, left.remaining, left.value, finalTable, left.observations⟩, ?_⟩
  unfold finishObservedCleanRunFromTable
  rw [mem_support_bind_iff]
  exact ⟨some (finalState, finalTable), hfinal, by simp⟩

theorem completionSafeStateLE_materialized_of_finalizationContextLE
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : (materializedDeferredState left).values = right.state.values) :
    CompletionSafeStateLE table (materializedDeferredState left) right.state := by
  refine ⟨hvalues, ?_, ?_⟩
  · rw [materializedDeferredState_revealed]
    exact hrevealed
  intro coordinate candidate hentry
  have hsourceEntry : (coordinate, candidate) ∈ left.state.pending := by
    simpa [materializedDeferredState_pending] using hentry
  cases hresolved : resolvedCompletionValue table left coordinate with
  | none =>
      left
      have hsourcePending : candidate ∈ left.state.pendingAt coordinate :=
        (LazyRevealProbe.State.mem_pendingAt_iff left.state coordinate candidate).2 hsourceEntry
      have hrightPending := hcontext.view.pendingLE coordinate hresolved hsourcePending
      exact (LazyRevealProbe.State.mem_pendingAt_iff right.state coordinate candidate).1
        hrightPending
  | some output =>
      have hmiss : candidate ≠ truncateHash output := by
        intro heq
        apply hcontext.view.leftClean coordinate output hresolved
        rw [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff]
        simpa [heq] using hsourceEntry
      cases coordinate with
      | position position =>
          right
          left
          refine ⟨output, ?_, hmiss⟩
          simpa [resolvedCompletionValue, DeferredContext.positionValue,
            materializedDeferredState_position] using hresolved
      | chainStart lay tree leafIdx chainIdx =>
          right
          right
          let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
          refine ⟨index, ?_, ?_⟩
          · rfl
          · have houtput : table index = output := by
              simpa [index, resolvedCompletionValue] using hresolved
            intro heq
            apply hmiss
            rw [← houtput]
            exact heq

theorem materializedDeferredState_install_eq_of_value
    (context : DeferredContext) (target : Position) (output : HashOutput)
    (hvalue : context.values target = some output) :
    materializedDeferredState
        { context with values := context.values.install target output } =
      materializedDeferredState context := by
  have hinstall : context.values.install target output = context.values := by
    unfold DeferredStructuralValues.install
    rw [← hvalue]
    exact Function.update_eq_self target context.values
  rw [hinstall]

def ObservedCompletionSafeRel
    (table : OtsSecretIndex → HashOutput)
    (leftPrefix rightPrefix : List CleanProbeObservation) :
    Option (ObservedCleanRunResult α) → Option (ObservedCleanRunResult α) → Prop
  | _, none => True
  | none, some _ => False
  | some left, some right =>
      left.value = right.value ∧ left.table = right.table ∧
        left.remaining = right.remaining ∧
        (∃ suffix,
          left.observations = leftPrefix ++ suffix ∧
            right.observations = rightPrefix ++ suffix) ∧
        CompletionSafeStateLE table left.state right.state

theorem ObservedCompletionSafeRel.pure
    (table : OtsSecretIndex → HashOutput)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (value : α)
    (hstate : CompletionSafeStateLE table leftState rightState) :
    ObservedCompletionSafeRel table leftPrefix rightPrefix
      (some ⟨leftState, fuel, value, table, leftPrefix⟩)
      (some ⟨rightState, fuel, value, table, rightPrefix⟩) := by
  exact ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, hstate⟩

theorem relTriple_any_pure_none_observedCompletionSafe
    (table : OtsSecretIndex → HashOutput)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (run : ProbComp (Option (ObservedCleanRunResult α))) :
    RelTriple run (pure none : ProbComp (Option (ObservedCleanRunResult α)))
      (ObservedCompletionSafeRel table leftPrefix rightPrefix) := by
  have hbase := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
    (relTriple_true run (pure none : ProbComp (Option (ObservedCleanRunResult α))))
  apply relTriple_post_mono hbase
  intro _ right hrelation
  have hright : right = none := by simpa using hrelation.2
  subst right
  trivial

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runObservedCleanFromTable_completionSafe
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : CompletionSafeStateLE table leftState rightState) :
    RelTriple
      (runObservedCleanFromTable leftPrefix leftState fuel table computation)
      (runObservedCleanFromTable rightPrefix rightState fuel table computation)
      (ObservedCompletionSafeRel table leftPrefix rightPrefix) := by
  induction computation using OracleComp.inductionOn generalizing
      leftPrefix rightPrefix leftState rightState fuel with
  | pure value =>
      rw [runObservedCleanFromTable, OracleComp.construct_pure,
        runObservedCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCompletionSafeRel.pure table leftPrefix rightPrefix leftState rightState fuel
          value hstate)
  | query_bind query next ih =>
      rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
        runObservedCleanFromTable, OracleComp.construct_query_bind]
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftPrefix rightPrefix leftState rightState fuel hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftPrefix rightPrefix leftState rightState fuel hstate
      | ensure coordinate =>
          exact ih () leftPrefix rightPrefix (leftState.ensure coordinate)
            (rightState.ensure coordinate) fuel
            (hstate.ensure coordinate)
      | probe coordinate candidate =>
          cases fuel with
          | zero => exact relTriple_pure_pure (by trivial)
          | succ remaining =>
              let leftObservation := cleanProbeObservation leftState coordinate candidate
              let rightObservation := cleanProbeObservation rightState coordinate candidate
              have hobservation : leftObservation = rightObservation := by
                unfold leftObservation rightObservation cleanProbeObservation
                simp [hstate.values, hstate.revealed]
              have hrevealed : coordinate ∈ leftState.revealed ↔
                  coordinate ∈ rightState.revealed := by
                rw [hstate.revealed]
              by_cases hleftRevealed : coordinate ∈ leftState.revealed
              · have hrightRevealed : coordinate ∈ rightState.revealed :=
                  hrevealed.mp hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                have hnext := ih ()
                  (leftPrefix ++ [leftObservation]) (rightPrefix ++ [rightObservation])
                  leftState rightState remaining hstate
                apply relTriple_post_mono hnext
                intro leftResult rightResult hresult
                cases rightResult with
                | none => trivial
                | some rightResult =>
                    cases leftResult with
                    | none => simp [ObservedCompletionSafeRel] at hresult
                    | some leftResult =>
                        rcases hresult with ⟨hvalue, htable, hremaining,
                          ⟨suffix, hleft, hright⟩, hnextState⟩
                        refine ⟨hvalue, htable, hremaining, ⟨leftObservation :: suffix, ?_, ?_⟩,
                          hnextState⟩
                        · simpa [List.append_assoc] using hleft
                        · simpa [List.append_assoc, hobservation] using hright
              · have hrightRevealed : coordinate ∉ rightState.revealed := by
                  simpa [hrevealed] using hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                have hnext := ih ()
                  (leftPrefix ++ [leftObservation]) (rightPrefix ++ [rightObservation])
                  (leftState.addPending coordinate candidate)
                  (rightState.addPending coordinate candidate) remaining
                  (hstate.addPending coordinate candidate)
                apply relTriple_post_mono hnext
                intro leftResult rightResult hresult
                cases rightResult with
                | none => trivial
                | some rightResult =>
                    cases leftResult with
                    | none => simp [ObservedCompletionSafeRel] at hresult
                    | some leftResult =>
                        rcases hresult with ⟨hvalue, htable, hremaining,
                          ⟨suffix, hleft, hright⟩, hnextState⟩
                        refine ⟨hvalue, htable, hremaining, ⟨leftObservation :: suffix, ?_, ?_⟩,
                          hnextState⟩
                        · simpa [List.append_assoc] using hleft
                        · simpa [List.append_assoc, hobservation] using hright
      | peek coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          rw [hvalue]
          exact ih (rightState.values coordinate) leftPrefix rightPrefix leftState rightState fuel
            hstate
      | publish coordinate =>
          simp only
          exact ih () leftPrefix rightPrefix (leftState.publish coordinate)
            (rightState.publish coordinate) fuel
            (hstate.publish coordinate)
      | reveal coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          cases hrightValue : rightState.values coordinate with
          | some output =>
              have hleftValue : leftState.values coordinate = some output := by
                rw [hvalue, hrightValue]
              simp only [hleftValue, hrightValue]
              exact ih output leftPrefix rightPrefix leftState rightState fuel hstate
          | none =>
              have hleftValue : leftState.values coordinate = none := by
                rw [hvalue, hrightValue]
              simp only [hleftValue, hrightValue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hrightHit : rightState.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [output, hrightHit, ↓reduceIte]
                    exact relTriple_any_pure_none_observedCompletionSafe table leftPrefix
                      rightPrefix _
                  · have hleftHit : ¬leftState.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output :=
                      hstate.not_hitAt_left_of_right _ output hleftValue
                        (by
                          intro index hcoordinate
                          rcases index with ⟨otherLay, otherTree, otherLeaf, otherChain⟩
                          simp [OtsSecretIndex.coordinate] at hcoordinate
                          obtain ⟨rfl, rfl, rfl, rfl⟩ := hcoordinate
                          rfl)
                        hrightHit
                    simp only [output, hleftHit, hrightHit, ↓reduceIte]
                    exact ih output leftPrefix rightPrefix
                      (leftState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      (rightState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel (hstate.materialize _ output)
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  by_cases hrightHit : rightState.hitAt (.position position) leftOutput
                  · simp only [hrightHit, ↓reduceIte]
                    exact relTriple_any_pure_none_observedCompletionSafe table leftPrefix
                      rightPrefix _
                  · have hleftHit : ¬leftState.hitAt (.position position) leftOutput :=
                      hstate.not_hitAt_left_of_right _ leftOutput hleftValue
                        (by intro index hcoordinate; cases hcoordinate) hrightHit
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact ih leftOutput leftPrefix rightPrefix
                      (leftState.materialize (.position position) leftOutput)
                      (rightState.materialize (.position position) leftOutput) fuel
                      (hstate.materialize _ leftOutput)

theorem materializedCanonicalContext_values_eq_of_completionSafe
    (table : OtsSecretIndex → HashOutput)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right) :
    (materializedCanonicalContext table left).state.values =
      (materializedCanonicalContext table right).state.values := by
  change publicMaterializedValues table (directDeferredContext left) =
    publicMaterializedValues table (directDeferredContext right)
  funext coordinate
  unfold publicMaterializedValues
  have hrevealed : coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed := by
    rw [hstate.revealed]
  by_cases hleftRevealed : coordinate ∈ left.revealed
  · have hrightRevealed : coordinate ∈ right.revealed := hrevealed.mp hleftRevealed
    simp only [directDeferredContext, hleftRevealed, hrightRevealed, ↓reduceIte]
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx => simp [resolvedCompletionValue]
    | position position =>
        simp [resolvedCompletionValue, DeferredContext.positionValue, directDeferredValues,
          hstate.values]
  · have hrightRevealed : coordinate ∉ right.revealed := by
      simpa [hrevealed] using hleftRevealed
    simp [directDeferredContext, hleftRevealed, hrightRevealed]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_completionSafe
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hstate : CompletionSafeStateLE table leftState rightState) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation leftPrefix leftState
        fuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation rightPrefix rightState
        fuel table cache)
      (ObservedCompletionSafeRel table leftPrefix rightPrefix) := by
  induction computation using OracleComp.inductionOn generalizing
      leftPrefix rightPrefix leftState rightState fuel cache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCompletionSafeRel.pure table leftPrefix rightPrefix leftState rightState fuel
          (value, cache) hstate)
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun
            (ObservedCompletionSafeRel table leftPrefix rightPrefix)) :
          RelTriple
            (leftRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (rightRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (ObservedCompletionSafeRel table leftPrefix rightPrefix) := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases rightResult with
        | none =>
            exact relTriple_any_pure_none_observedCompletionSafe table leftPrefix rightPrefix _
        | some rightResult =>
            cases leftResult with
            | none => simp [ObservedCompletionSafeRel] at hresult
            | some leftResult =>
                rcases hresult with ⟨hvalue, htable, hremaining,
                  ⟨suffix, hleftObservations, hrightObservations⟩, hnextState⟩
                simp only
                have houtput : leftResult.value.1 = rightResult.value.1 :=
                  congrArg Prod.fst hvalue
                have hnextCache : leftResult.value.2 = rightResult.value.2 :=
                  congrArg Prod.snd hvalue
                rw [← houtput, ← hnextCache, ← hremaining]
                have hnext := ih leftResult.value.1 leftResult.observations
                  rightResult.observations leftResult.state rightResult.state
                  leftResult.remaining leftResult.value.2 hnextState
                apply relTriple_post_mono hnext
                intro laterLeft laterRight hlater
                cases laterRight with
                | none => trivial
                | some laterRight =>
                    cases laterLeft with
                    | none => simp [ObservedCompletionSafeRel] at hlater
                    | some laterLeft =>
                        rcases hlater with ⟨hlaterValue, hlaterTable, hlaterRemaining,
                          ⟨laterSuffix, hlaterLeft, hlaterRight⟩, hlaterState⟩
                        refine ⟨hlaterValue, hlaterTable, hlaterRemaining,
                          ⟨suffix ++ laterSuffix, ?_, ?_⟩, hlaterState⟩
                        · rw [hlaterLeft, hleftObservations, List.append_assoc]
                        · rw [hlaterRight, hrightObservations, List.append_assoc]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have hstep := relTriple_runObservedCleanFromTable_completionSafe
                ((splitUniformImpl n).run cache) leftPrefix rightPrefix leftState rightState fuel
                table hstate
              convert continueAfter _ _ hstep using 1 <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let leftPublic := materializedCanonicalContext table leftState
              let rightPublic := materializedCanonicalContext table rightState
              have hpublicValues : leftPublic.state.values = rightPublic.state.values :=
                materializedCanonicalContext_values_eq_of_completionSafe table hstate
              have hplan : purePlanProbingHashQuery parameter input leftPublic.state =
                  purePlanProbingHashQuery parameter input rightPublic.state :=
                purePlanProbingHashQuery_eq_of_values_eq hpublicValues parameter input
              let plan := purePlanProbingHashQuery parameter input leftPublic.state
              have hexecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input rightPublic.state
                      plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hpublicValues plan
              rw [← hplan, ← hexecutor]
              have hstep := relTriple_runObservedCleanFromTable_completionSafe
                ((probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state
                  plan).run cache)
                leftPrefix rightPrefix leftState rightState fuel table hstate
              convert continueAfter _ _ hstep using 1 <;>
                simp only [leftPublic, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          have hstep := relTriple_runObservedCleanFromTable_completionSafe
            ((maskedSign parameter root ftsSecret message).run cache)
            leftPrefix rightPrefix leftState rightState fuel table hstate
          convert continueAfter _ _ hstep using 1 <;>
            simp only [observedMaterializedBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_observedMaterializedBoundary_completionSafe_of_left_doomed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (cache : SplitHashCache)
    (hstate : CompletionSafeStateLE table leftState rightState)
    (hleftStarts : StartTableAgrees leftState table)
    (hbudget : fuel + rightState.pending.card < Fintype.card Digest)
    (hleftDoomed : ∀ result : ObservedCleanRunResult (α × SplitHashCache),
      some result ∈ support
          (observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
            leftState fuel table cache) →
        ¬DeferredCompletable table (directDeferredContext result.state)) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          rightState fuel table cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          leftState fuel table cache)
      SuccessfulObservedIndicatorRel := by
  let leftRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations leftState fuel table cache
  let rightRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations rightState fuel table cache
  have hbase := relTriple_observedMaterializedBoundary_completionSafe parameter publicRoot
    ftsSecret computation observations observations leftState rightState fuel table cache hstate
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result ↦ result ∈ support leftRun) (by
        intro result hresult
        simpa [leftRun] using hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  have hreverse := relTriple_symm hbothSupported
  apply relTriple_map
  apply relTriple_post_mono hreverse
  intro rightResult leftResult hrelation hrightGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (rightResult, rightRoot) = true at hrightGood
  rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hrightGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (leftResult, rightRoot) = true
  rw [successfulObservedRootComparisonIndicator_eq_true_iff]
  rcases hrelation with ⟨⟨hcompletion, hleftSupport⟩, hrightSupport⟩
  cases rightResult with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hrightGood
  | some rightResult =>
      cases leftResult with
      | none => simp [ObservedCompletionSafeRel] at hcompletion
      | some leftResult =>
          rcases hcompletion with ⟨_hvalue, htable, _hremaining,
            ⟨suffix, hleftObservations, hrightObservations⟩, hfinalState⟩
          have hobservations : leftResult.observations = rightResult.observations := by
            rw [hleftObservations, hrightObservations]
          rcases hrightGood with
            ⟨⟨⟨⟨rightFinal, hrightFinish⟩, _hrightDoomed, hrightFirstRoot⟩,
              hrightPosition⟩, hrightComparison⟩
          have hleftTable : leftResult.table = table :=
            (startTableAgrees_of_mem_observedMaterializedBoundary parameter publicRoot ftsSecret
              computation observations leftState fuel table cache hleftStarts leftResult
              (by simpa [leftRun] using hleftSupport)).1
          have hrightTable : rightResult.table = table := htable.symm.trans hleftTable
          have hrightStart : ¬MissingChainStartHit table
              (directDeferredContext rightResult.state) :=
            by
              rw [← hrightTable]
              exact not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable rightResult
                rightFinal hrightFinish
          have hrightCard : rightResult.state.pending.card < Fintype.card Digest := by
            have hremaining := remaining_add_pending_card_le_of_mem_observedMaterializedBoundary
              parameter publicRoot ftsSecret computation observations rightState fuel table cache
              rightResult (by simpa [rightRun] using hrightSupport)
            omega
          obtain ⟨leftFinal, hleftFinish⟩ :=
            exists_successful_finishObservedCleanRunFromTable_completionSafe hfinalState
              hleftTable hrightStart hrightCard
          have hleftPosition :
              observedFirstLayerRootPosition? ordinal (some leftResult) = some target := by
            rw [observedFirstLayerRootPosition?_eq_of_observations_eq ordinal leftResult
              rightResult hobservations]
            exact hrightPosition
          have hleftFirstRoot :
              ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some leftResult) := by
            obtain ⟨_selected, _hselected, hrightFirst, _hroot⟩ := hrightFirstRoot
            have hleftFirst := firstExistingHiddenHitAt_of_observations_eq rightResult leftResult
              ordinal hobservations.symm hrightFirst
            exact firstExistingHiddenRootHitAt_of_first_of_position leftResult ordinal target
              hleftFirst hleftPosition
          have hleftComparison : CandidatesAvoidRoot target rightRoot
              (observedPrefixProbes ordinal (some leftResult)) := by
            rw [observedPrefixProbes_eq_of_observations_eq ordinal leftResult rightResult
              hobservations]
            exact hrightComparison
          exact ⟨⟨⟨⟨leftFinal, hleftFinish⟩,
            hleftDoomed leftResult (by simpa [leftRun] using hleftSupport), hleftFirstRoot⟩,
            hleftPosition⟩, hleftComparison⟩

set_option maxRecDepth 100000 in
theorem selectedHash_goodForRoots
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (candidate : Probe)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input left.state) = some candidate)
    (hordinal : snapshots.length = ordinal)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hleftCovered : PendingCoveredBy
      (snapshots.map PlannedProbeSnapshot.toProbe) left)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations right.state fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) :
    ∃ output,
      let selection : PrivateOrdinalSelection :=
        ⟨candidate, left,
          (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
            PlannedProbeSnapshot.toProbe⟩
      selection.GoodForRoots target output rightRoot ordinal ∧
        PendingCoveredBy (selection.candidates.take ordinal) selection.context := by
  have hobservationLength : observations.length = ordinal :=
    haligned.length_eq.symm.trans hordinal
  have hrightValues :
      (materializedCanonicalContext table right.state).state.values = left.state.values := by
    unfold materializedCanonicalContext
    rw [← hrightMaterialized]
    exact canonicalized_right_values_eq_of_finalizationContextLE hcontext hrevealed hcanonical
  have hplanEq :
      purePlanProbingHashQuery parameter input
          (materializedCanonicalContext table right.state).state =
        purePlanProbingHashQuery parameter input left.state :=
    purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
  have hqueryCandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table right.state).state) = some candidate := by
    rw [hplanEq]
    exact hcandidate
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
    selected, hselected, hfirst, _hroot⟩, hposition⟩, hcomparison⟩ := hgood
  have hobservation :=
    selected_observation_eq_of_mem_observedMaterializedBoundary_hash_query ordinal parameter
      publicRoot ftsSecret input next observations right.state fuel table cache candidate
      hobservationLength hqueryCandidate result hresult selected hselected
  obtain ⟨first, hfirstOrdinal, hfirstHit, _hbeforeFirst⟩ := hfirst
  have hfirstSelected : first = selected :=
    Fin.ext (hfirstOrdinal.trans hselected.symm)
  subst first
  rw [ExistingHiddenHitAtOrdinal, hobservation] at hfirstHit
  obtain ⟨hselectedHidden, output, hselectedValue, hselectedCandidate⟩ := hfirstHit
  have hrightValue : right.state.values candidate.coordinate = some output := by
    simpa [cleanProbeObservation] using hselectedValue
  have hcandidateDigest : truncateHash output = candidate.candidate := by
    simpa [cleanProbeObservation] using hselectedCandidate
  have hselectedLt : ordinal < result.observations.length := by
    rw [← hselected]
    exact selected.isLt
  have hselectedIndex :
      (⟨ordinal, hselectedLt⟩ : Fin result.observations.length) = selected :=
    Fin.ext hselected.symm
  have htargetData :
      (result.observations.get selected).coordinate = .position target ∧ IsLayerRoot target := by
    simp only [observedFirstLayerRootPosition?, hselectedLt, ↓reduceDIte] at hposition
    rw [candidateLayerRootPosition?_eq_some_iff, hselectedIndex] at hposition
    exact hposition
  have hcandidateCoordinate : candidate.coordinate = .position target := by
    rw [hobservation] at htargetData
    simpa [cleanProbeObservation] using htargetData.1
  have hcandidateEq : candidate = ⟨.position target, truncateHash output⟩ := by
    cases candidate
    simp only [Probe.mk.injEq]
    exact ⟨hcandidateCoordinate, hcandidateDigest.symm⟩
  have hrightHidden : candidate.coordinate ∉ right.state.revealed := by
    simpa [cleanProbeObservation, decide_eq_false_iff_not] using hselectedHidden
  have hleftHidden : Coordinate.position target ∉ left.state.revealed := by
    rw [← hcandidateCoordinate, hrevealed]
    exact hrightHidden
  have hleftState : left.state.values (.position target) = none :=
    canonical_value_none_of_not_revealed hcanonical hleftHidden
  have hrightPositionValue : right.state.values (.position target) = some output := by
    rw [← hcandidateCoordinate]
    exact hrightValue
  have hleftPrivate : left.values target = some output :=
    hcontext.view.privateValue_of_left_hidden_of_right_materialized target output hleftState
      hrightPositionValue
  have hleftCandidateHidden : candidate.coordinate ∉ left.state.revealed := by
    simpa [hcandidateCoordinate] using hleftHidden
  have hactualAvoid := candidatesAvoidRoot_of_aligned_tracked table snapshots observations
    candidate left right hbefore hcontext hrightMaterialized hnoHit haligned htracked target output
    hcandidateEq hleftState hleftPrivate hleftCandidateHidden
  have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
    ftsSecret
    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
      (Sum.inl (Sum.inr input))) >>= next)
    observations right.state fuel table cache result hresult
  have htake : result.observations.take ordinal = observations := by
    obtain ⟨tail, htail⟩ := hprefix
    rw [← htail, List.take_append_of_le_length]
    · simpa [hobservationLength]
    · omega
  have hcomparison' : CandidatesAvoidRoot target rightRoot
      (snapshots.map PlannedProbeSnapshot.toProbe) := by
    simpa [observedPrefixProbes, htake, haligned.map_toProbe_eq] using hcomparison
  let selection : PrivateOrdinalSelection :=
    ⟨candidate, left,
      (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
        PlannedProbeSnapshot.toProbe⟩
  refine ⟨output, ?_, ?_⟩
  · refine ⟨hcandidateEq, hleftState, hleftHidden, hleftPrivate, ?_⟩
    intro earlier hearlier
    have hearlier' : earlier ∈ snapshots.map PlannedProbeSnapshot.toProbe := by
      simpa [selection, hordinal] using hearlier
    exact ⟨hactualAvoid earlier hearlier', hcomparison' earlier hearlier'⟩
  · simpa [selection, hordinal] using hleftCovered

theorem relTriple_indicator_observedMaterializedBoundary_pure_false
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (value : α) (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret
          (pure value : OracleComp (OracleWorld + SigningSpec) α) observations state fuel table
          cache)
      (pure false : ProbComp Bool)
      SuccessfulObservedIndicatorRel := by
  rw [observedMaterializedBoundary, OracleComp.construct_pure]
  simp only [map_pure]
  apply relTriple_pure_pure
  intro hgood
  change successfulObservedRootComparisonIndicator table ordinal target
    (some ⟨state, fuel, (value, cache), table, observations⟩, rightRoot) = true at hgood
  rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hgood
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
    selected, _hselected, hfirst, _hroot⟩, _hposition⟩, _hcomparison⟩ := hgood
  obtain ⟨first, _hfirstOrdinal, hfirstHit, _hbefore⟩ := hfirst
  exact (hnoHit (observations.get first) (List.get_mem observations first) hfirstHit).elim

set_option maxRecDepth 100000 in
theorem relTriple_indicator_observedMaterializedBoundary_false_of_ordinal_lt
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (other : ProbComp Bool)
    (hordinal : ordinal < observations.length)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          state fuel table cache)
      other SuccessfulObservedIndicatorRel := by
  let real :=
    (successfulObservedRootComparisonIndicator table ordinal target ∘
        fun observed ↦ (observed, rightRoot)) <$>
      observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
        state fuel table cache
  have hbase := relTriple_true real other
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result ↦ result ∈ support real) (fun _ hresult ↦ hresult)
  apply relTriple_post_mono hsupported
  intro realResult _otherResult hsupport htrue
  have hrealSupport : true ∈ support real := by simpa [htrue] using hsupport.2
  unfold real at hrealSupport
  rw [support_map] at hrealSupport
  obtain ⟨observed, hobserved, hindicator⟩ := hrealSupport
  have hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot observed := by
    change successfulObservedRootComparisonIndicator table ordinal target
      (observed, rightRoot) = true at hindicator
    rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hindicator
    exact hindicator
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
        _selected, _hselected, hfirst, _hroot⟩, _hposition⟩, _hcomparison⟩ := hgood
      obtain ⟨first, hfirstOrdinal, hfirstHit, _hbefore⟩ := hfirst
      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter
        publicRoot ftsSecret computation observations state fuel table cache result hobserved
      let initial : Fin observations.length := ⟨ordinal, hordinal⟩
      have hresultOrdinal : ordinal < result.observations.length :=
        hordinal.trans_le hprefix.length_le
      let resultIndex : Fin result.observations.length := ⟨ordinal, hresultOrdinal⟩
      have hfirstEq : first = resultIndex := Fin.ext hfirstOrdinal
      subst first
      have hget : observations[initial.val] = result.observations[resultIndex.val] :=
        hprefix.getElem hordinal
      have hinitialHit : (observations.get initial).ExistingHiddenHit := by
        simpa [ExistingHiddenHitAtOrdinal, initial, resultIndex, ← hget] using hfirstHit
      exact (hnoHit (observations.get initial) (List.get_mem observations initial)
        hinitialHit).elim

set_option maxRecDepth 100000 in
theorem relTriple_observed_finishDirectDelayed_of_firstStopped
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedFirstStoppedStepRel table observations leftResult rightResult)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
            observations right.context.state right.remaining table right.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe left.context left.remaining
          (left.value.1, left.value.2) snapshots delayedObservations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (match rightResult with
      | none => pure false
      | some result =>
          (successfulObservedRootComparisonIndicator table ordinal target ∘
              fun observed ↦ (observed, rightRoot)) <$>
            observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
              result.observations result.state result.remaining table result.value.2)
      (finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots delayedObservations leftResult)
      SuccessfulObservedIndicatorRel := by
  rcases hrelation with hfailed | haligned | hmissing
  · subst rightResult
    have hbase := relTriple_true (pure false : ProbComp Bool)
      (finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots delayedObservations leftResult)
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun result ↦ result = false) (by intro result hresult; simpa using hresult)
    apply relTriple_post_mono hsupported
    intro real delayed hrelation hreal
    exact (Bool.false_ne_true (hrelation.2.symm.trans hreal)).elim
  · obtain ⟨left, right, hleft, hright, hclean⟩ := haligned
    subst leftResult
    subst rightResult
    simp only [finishDirectDelayedSelectedRootIndicator, observedResolvedResult]
    exact hrecursive left right rfl rfl hclean
  · obtain ⟨right, hright, hdoomed, hmissing⟩ := hmissing
    subst rightResult
    let realRun :=
      (successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
          observations right.context.state right.remaining table right.value.2
    let delayedRun := finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table observe)
      snapshots delayedObservations leftResult
    have hbase := relTriple_true realRun delayedRun
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun result ↦ result ∈ support realRun) (fun _ hresult ↦ hresult)
    apply relTriple_post_mono hsupported
    intro real delayed hsupport hreal
    exfalso
    have hrealSupport : true ∈ support realRun := by simpa [hreal] using hsupport.2
    unfold realRun at hrealSupport
    rw [support_map] at hrealSupport
    obtain ⟨observed, hobserved, hindicator⟩ := hrealSupport
    have hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot observed := by
      change successfulObservedRootComparisonIndicator table ordinal target
        (observed, rightRoot) = true at hindicator
      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hindicator
      exact hindicator
    cases observed with
    | none =>
        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
    | some result =>
        obtain ⟨finalResult, hfinish⟩ := hgood.1.1.1
        exact not_missingChainStartHit_of_successful_observedMaterializedBoundary parameter
          publicRoot ftsSecret (next right.value.1) observations right.context.state
          right.remaining table right.value.2 result finalResult hobserved hfinish
          (by rw [hdoomed.2] at hmissing; exact hmissing)

set_option maxRecDepth 100000 in
theorem relTriple_bind_observed_finishDirectDelayed_of_firstStopped
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (leftStep : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightStep : ProbComp (Option (ObservedCleanRunResult (α × SplitHashCache))))
    (hstep : RelTriple leftStep rightStep
      (WitnessObservedFirstStoppedStepRel table observations))
    (hrecursive : ∀ left right,
      DirectWitnessResult.done left ∈ support leftStep →
      some (observedResolvedResult observations right) ∈ support rightStep →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
            observations right.context.state right.remaining table right.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe left.context left.remaining
          (left.value.1, left.value.2) snapshots delayedObservations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (rightStep >>= fun result =>
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
                result.observations result.state result.remaining table result.value.2)
      (leftStep >>= finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots delayedObservations)
      SuccessfulObservedIndicatorRel := by
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result ↦ result ∈ support leftStep) (fun _ hresult ↦ hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_bind (relTriple_symm hbothSupported)
  intro rightResult leftResult hrelation
  rcases hrelation with ⟨⟨hrelation, hrightSupport⟩, hleftSupport⟩
  exact relTriple_observed_finishDirectDelayed_of_firstStopped ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations delayedObservations
    leftResult rightResult hrelation (by
      intro left right hleft hright hclean
      subst leftResult
      subst rightResult
      exact hrecursive left right hrightSupport hleftSupport hclean)

set_option maxRecDepth 100000 in
theorem relTriple_bind_observed_finishDirectDelayed_of_probeFree
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftComputation rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (hbase : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectWitnessMaterializedStableRunEq table))
    (hleftProbeFree : leftComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hrightProbeFree : rightComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hleftValid : left.Valid) (hleftCompletable : DeferredCompletable table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table leftComputation) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table rightComputation) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots
            delayedObservations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table rightComputation >>=
        fun result =>
          match result with
          | none => pure false
          | some result =>
              (successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$>
                observedMaterializedBoundary parameter publicRoot ftsSecret
                  (next result.value.1) result.observations result.state result.remaining table
                  result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots delayedObservations)
      SuccessfulObservedIndicatorRel := by
  have hstep := relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
    leftComputation rightComputation observations left right leftFuel rightFuel hbase
    hleftProbeFree hrightProbeFree hleftValid hleftCompletable hrightMaterialized htracked hcovered
    hnoHit hbudget
  exact relTriple_bind_observed_finishDirectDelayed_of_firstStopped ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations
    delayedObservations
    (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
    (runObservedCleanFromTable observations right.state rightFuel table rightComputation)
    hstep hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_uniform_finishDirectDelayed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (n : unifSpec.Domain)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (Fin (n + 1) × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache)) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table
          ((splitUniformImpl n).run rightCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots
            delayedObservations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table
          ((splitUniformImpl n).run rightCache) >>= fun result ↦
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret
                (next result.value.1) result.observations result.state result.remaining table
                result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots delayedObservations)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_bind_observed_finishDirectDelayed_of_probeFree ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations delayedObservations
    left right leftFuel
    rightFuel ((splitUniformImpl n).run leftCache) ((splitUniformImpl n).run rightCache)
  · exact (witnessMaterializedStableCouples_splitUniformImpl table n) left right leftFuel
      rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
      hrightMaterialized
  · exact splitUniformImpl_probeFree n leftCache
  · exact splitUniformImpl_probeFree n rightCache
  · exact hcontext.leftValid
  · exact hcontext.leftCompletable
  · exact hrightMaterialized
  · exact htracked
  · exact hcovered
  · exact hnoHit
  · exact hbudget
  · exact hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_sign_finishDirectDelayed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (message : Message)
    (next : Option Signature →
      OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run leftCache)) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run rightCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots
            delayedObservations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run rightCache) >>= fun result ↦
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret
                (next result.value.1) result.observations result.state result.remaining table
                result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run leftCache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots delayedObservations)
      SuccessfulObservedIndicatorRel := by
  have hresult := relTriple_bind_observed_finishDirectDelayed_of_probeFree ordinal parameter
    publicRoot rightRoot ftsSecret table target next observe snapshots observations
    delayedObservations left right leftFuel rightFuel
    ((maskedSign parameter publicRoot ftsSecret message).run leftCache)
    ((maskedSign parameter publicRoot ftsSecret message).run rightCache)
    ((witnessMaterializedStableCouples_maskedSign table parameter publicRoot ftsSecret message)
      left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
      hpublished hrightMaterialized)
    (maskedSign_probeFree parameter publicRoot ftsSecret message leftCache)
    (maskedSign_probeFree parameter publicRoot ftsSecret message rightCache)
    hcontext.leftValid hcontext.leftCompletable hrightMaterialized htracked hcovered hnoHit hbudget
    hrecursive
  convert hresult using 1 <;>
    try (apply bind_congr; intro result; cases result <;> rfl)

set_option maxRecDepth 100000 in
theorem relTriple_indicator_observedMaterializedHashContinuation_hidden_notCompletable
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (input : HashInput)
    (plan : PlannedHashQuery) (candidate : Probe)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (rightFuel : Nat) (rightCache : SplitHashCache)
    (delayed : ProbComp Bool)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hnotSelected : ¬ordinal < (snapshots ++
      [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).length)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hcanonical : CanonicalMaterializedValues table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hrightPositive : 0 < rightFuel)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hnotCompletable : ¬DeferredCompletable table
      ({ right with state :=
        right.state.addPending candidate.coordinate candidate.candidate } : DeferredContext)) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedHashContinuation parameter publicRoot ftsSecret input plan next
          observations right.state rightFuel table rightCache)
      delayed SuccessfulObservedIndicatorRel := by
  let nextSnapshots := snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]
  let source : ProbComp PrivateWitnessSnapshotOutput := pure (none, nextSnapshots)
  have hpostCard :
      (right.state.addPending candidate.coordinate candidate.candidate).pending.card <
        Fintype.card Digest := by
    have hcard := LazyRevealProbe.State.pending_card_addPending_le right.state
      candidate.coordinate candidate.candidate
    omega
  have hsource : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends nextSnapshots output := by
    intro output houtput
    simp [source] at houtput
    subst output
    simp [PrivateWitnessSnapshotExtends]
  have hstopped :=
    relTriple_source_observedMaterializedHashContinuation_firstStopped_of_notCompletable
      parameter publicRoot ftsSecret input plan candidate next source snapshots observations left
      right (rightFuel - 1) table rightCache hcandidate hcontext hrevealed hcanonical
      hrightMaterialized hhidden hnoHit haligned hbefore htracked (by
        intro output houtput
        exact hsource output houtput) hpostCard hnotCompletable
  have hstoppedSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstopped
      (fun output ↦ output ∈ support source) (fun _ houtput ↦ houtput)
  have hsemantic : RelTriple
      (observedMaterializedHashContinuation parameter publicRoot ftsSecret input plan next
        observations right.state (rightFuel - 1 + 1) table rightCache)
      source
      (fun observed sourceOutput ↦
        EqRel Bool
          (successfulObservedRootComparisonIndicator table ordinal target
            (observed, rightRoot)) false) := by
    apply relTriple_post_mono (relTriple_symm hstoppedSupported)
    intro observed sourceOutput hrelation
    rw [EqRel, Bool.eq_false_iff]
    intro htrue
    have hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot observed := by
      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at htrue
      exact htrue
    cases observed with
    | none =>
        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
    | some result =>
        have hsourceOutput : sourceOutput = (none, nextSnapshots) := by
          simpa [source] using hrelation.2
        subst sourceOutput
        obtain ⟨⟨⟨⟨finalResult, hfinish⟩, _hdoomed,
          selected, hselected, hfirst, hroot⟩, _hposition⟩, _hcomparison⟩ := hgood
        have hrootAll : ∀ other : Fin result.observations.length,
            other.val = ordinal → (result.observations.get other).toProbe.IsLayerRoot := by
          intro other hother
          have heq : other = selected := Fin.ext (hother.trans hselected.symm)
          subst other
          exact hroot
        have hselectedSource := hrelation.1.selected_of_successful_firstRoot finalResult hfinish
          ordinal hfirst hrootAll
        obtain ⟨sourceSelected, hselectedOrdinal, _hwitness⟩ := hselectedSource
        apply hnotSelected
        simpa [nextSnapshots, hselectedOrdinal] using sourceSelected.isLt
  have hmapped := relTriple_map
    (f := successfulObservedRootComparisonIndicator table ordinal target ∘
      fun observed ↦ (observed, rightRoot))
    (g := fun _ : PrivateWitnessSnapshotOutput ↦ false)
    hsemantic
  have hmappedFalse : RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedHashContinuation parameter publicRoot ftsSecret input plan next
          observations right.state (rightFuel - 1 + 1) table rightCache)
      (pure false : ProbComp Bool) (EqRel Bool) := by
    simpa [source] using hmapped
  have hfalse : RelTriple (pure false : ProbComp Bool) delayed
      SuccessfulObservedIndicatorRel := by
    have hbase := relTriple_true (pure false : ProbComp Bool) delayed
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun result ↦ result = false) (by intro result hresult; simpa using hresult)
    apply relTriple_post_mono hsupported
    intro actual _delayed hrelation hactual
    exact (Bool.false_ne_true (hrelation.2.symm.trans hactual)).elim
  have hglued := SphincsSecurity.relTriple_trans_exists hmappedFalse hfalse
  have hresult : RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedHashContinuation parameter publicRoot ftsSecret input plan next
          observations right.state (rightFuel - 1 + 1) table rightCache)
      delayed SuccessfulObservedIndicatorRel := by
    apply relTriple_post_mono hglued
    intro actual delayedResult hrelation
    obtain ⟨middle, hactual, hmiddle⟩ := hrelation
    exact hactual ▸ hmiddle
  have hrightFuel : rightFuel - 1 + 1 = rightFuel := by omega
  simpa [hrightFuel] using hresult

theorem relTriple_indicator_observed_directDelayed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (hroot : IsLayerRoot target)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations delayedObservations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hchainValid : ChainState.ValidFor (fun _ => True) right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hdelayedProbes : delayedObservations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hdelayedNoHit : ∀ observation ∈ delayedObservations,
      ¬observation.ExistingHiddenHit)
    (hleftCovered : PendingCoveredBy
      (snapshots.map PlannedProbeSnapshot.toProbe) left)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          right.state rightFuel table rightCache)
      (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
        rightRoot computation snapshots delayedObservations left leftFuel leftCache)
      SuccessfulObservedIndicatorRel := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations delayedObservations left right leftFuel rightFuel leftCache
      rightCache bound with
  | pure value =>
      by_cases hselected : ordinal < snapshots.length
      · have hordinal : ordinal < observations.length := by
          rw [← haligned.length_eq]
          exact hselected
        exact relTriple_indicator_observedMaterializedBoundary_false_of_ordinal_lt ordinal
          parameter publicRoot rightRoot ftsSecret table target (pure value) observations
          right.state rightFuel rightCache
          (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
            rightRoot (pure value) snapshots delayedObservations left leftFuel leftCache)
          hordinal hnoHit
      · rw [directDelayedSelectedRootIndicator, OracleComp.construct_pure]
        simp only [hselected, ↓reduceDIte]
        exact relTriple_indicator_observedMaterializedBoundary_pure_false ordinal parameter
          publicRoot rightRoot ftsSecret table target value observations right.state rightFuel
          rightCache hnoHit
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      by_cases hselected : ordinal < snapshots.length
      · have hordinal : ordinal < observations.length := by
          rw [← haligned.length_eq]
          exact hselected
        exact relTriple_indicator_observedMaterializedBoundary_false_of_ordinal_lt ordinal
          parameter publicRoot rightRoot ftsSecret table target
          (liftM (OracleSpec.query query) >>= next) observations right.state rightFuel rightCache
          (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
            rightRoot (liftM (OracleSpec.query query) >>= next) snapshots delayedObservations left
            leftFuel leftCache)
          hordinal hnoHit
      · cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
                  directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
                simp only [hselected, ↓reduceDIte]
                let observe : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → List PlannedProbeSnapshot →
                      List CleanProbeObservation → ProbComp Bool :=
                  fun nextContext remaining value laterSnapshots laterObservations =>
                    directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret
                      table target rightRoot (next value.1) laterSnapshots laterObservations
                      nextContext remaining value.2
                apply relTriple_uniform_finishDirectDelayed ordinal parameter publicRoot
                  rightRoot ftsSecret table target n next observe snapshots observations
                  delayedObservations left
                  right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                  hrevealed hvalues hpublished hrightMaterialized htracked hcovered hnoHit hbudget
                intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                  have hfuel := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                    (splitUniformImpl_probeFree n leftCache) hleftSupport
                  omega
                have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                  have hfuel := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    (observedResolvedResult observations nextRight) 0
                    (splitUniformImpl_probeFree n rightCache) hrightSupport
                  simpa [observedResolvedResult] using hfuel
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                have hnextTracked : CleanProbeObservationsTrackedBy observations
                    nextRight.context.state := by
                  simpa [observedResolvedResult] using
                    (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                      ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                      htracked (observedResolvedResult observations nextRight) hrightSupport)
                have hnextCovered : CleanProbeObservationsCoverPending observations
                    nextRight.context.state := by
                  simpa [observedResolvedResult] using
                    (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                      ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                      hcovered (observedResolvedResult observations nextRight) hrightSupport)
                have hnextBudget : nextRight.remaining +
                    nextRight.context.state.pending.card < Fintype.card Digest := by
                  have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    (observedResolvedResult observations nextRight) hrightSupport
                  simpa [observedResolvedResult] using hremaining.trans_lt hbudget
                have hnextBefore : SnapshotsBefore snapshots canonical :=
                  (hbefore.of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft
                    hleftSupport).canonicalize_right table
                have hnextLeftCovered : PendingCoveredBy
                    (snapshots.map PlannedProbeSnapshot.toProbe) canonical := by
                  apply (pendingCoveredBy_canonicalize_iff table
                    (snapshots.map PlannedProbeSnapshot.toProbe) nextLeft.context).2
                  apply hleftCovered.of_subset
                  apply pending_subset_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft
                    (splitUniformImpl_probeFree n leftCache)
                  rw [← map_erase_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                  exact ⟨.done nextLeft, hleftSupport, rfl⟩
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hnextChainValid : ChainState.ValidFor (fun _ => True)
                    nextRight.context.state := by
                  have hnext := chainValid_of_mem_runObservedCleanFromTable
                    (splitUniformImpl n) observations right.state rightFuel table rightCache
                    (observedResolvedResult observations nextRight)
                    (preservesChainValid_splitUniformImpl (fun _ => True) n) hchainValid
                    hrightSupport
                  simpa [observedResolvedResult] using hnext
                unfold canonicalizeDirectDelayedSelectedRootIndicator
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [observe] using
                  (ih nextLeft.value.1 snapshots observations delayedObservations canonical
                    nextRight.context
                    nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                    (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                    hcanonicalRun.revealed_eq hcanonicalRun.values_le hcanonicalRun.left_published
                    hcanonicalRun.right_materialized hnextChainValid
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    haligned hnextBefore hnextTracked hnextCovered hnoHit hdelayedProbes
                    hdelayedNoHit
                    hnextLeftCovered
                    (by omega) (by omega) (by omega) hnextBudget)
            | inr input =>
                change HashOutput → OracleComp (OracleWorld + SigningSpec)
                  RetainedRestResult at next
                have hrightValues :
                    (materializedCanonicalContext table right.state).state.values =
                      left.state.values := by
                  unfold materializedCanonicalContext
                  rw [← hrightMaterialized]
                  exact canonicalized_right_values_eq_of_finalizationContextLE hcontext hrevealed
                    hcanonical
                have hplanEq :
                    purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table right.state).state =
                      purePlanProbingHashQuery parameter input left.state :=
                  purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
                let plan := purePlanProbingHashQuery parameter input left.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextSnapshots := appendPlannedSnapshot snapshots candidate? left
                by_cases hnowSelected : ordinal < nextSnapshots.length
                · have hcandidateExists : ∃ candidate, candidate? = some candidate := by
                    cases hcandidate : candidate? with
                    | none =>
                        exfalso
                        apply hselected
                        simpa [nextSnapshots, hcandidate, appendPlannedSnapshot] using hnowSelected
                    | some candidate => exact ⟨candidate, rfl⟩
                  obtain ⟨candidate, hcandidate⟩ := hcandidateExists
                  have hnextSnapshots : nextSnapshots =
                      snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)] := by
                    simp [nextSnapshots, hcandidate, appendPlannedSnapshot]
                  have hordinal : snapshots.length = ordinal := by
                    rw [hnextSnapshots] at hnowSelected
                    simp only [List.length_append, List.length_singleton] at hnowSelected
                    omega
                  subst ordinal
                  have hget : nextSnapshots.get ⟨snapshots.length, hnowSelected⟩ =
                      (⟨candidate, left⟩ : PlannedProbeSnapshot) := by
                    simp [nextSnapshots, appendPlannedSnapshot, hcandidate, List.get_eq_getElem]
                  let selection : PrivateOrdinalSelection :=
                    ⟨candidate, left,
                      (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
                        PlannedProbeSnapshot.toProbe⟩
                  have hselectedEq :
                      directDelayedSelectedRootIndicator snapshots.length parameter publicRoot ftsSecret
                          table target rightRoot
                          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                            (Sum.inl (Sum.inr input))) >>= next)
                          snapshots delayedObservations left leftFuel leftCache =
                        delayedSelectedRootIndicator snapshots.length parameter publicRoot ftsSecret table
                          target rightRoot
                          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                            (Sum.inl (Sum.inr input))) >>= next)
                          delayedObservations selection leftFuel leftCache := by
                    rw [directDelayedSelectedRootIndicator_hash_eq_selected snapshots.length parameter
                      publicRoot ftsSecret table target rightRoot input next snapshots
                      delayedObservations left leftFuel leftCache hselected
                      (by simpa [nextSnapshots] using hnowSelected)]
                    rw [show (appendPlannedSnapshot snapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input left.state)) left).get
                          ⟨snapshots.length, by simpa [nextSnapshots] using hnowSelected⟩ =
                        (⟨candidate, left⟩ : PlannedProbeSnapshot) by
                          simpa [nextSnapshots] using hget]
                    have hcandidateRaw : rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input left.state) = some candidate := by
                      simpa [candidate?, plan] using hcandidate
                    simp [selection, hcandidateRaw, appendPlannedCandidate]
                  rw [hselectedEq]
                  by_cases hgoodExists : ∃ output,
                      selection.GoodForRoots target output rightRoot snapshots.length ∧
                        PendingCoveredBy (selection.candidates.take snapshots.length) selection.context
                  · obtain ⟨output, hselectionGood, hselectionCovered⟩ := hgoodExists
                    have hmaterializedValues :
                        (materializedDeferredState left).values = right.state.values :=
                      materializedDeferredState_values_eq_of_chainValid table left right hcontext
                        hrevealed hvalues hpublished hchainValid hrightMaterialized
                    have hcompletionState : CompletionSafeStateLE table
                        (materializedDeferredState left) right.state :=
                      completionSafeStateLE_materialized_of_finalizationContextLE table left right
                        hcontext hrevealed hmaterializedValues
                    have hinstalledState :
                        materializedDeferredState
                            { selection.context with
                              values := selection.context.values.install target output } =
                          materializedDeferredState left := by
                      simpa [selection] using
                        (materializedDeferredState_install_eq_of_value left target output
                          hselectionGood.2.2.2.1)
                    have hcompletionInstalled : CompletionSafeStateLE table
                        (materializedDeferredState
                          { selection.context with
                            values := selection.context.values.install target output })
                        right.state := by
                      rw [hinstalledState]
                      exact hcompletionState
                    let resolved : DeferredResolution :=
                      ⟨{ state := selection.context.state.clearPending (.position target)
                         values := selection.context.values }, output⟩
                    have hresolve : resolveDeferredPositionValue target selection.context =
                        pure (some resolved) := by
                      simpa [resolved] using
                        resolveDeferredPositionValue_eq_good_output hselectionGood
                          hselectionCovered
                    have hresolved : some resolved ∈ support
                        (resolveDeferredPositionValue target selection.context) := by
                      rw [hresolve]
                      simp
                    let resolvedState := materializedDeferredState resolved.toDeferredContext
                    have hsafe : SafeTargetPendingLE target output resolvedState
                        (materializedDeferredState
                          { selection.context with
                            values := selection.context.values.install target output }) := by
                      exact safeTargetPendingLE_of_resolveDeferredPositionValue hselectionGood
                        hselectionCovered resolved hresolved
                    have hcompletionResolved : CompletionSafeStateLE table resolvedState
                        right.state := by
                      refine ⟨hsafe.values.trans hcompletionInstalled.values,
                        hsafe.revealed.trans hcompletionInstalled.revealed, ?_⟩
                      intro coordinate digest hentry
                      rcases hcompletionInstalled.pending coordinate digest
                          (hsafe.pending hentry) with hright | hknown | hchain
                      · exact Or.inl hright
                      · right
                        left
                        obtain ⟨known, hknownValue, hmiss⟩ := hknown
                        refine ⟨known, ?_, hmiss⟩
                        rw [hsafe.values]
                        exact hknownValue
                      · exact Or.inr (Or.inr hchain)
                    have hresolvedStarts : StartTableAgrees resolvedState table := by
                      intro index stored hstored
                      apply hcontext.view.rightStarts index stored
                      rw [← hcompletionResolved.values]
                      exact hstored
                    have hresolvedPublicValues :
                        (materializedCanonicalContext table resolvedState).state.values =
                          left.state.values := by
                      calc
                        _ = (materializedCanonicalContext table right.state).state.values :=
                          materializedCanonicalContext_values_eq_of_completionSafe table
                            hcompletionResolved
                        _ = left.state.values := hrightValues
                    have hresolvedPlan :
                        purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table resolvedState).state = plan := by
                      simpa [plan] using
                        (purePlanProbingHashQuery_eq_of_values_eq hresolvedPublicValues parameter
                          input)
                    have hresolvedCandidate : rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table resolvedState).state) =
                          some candidate := by
                      rw [hresolvedPlan]
                      simpa [candidate?, plan] using hcandidate
                    have hcandidateEq : candidate =
                        ⟨.position target, truncateHash output⟩ := by
                      simpa [selection] using hselectionGood.1
                    have hresolvedHidden : candidate.coordinate ∉ resolvedState.revealed := by
                      rw [hcandidateEq]
                      simpa [resolvedState, resolved, materializedDeferredState_revealed,
                        LazyRevealProbe.State.clearPending] using
                        hselectionGood.2.2.1
                    have hresolvedValue : resolvedState.values candidate.coordinate =
                        some output := by
                      rw [hcandidateEq]
                      exact hsafe.target_value
                    have hresolvedDoomed : DoomedResolvedContext table
                        (directDeferredContext
                          (resolvedState.addPending candidate.coordinate candidate.candidate)) := by
                      rw [hcandidateEq]
                      exact doomed_direct_addPending_of_stored resolvedState (.position target)
                        output hsafe.target_value hresolvedStarts
                    have hboundPositive : 0 < bound := by
                      rcases hbound.1 with hnot | hpositive
                      · exact (hnot (by simp [IsOuterHash])).elim
                      · exact hpositive
                    have hrightPositive : 0 < rightFuel := by omega
                    have hleftDoomed : ∀ result : ObservedCleanRunResult
                        (RetainedRestResult × SplitHashCache),
                        some result ∈ support
                            (observedMaterializedBoundary parameter publicRoot ftsSecret
                              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                                (Sum.inl (Sum.inr input))) >>= next)
                              observations resolvedState rightFuel table rightCache) →
                          ¬DeferredCompletable table
                            (directDeferredContext result.state) := by
                      intro result hresult
                      rw [observedMaterializedBoundary_hash_query_bind] at hresult
                      change some result ∈ support
                        (observedMaterializedHashContinuation parameter publicRoot ftsSecret input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table resolvedState).state)
                          next observations resolvedState rightFuel table rightCache) at hresult
                      have hstopped := stopped_data_of_mem_observedMaterializedHashContinuation
                        parameter publicRoot ftsSecret input
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table resolvedState).state)
                        candidate next observations resolvedState (rightFuel - 1) table rightCache
                        result hresolvedCandidate hresolvedHidden hresolvedDoomed (by
                          simpa [Nat.sub_add_cancel hrightPositive] using hresult)
                      exact hstopped.2.1.2.2
                    have hsameFuel :=
                      relTriple_indicator_observedMaterializedBoundary_completionSafe_of_left_doomed
                        snapshots.length parameter publicRoot rightRoot ftsSecret table target
                        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                          (Sum.inl (Sum.inr input))) >>= next)
                        observations resolvedState right.state rightFuel rightCache
                        hcompletionResolved hresolvedStarts hbudget hleftDoomed
                    rw [delayedSelectedRootIndicator, hresolve]
                    simp only [pure_bind]
                    let selectedComputation :=
                      liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                        (Sum.inl (Sum.inr input))) >>= next
                    have hselectedBound : selectedComputation.IsQueryBoundP IsOuterHash bound := by
                      unfold selectedComputation
                      rw [OracleComp.isQueryBoundP_query_bind_iff]
                      exact hbound
                    have hcacheBridge :=
                      relTriple_indicator_observedMaterializedBoundary_ordinaryCache
                        snapshots.length parameter publicRoot rightRoot ftsSecret table target
                        selectedComputation observations delayedObservations resolvedState rightFuel
                        rightCache leftCache hcache.symm haligned.length_eq.symm
                        (haligned.map_toProbe_eq.symm.trans hdelayedProbes.symm) hnoHit
                        hdelayedNoHit
                    have hfuelBridge :=
                      relTriple_indicator_observedMaterializedBoundary_fuel_of_isQueryBoundP
                        snapshots.length parameter publicRoot rightRoot ftsSecret table target
                        selectedComputation delayedObservations resolvedState rightFuel leftFuel
                        bound leftCache hselectedBound (by omega) hleftLower
                    have hstateCache := SphincsSecurity.relTriple_trans_exists hsameFuel hcacheBridge
                    have hstateCache' : RelTriple
                        ((successfulObservedRootComparisonIndicator table snapshots.length target ∘
                            fun observed ↦ (observed, rightRoot)) <$>
                          observedMaterializedBoundary parameter publicRoot ftsSecret
                            selectedComputation observations right.state rightFuel table rightCache)
                        ((successfulObservedRootComparisonIndicator table snapshots.length target ∘
                            fun observed ↦ (observed, rightRoot)) <$>
                          observedMaterializedBoundary parameter publicRoot ftsSecret
                            selectedComputation delayedObservations resolvedState rightFuel table
                            leftCache)
                        SuccessfulObservedIndicatorRel := by
                      apply relTriple_post_mono hstateCache
                      intro actual delayed hrelation hactual
                      obtain ⟨middle, hfirst, hsecond⟩ := hrelation
                      exact hsecond (hfirst hactual)
                    have hfinal := SphincsSecurity.relTriple_trans_exists hstateCache' hfuelBridge
                    apply relTriple_post_mono hfinal
                    intro actual delayed hrelation hactual
                    obtain ⟨middle, hfirst, hsecond⟩ := hrelation
                    simpa [selectedComputation, resolvedState] using hsecond (hfirst hactual)
                  · let real :=
                      (successfulObservedRootComparisonIndicator table snapshots.length target ∘
                          fun observed ↦ (observed, rightRoot)) <$>
                        observedMaterializedBoundary parameter publicRoot ftsSecret
                          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                            (Sum.inl (Sum.inr input))) >>= next)
                          observations right.state rightFuel table rightCache
                    let delayed := delayedSelectedRootIndicator snapshots.length parameter publicRoot
                      ftsSecret table target rightRoot
                      (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                        (Sum.inl (Sum.inr input))) >>= next)
                      delayedObservations selection leftFuel leftCache
                    have hbase := relTriple_true real delayed
                    have hsupported :=
                      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
                        hbase (fun result ↦ result ∈ support real) (fun _ hresult ↦ hresult)
                    apply relTriple_post_mono hsupported
                    intro actual _delayed hrelation hactual
                    have hactualSupport : true ∈ support real := by
                      simpa [hactual] using hrelation.2
                    unfold real at hactualSupport
                    rw [support_map] at hactualSupport
                    obtain ⟨result, hresult, hindicator⟩ := hactualSupport
                    have hgood :
                        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
                          table snapshots.length target rightRoot result := by
                      change successfulObservedRootComparisonIndicator table snapshots.length target
                        (result, rightRoot) = true at hindicator
                      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hindicator
                      exact hindicator
                    cases result with
                    | none =>
                        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                          at hgood
                    | some result =>
                        obtain ⟨output, houtputGood, houtputCovered⟩ :=
                          selectedHash_goodForRoots snapshots.length parameter publicRoot rightRoot
                            ftsSecret table target input next snapshots observations left right
                            rightFuel rightCache candidate
                            (by simpa [candidate?, plan] using hcandidate) rfl hcontext
                            hrevealed hrightMaterialized hcanonical haligned hbefore htracked
                            hnoHit hleftCovered result hresult hgood
                        exact (hgoodExists ⟨output, by simpa [selection] using houtputGood,
                          by simpa [selection] using houtputCovered⟩).elim
                · rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter
                    publicRoot ftsSecret table target rightRoot input next snapshots
                    delayedObservations left leftFuel leftCache hselected
                    (by simpa [nextSnapshots, candidate?, plan] using hnowSelected)]
                  rw [observedMaterializedBoundary_hash_query_bind]
                  simp only
                  rw [hplanEq]
                  have hpublicExecutor :
                      probingHashQueryAfterRootAwarePublicPlan parameter input
                          (materializedCanonicalContext table right.state).state plan =
                        probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                    probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                      hrightValues plan
                  rw [hpublicExecutor]
                  let delayedNextObservations := observationsAfterCandidate delayedObservations
                    (materializedDeferredState left) candidate?
                  let leftStep : ProbComp (DirectWitnessResult
                      (HashOutput × SplitHashCache)) :=
                    runDirectResolvedWitnessFromTable left leftFuel table
                      ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                  let rightStep : ProbComp (Option (ObservedCleanRunResult
                      (HashOutput × SplitHashCache))) :=
                    runObservedCleanFromTable observations right.state rightFuel table
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                        rightCache)
                  have hrealEq :
                      ((successfulObservedRootComparisonIndicator table ordinal target ∘
                          fun observed ↦ (observed, rightRoot)) <$>
                        (rightStep >>= fun result =>
                          match result with
                          | none => pure none
                          | some result =>
                              observedMaterializedBoundary parameter publicRoot ftsSecret
                                (next result.value.1) result.observations result.state
                                result.remaining table result.value.2)) =
                        (rightStep >>= fun result =>
                          match result with
                          | none => pure false
                          | some result =>
                              (successfulObservedRootComparisonIndicator table ordinal target ∘
                                  fun observed ↦ (observed, rightRoot)) <$>
                                observedMaterializedBoundary parameter publicRoot ftsSecret
                                  (next result.value.1) result.observations result.state
                                  result.remaining table result.value.2) := by
                    rw [map_bind]
                    apply bind_congr
                    intro result
                    cases result with
                    | none =>
                        simp [successfulObservedRootComparisonIndicator,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                    | some result => rfl
                  have hrealPointwise (result : Option (ObservedCleanRunResult
                      (HashOutput × SplitHashCache))) :
                      ((successfulObservedRootComparisonIndicator table ordinal target ∘
                          fun observed ↦ (observed, rightRoot)) <$>
                        match result with
                        | none => pure none
                        | some result =>
                            observedMaterializedBoundary parameter publicRoot ftsSecret
                              (next result.value.1) result.observations result.state
                              result.remaining table result.value.2) =
                        (match result with
                        | none => pure false
                        | some result =>
                            (successfulObservedRootComparisonIndicator table ordinal target ∘
                                fun observed ↦ (observed, rightRoot)) <$>
                              observedMaterializedBoundary parameter publicRoot ftsSecret
                                (next result.value.1) result.observations result.state
                                result.remaining table result.value.2) := by
                    cases result with
                    | none =>
                        simp [successfulObservedRootComparisonIndicator,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                    | some result => rfl
                  rw [map_bind]
                  let observe : DeferredContext → Nat → (HashOutput × SplitHashCache) →
                      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool :=
                    fun nextContext remaining value laterSnapshots laterObservations =>
                      directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret
                        table target rightRoot (next value.1) laterSnapshots laterObservations
                        nextContext remaining value.2
                  have hcontextDirect :
                      FinalizationContextLE table left (directDeferredContext right.state) := by
                    rwa [← hrightMaterialized]
                  have houter : IsOuterHash (.inl (.inr input)) := by simp [IsOuterHash]
                  have hboundPositive : 0 < bound := by
                    rcases hbound.1 with hnot | hpositive
                    · exact (hnot houter).elim
                    · exact hpositive
                  have hleftPositive : 0 < leftFuel := by omega
                  have hstrictFuel : leftFuel < rightFuel := by omega
                  have hcontinue (actualNextObservations : List CleanProbeObservation)
                      (hnextAligned : SnapshotsObservedAt table nextSnapshots actualNextObservations)
                      (hnextNoHit : ∀ observation ∈ actualNextObservations,
                        ¬observation.ExistingHiddenHit)
                      (hnextDelayedProbes : delayedNextObservations.map
                          CleanProbeObservation.toProbe =
                        nextSnapshots.map PlannedProbeSnapshot.toProbe)
                      (hnextDelayedNoHit : ∀ observation ∈ delayedNextObservations,
                        ¬observation.ExistingHiddenHit)
                      (hlocal : RelTriple leftStep rightStep
                        (WitnessObservedFirstStoppedStepRel table actualNextObservations)) :
                      RelTriple
                        (rightStep >>= fun result =>
                          (successfulObservedRootComparisonIndicator table ordinal target ∘
                              fun observed ↦ (observed, rightRoot)) <$>
                            match result with
                            | none => pure none
                            | some result =>
                                observedMaterializedBoundary parameter publicRoot ftsSecret
                                  (next result.value.1) result.observations result.state
                                  result.remaining table result.value.2)
                        (leftStep >>= finishDirectDelayedSelectedRootIndicator
                          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                          nextSnapshots delayedNextObservations)
                        SuccessfulObservedIndicatorRel := by
                    let middle : ProbComp Bool := rightStep >>= fun result =>
                      match result with
                      | none => pure false
                      | some result =>
                          (successfulObservedRootComparisonIndicator table ordinal target ∘
                              fun observed ↦ (observed, rightRoot)) <$>
                            observedMaterializedBoundary parameter publicRoot ftsSecret
                              (next result.value.1) result.observations result.state
                              result.remaining table result.value.2
                    have hfinish : RelTriple middle
                        (leftStep >>= finishDirectDelayedSelectedRootIndicator
                          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                          nextSnapshots delayedNextObservations)
                        SuccessfulObservedIndicatorRel := by
                      unfold middle
                      convert (relTriple_bind_observed_finishDirectDelayed_of_firstStopped
                        (α := HashOutput) ordinal parameter publicRoot rightRoot ftsSecret table
                        target next observe nextSnapshots actualNextObservations
                        delayedNextObservations leftStep rightStep hlocal (by
                          intro nextLeft nextRight hleftSupport hrightSupport hclean
                          have hcanonicalRun := hclean.canonicalize_left
                          let canonical := canonicalizeMaterializedValues table nextLeft.context
                          have hleftCompletable : DeferredCompletable table canonical :=
                            hcanonicalRun.context_le.leftCompletable
                          have hleftFuelSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                            fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                              leftFuel table nextLeft 1
                              (probingHashQueryAfterPlan_isProbeBound_one parameter input plan
                                leftCache)
                              hleftSupport
                          have hrightFuelSpent : rightFuel ≤ nextRight.remaining + 1 := by
                            have hfuel := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                                plan).run rightCache) observations right.state rightFuel table
                              (observedResolvedResult actualNextObservations nextRight) 1
                              (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter
                                input left.state plan rightCache) hrightSupport
                            simpa [observedResolvedResult] using hfuel
                          have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                            remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                              leftFuel table nextLeft (by
                                rw [← map_erase_runDirectResolvedWitnessFromTable
                                  ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                                  left leftFuel table, support_map]
                                exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                          have hnextTracked : CleanProbeObservationsTrackedBy actualNextObservations
                              nextRight.context.state := by
                            simpa [rightStep, observedResolvedResult] using
                              (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                                  plan).run rightCache) observations right.state rightFuel table
                                htracked (observedResolvedResult actualNextObservations nextRight)
                                hrightSupport)
                          have hnextCovered : CleanProbeObservationsCoverPending
                              actualNextObservations nextRight.context.state := by
                            simpa [rightStep, observedResolvedResult] using
                              (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                                  plan).run rightCache) observations right.state rightFuel table
                                hcovered (observedResolvedResult actualNextObservations nextRight)
                                hrightSupport)
                          have hnextBudget : nextRight.remaining +
                              nextRight.context.state.pending.card < Fintype.card Digest := by
                            have hremaining :=
                              remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                                  plan).run rightCache) observations right.state rightFuel table
                                (observedResolvedResult actualNextObservations nextRight)
                                hrightSupport
                            simpa [observedResolvedResult] using hremaining.trans_lt hbudget
                          have hnextBefore : SnapshotsBefore nextSnapshots canonical :=
                            ((hbefore.appendPlannedSnapshot candidate?).of_done_runDirectResolvedWitnessFromTable
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                              leftFuel table nextLeft hleftSupport).canonicalize_right table
                          have hnextCandidates : nextSnapshots.map PlannedProbeSnapshot.toProbe =
                              appendPlannedCandidate
                                (snapshots.map PlannedProbeSnapshot.toProbe) candidate? := by
                            cases hcandidate' : candidate? <;>
                              simp [nextSnapshots, hcandidate', appendPlannedSnapshot,
                                appendPlannedCandidate]
                          have hcoveredAtStart : PendingCoveredBy
                              (nextSnapshots.map PlannedProbeSnapshot.toProbe) left := by
                            apply hleftCovered.mono_candidates
                            cases hcandidate' : candidate? <;>
                              simp [nextSnapshots, hcandidate', appendPlannedSnapshot]
                          have hplanMem : ∀ candidate, plan.candidate? = some candidate →
                              candidate ∈ nextSnapshots.map PlannedProbeSnapshot.toProbe := by
                            intro candidate hcandidate
                            rw [hnextCandidates]
                            have hrecorded :=
                              rootAwarePlannedCandidate?_eq_of_plan_some hcandidate
                            have hcandidateRoot : candidate? = some candidate := by
                              simpa [candidate?, plan, rootAwareCandidateForPlan?_purePlan] using
                                hrecorded
                            simp [appendPlannedCandidate, hcandidateRoot]
                          have hprobeBound := probingHashQueryAfterPlan_probeBound parameter input
                            plan (nextSnapshots.map PlannedProbeSnapshot.toProbe) hplanMem leftCache
                          have hnextLeftCovered : PendingCoveredBy
                              (nextSnapshots.map PlannedProbeSnapshot.toProbe) canonical := by
                            apply (pendingCoveredBy_canonicalize_iff table
                              (nextSnapshots.map PlannedProbeSnapshot.toProbe) nextLeft.context).2
                            apply pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
                              (nextSnapshots.map PlannedProbeSnapshot.toProbe)
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                              leftFuel table nextLeft hcoveredAtStart hprobeBound
                            rw [← map_erase_runDirectResolvedWitnessFromTable
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                              leftFuel table, support_map]
                            exact ⟨.done nextLeft, hleftSupport, rfl⟩
                          have hnotPrivate : ¬PrivateStructuralHit canonical :=
                            not_privateStructuralHit_of_deferredCompletable hleftCompletable
                          have hnoChain : NoExistingHiddenChainStartHits observations := by
                            intro observation hobservation hhit
                            exact hnoHit observation hobservation hhit.1
                          have hnextChainValid : ChainState.ValidFor (fun _ => True)
                              nextRight.context.state := by
                            have hnext := rootAwarePublic_invariants_of_mem_runObservedCleanFromTable
                              parameter input left.state plan observations right.state rightFuel
                              table rightCache (observedResolvedResult actualNextObservations
                                nextRight) hnoChain hchainValid hrightSupport
                            simpa [observedResolvedResult] using hnext.1
                          unfold canonicalizeDirectDelayedSelectedRootIndicator
                          simp only [canonical, hnotPrivate, hclean.left_published, ↓reduceIte,
                            hleftCompletable]
                          rw [← hclean.value_eq]
                          simpa [observe, IsOuterHash] using
                            (ih nextLeft.value.1 nextSnapshots actualNextObservations
                              delayedNextObservations canonical nextRight.context
                              nextLeft.remaining nextRight.remaining nextLeft.value.2
                              nextRight.value.2 (bound - 1)
                              (by simpa [IsOuterHash] using hbound.2 nextLeft.value.1)
                              hcanonicalRun.context_le hcanonicalRun.cache_eq
                              hcanonicalRun.revealed_eq hcanonicalRun.values_le
                              hcanonicalRun.left_published hcanonicalRun.right_materialized
                              hnextChainValid
                              (canonicalizeMaterializedValues_canonical table nextLeft.context
                                hclean.context_le.view.leftConsistent)
                              hnextAligned hnextBefore hnextTracked hnextCovered hnextNoHit
                              hnextDelayedProbes hnextDelayedNoHit hnextLeftCovered
                              (by omega) (by omega) (by omega)
                              hnextBudget))) using 1
                      apply bind_congr
                      intro result
                      cases result <;> rfl
                    have houter : RelTriple
                        (rightStep >>= fun result =>
                          (successfulObservedRootComparisonIndicator table ordinal target ∘
                              fun observed ↦ (observed, rightRoot)) <$>
                            match result with
                            | none => pure none
                            | some result =>
                                observedMaterializedBoundary parameter publicRoot ftsSecret
                                  (next result.value.1) result.observations result.state
                                  result.remaining table result.value.2)
                        middle
                        (EqRel Bool) := by
                      unfold middle
                      apply relTriple_bind (relTriple_refl rightStep)
                      intro actual expected heq
                      subst expected
                      exact relTriple_eqRel_of_eq (hrealPointwise actual)
                    have hglued := SphincsSecurity.relTriple_trans_exists
                      (ob := middle)
                      (oc := leftStep >>= finishDirectDelayedSelectedRootIndicator
                        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                        nextSnapshots delayedNextObservations)
                      (R := EqRel Bool) (S := SuccessfulObservedIndicatorRel) houter hfinish
                    apply relTriple_post_mono hglued
                    intro actual delayed hrelation
                    obtain ⟨middle, hactual, hmiddle⟩ := hrelation
                    exact hactual ▸ hmiddle
                  cases hcandidate : candidate? with
                  | none =>
                      have hnextSnapshots : nextSnapshots = snapshots := by
                        simp [nextSnapshots, hcandidate, appendPlannedSnapshot]
                      have hnextDelayedObservations : delayedNextObservations =
                          delayedObservations := by
                        simp [delayedNextObservations, hcandidate, observationsAfterCandidate]
                      have hlocal :=
                        relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_none
                          table parameter input plan observations left right leftFuel rightFuel
                          leftCache rightCache hcandidate (by omega) hcontext hcache hrevealed
                          hvalues hpublished hrightMaterialized htracked hcovered hnoHit hbudget
                      have hresult := hcontinue observations
                        (by simpa [hnextSnapshots] using haligned) hnoHit
                        (by simpa [hnextSnapshots, hnextDelayedObservations] using hdelayedProbes)
                        (by simpa [hnextDelayedObservations] using hdelayedNoHit)
                        (by simpa [leftStep, rightStep] using hlocal)
                      simp only [leftStep, rightStep, observe, plan, candidate?,
                        delayedNextObservations, hnextDelayedObservations, nextSnapshots,
                        hnextSnapshots] at hresult ⊢
                      convert hresult using 1
                      apply bind_congr
                      intro result
                      cases result <;> rfl
                  | some candidate =>
                      have hnextSnapshotsEq : nextSnapshots =
                          snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)] := by
                        simp [nextSnapshots, hcandidate, appendPlannedSnapshot]
                      let actualNextObservations := observations ++
                        [cleanProbeObservation right.state candidate.coordinate
                          candidate.candidate]
                      have hnextDelayedProbes : delayedNextObservations.map
                            CleanProbeObservation.toProbe =
                          nextSnapshots.map PlannedProbeSnapshot.toProbe := by
                        simp [delayedNextObservations, nextSnapshots, hcandidate,
                          observationsAfterCandidate, appendPlannedSnapshot,
                          CleanProbeObservation.toProbe, cleanProbeObservation, hdelayedProbes]
                      by_cases hcandidateRevealed : candidate.coordinate ∈ right.state.revealed
                      · have hnewNoHit : ¬(cleanProbeObservation right.state candidate.coordinate
                            candidate.candidate).ExistingHiddenHit := by
                          rintro ⟨hhidden, _output, _hvalue, _hcandidate⟩
                          simp [cleanProbeObservation, hcandidateRevealed] at hhidden
                        have hnextNoHit : ∀ observation ∈ actualNextObservations,
                            ¬observation.ExistingHiddenHit := by
                          intro observation hobservation
                          simp only [actualNextObservations, List.mem_append,
                            List.mem_singleton] at hobservation
                          rcases hobservation with hold | rfl
                          · exact hnoHit observation hold
                          · exact hnewNoHit
                        have hlocal :=
                          relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_revealed
                            table parameter input plan candidate observations left right leftFuel
                            (rightFuel - 1) leftCache rightCache hcandidate hleftPositive
                            (by omega) hcontext hcache hrevealed hvalues hpublished
                            hrightMaterialized hcandidateRevealed htracked hcovered hnoHit (by omega)
                        have hrightFuelEq : rightFuel - 1 + 1 = rightFuel := by omega
                        have hresult := hcontinue actualNextObservations
                          (by simpa [actualNextObservations, nextSnapshots, candidate?, hcandidate,
                              observationsAfterCandidate, appendPlannedSnapshot] using
                            (haligned.appendCandidate (some candidate) hcontextDirect hrevealed
                              hpublished hcanonical))
                          hnextNoHit hnextDelayedProbes
                          (by
                            intro observation hobservation
                            simp only [delayedNextObservations, observationsAfterCandidate,
                              hcandidate, List.mem_append, List.mem_singleton] at hobservation
                            rcases hobservation with hold | rfl
                            · exact hdelayedNoHit observation hold
                            · exact not_existingHiddenHit_cleanProbeObservation_materializedDeferredState
                                table left right candidate.coordinate candidate.candidate hcontext
                                hrevealed hvalues hrightMaterialized hnewNoHit)
                          (by simpa [leftStep, rightStep, hrightFuelEq] using hlocal)
                        simp only [leftStep, rightStep, observe, plan, candidate?, nextSnapshots,
                          delayedNextObservations] at hresult ⊢
                        convert hresult using 1
                        apply bind_congr
                        intro result
                        cases result <;> rfl
                      · let postRight : DeferredContext :=
                          { right with state :=
                              right.state.addPending candidate.coordinate candidate.candidate }
                        by_cases hpostCompletable : DeferredCompletable table postRight
                        · have hnewNoHit :
                              ¬(cleanProbeObservation right.state candidate.coordinate
                                candidate.candidate).ExistingHiddenHit :=
                            not_existingHiddenHit_cleanProbeObservation_of_addPending_completable
                              table right candidate hpostCompletable
                          have hnextNoHit : ∀ observation ∈ actualNextObservations,
                              ¬observation.ExistingHiddenHit := by
                            intro observation hobservation
                            simp only [actualNextObservations, List.mem_append,
                              List.mem_singleton] at hobservation
                            rcases hobservation with hold | rfl
                            · exact hnoHit observation hold
                            · exact hnewNoHit
                          have hpostBudget : (rightFuel - 1) +
                              (right.state.addPending candidate.coordinate
                                candidate.candidate).pending.card < Fintype.card Digest := by
                            have hcard := LazyRevealProbe.State.pending_card_addPending_le
                              right.state candidate.coordinate candidate.candidate
                            omega
                          have hlocal :=
                            relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_hidden_completable
                              table parameter input plan candidate observations left right leftFuel
                              (rightFuel - 1) leftCache rightCache hcandidate hleftPositive
                              (by omega) hcontext hcache hrevealed hvalues hpublished
                              hrightMaterialized hcandidateRevealed hpostCompletable htracked
                              hcovered hnoHit hpostBudget
                          have hrightFuelEq : rightFuel - 1 + 1 = rightFuel := by omega
                          have hresult := hcontinue actualNextObservations
                            (by simpa [actualNextObservations, nextSnapshots, candidate?, hcandidate,
                                observationsAfterCandidate, appendPlannedSnapshot] using
                              (haligned.appendCandidate (some candidate) hcontextDirect hrevealed
                                hpublished hcanonical))
                            hnextNoHit hnextDelayedProbes
                            (by
                              intro observation hobservation
                              simp only [delayedNextObservations, observationsAfterCandidate,
                                hcandidate, List.mem_append, List.mem_singleton] at hobservation
                              rcases hobservation with hold | rfl
                              · exact hdelayedNoHit observation hold
                              · exact not_existingHiddenHit_cleanProbeObservation_materializedDeferredState
                                  table left right candidate.coordinate candidate.candidate hcontext
                                  hrevealed hvalues hrightMaterialized hnewNoHit)
                            (by simpa [leftStep, rightStep, hrightFuelEq] using hlocal)
                          simp only [leftStep, rightStep, observe, plan, candidate?, nextSnapshots,
                            delayedNextObservations] at hresult ⊢
                          convert hresult using 1
                          apply bind_congr
                          intro result
                          cases result <;> rfl

                        · have hnoncompletable :=
                            relTriple_indicator_observedMaterializedHashContinuation_hidden_notCompletable
                              ordinal parameter publicRoot rightRoot ftsSecret table target input plan
                              candidate next snapshots observations left right rightFuel rightCache
                              (leftStep >>= finishDirectDelayedSelectedRootIndicator
                                (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                                nextSnapshots delayedNextObservations)
                              hcandidate (by simpa [hnextSnapshotsEq] using hnowSelected) hcontext
                              hrevealed hcanonical hrightMaterialized hcandidateRevealed hnoHit
                              haligned hbefore htracked (by omega) hbudget (by
                                simpa [postRight] using hpostCompletable)
                          simp only [leftStep, rightStep, observe, plan, candidate?, nextSnapshots,
                            delayedNextObservations, observedMaterializedHashContinuation,
                            hpublicExecutor, map_bind] at hnoncompletable ⊢
                          convert hnoncompletable using 1
                          apply bind_congr
                          intro result
                          cases result <;> rfl
        | inr message =>
            change Option Signature → OracleComp (OracleWorld + SigningSpec)
              RetainedRestResult at next
            have hleft :
                ((successfulObservedRootComparisonIndicator table ordinal target ∘
                    fun observed ↦ (observed, rightRoot)) <$>
                  observedMaterializedBoundary parameter publicRoot ftsSecret
                    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (Sum.inr message)) >>= next)
                    observations right.state rightFuel table rightCache) =
                  (runObservedCleanFromTable observations right.state rightFuel table
                      ((maskedSign parameter publicRoot ftsSecret message).run rightCache) >>=
                    fun result =>
                      match result with
                      | none => pure false
                      | some result =>
                          (successfulObservedRootComparisonIndicator table ordinal target ∘
                              fun observed ↦ (observed, rightRoot)) <$>
                            observedMaterializedBoundary parameter publicRoot ftsSecret
                              (next result.value.1) result.observations result.state
                              result.remaining table result.value.2) := by
              rw [observedMaterializedBoundary, OracleComp.construct_query_bind, map_bind]
              apply bind_congr
              intro result
              cases result with
              | none =>
                  simp [successfulObservedRootComparisonIndicator,
                    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                    ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                    ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
              | some result => rfl
            rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
            simp only [hselected, ↓reduceDIte]
            rw [hleft]
            let observe : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → List PlannedProbeSnapshot →
                  List CleanProbeObservation → ProbComp Bool :=
              fun nextContext remaining value laterSnapshots laterObservations =>
                directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table
                  target rightRoot (next value.1) laterSnapshots laterObservations nextContext
                  remaining value.2
            apply relTriple_sign_finishDirectDelayed ordinal parameter publicRoot rightRoot
              ftsSecret table target message next observe snapshots observations delayedObservations
              left right
              leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache hrevealed
              hvalues hpublished hrightMaterialized htracked hcovered hnoHit hbudget
            intro nextLeft nextRight hleftSupport hrightSupport hclean
            have hcanonicalRun := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hleftCompletable : DeferredCompletable table canonical :=
              hcanonicalRun.context_le.leftCompletable
            have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
              have hfuel := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left leftFuel
                table nextLeft 0
                (maskedSign_probeFree parameter publicRoot ftsSecret message leftCache)
                hleftSupport
              omega
            have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
              have hfuel := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run rightCache) observations
                right.state rightFuel table (observedResolvedResult observations nextRight) 0
                (maskedSign_probeFree parameter publicRoot ftsSecret message rightCache)
                hrightSupport
              simpa [observedResolvedResult] using hfuel
            have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
              remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left leftFuel
                table nextLeft (by
                  rw [← map_erase_runDirectResolvedWitnessFromTable
                    ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left
                    leftFuel table, support_map]
                  exact ⟨.done nextLeft, hleftSupport, rfl⟩)
            have hnextTracked : CleanProbeObservationsTrackedBy observations
                nextRight.context.state := by
              simpa [observedResolvedResult] using
                (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter publicRoot ftsSecret message).run rightCache)
                  observations right.state rightFuel table htracked
                  (observedResolvedResult observations nextRight) hrightSupport)
            have hnextCovered : CleanProbeObservationsCoverPending observations
                nextRight.context.state := by
              simpa [observedResolvedResult] using
                (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                  ((maskedSign parameter publicRoot ftsSecret message).run rightCache)
                  observations right.state rightFuel table hcovered
                  (observedResolvedResult observations nextRight) hrightSupport)
            have hnextBudget : nextRight.remaining + nextRight.context.state.pending.card <
                Fintype.card Digest := by
              have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run rightCache) observations
                right.state rightFuel table (observedResolvedResult observations nextRight)
                hrightSupport
              simpa [observedResolvedResult] using hremaining.trans_lt hbudget
            have hnextBefore : SnapshotsBefore snapshots canonical :=
              (hbefore.of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left leftFuel
                table nextLeft hleftSupport).canonicalize_right table
            have hnextLeftCovered : PendingCoveredBy
                (snapshots.map PlannedProbeSnapshot.toProbe) canonical := by
              apply (pendingCoveredBy_canonicalize_iff table
                (snapshots.map PlannedProbeSnapshot.toProbe) nextLeft.context).2
              apply hleftCovered.of_subset
              apply pending_subset_of_done_runDirectResolvedDetailedFromTable_of_probeFree
                ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left leftFuel
                table nextLeft
                (maskedSign_probeFree parameter publicRoot ftsSecret message leftCache)
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run leftCache) left leftFuel
                table, support_map]
              exact ⟨.done nextLeft, hleftSupport, rfl⟩
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hnextChainValid : ChainState.ValidFor (fun _ => True)
                nextRight.context.state := by
              have hnext := chainValid_of_mem_runObservedCleanFromTable
                (maskedSign parameter publicRoot ftsSecret message) observations right.state
                rightFuel table rightCache (observedResolvedResult observations nextRight)
                (preservesChainValid_maskedSign_true parameter publicRoot ftsSecret message)
                hchainValid hrightSupport
              simpa [observedResolvedResult] using hnext
            unfold canonicalizeDirectDelayedSelectedRootIndicator
            simp only [canonical, hnotPrivate, hclean.left_published, ↓reduceIte,
              hleftCompletable]
            rw [← hclean.value_eq]
            simpa [observe] using
              (ih nextLeft.value.1 snapshots observations delayedObservations canonical
                nextRight.context
                nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                hcanonicalRun.revealed_eq hcanonicalRun.values_le hcanonicalRun.left_published
                hcanonicalRun.right_materialized hnextChainValid
                (canonicalizeMaterializedValues_canonical table nextLeft.context
                  hclean.context_le.view.leftConsistent)
                haligned hnextBefore hnextTracked hnextCovered hnoHit hdelayedProbes
                hdelayedNoHit
                hnextLeftCovered
                (by omega) (by omega) (by omega) hnextBudget)

end SphincsSecurity.Concrete.OtsProbeSimulation
