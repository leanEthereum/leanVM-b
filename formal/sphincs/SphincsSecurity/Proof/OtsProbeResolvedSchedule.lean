import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Concrete one-time layer scheduling

The chronological signer resolves a selected layer before selecting the next one. The ordinary
signer selects all three layers first. This file permutes those operations without changing their
joint distribution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp
open OracleComp.ProgramLogic.Relational

abbrev DeferredLayerEncoding := Counter × (ChainIndex → Digit)

structure DeferredLayerStore where
  selected : Layer → Option DeferredLayerEncoding
  resolved : Layer → Option LayerPart
  cache : SplitHashCache

def emptyDeferredLayerStore (cache : SplitHashCache) : DeferredLayerStore :=
  { selected := fun _ => none
    resolved := fun _ => none
    cache := cache }

def projectDeferredLayerStore
    (result : ResolvedRunResult DeferredLayerStore) :
    ResolvedRunResult ((Layer → Option LayerPart) × SplitHashCache) :=
  { result with value := (result.value.resolved, result.value.cache) }

theorem DeferredCompletion.materializeResolvedPosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending =
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output)
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table
      (materializeResolvedPosition context position result) completion := by
  refine ⟨?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      change (context.state.materialize (.position position) result.output).values
        (.position position) = some output at hvalue
      have hsame : result.output = output := by
        exact Option.some.inj (by simpa [LazyRevealProbe.State.materialize] using hvalue)
      rw [← hsame]
      exact hcompletion.eq_positionValue position result.output hresolved
    · apply hcompletion.1 coordinate output
      rw [hstateValues]
      change (context.state.materialize (.position position) result.output).values
        coordinate = some output at hvalue
      simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    rw [hpending]
    change (coordinate, candidate) ∈
      (context.state.materialize (.position position) result.output).pending at hmember
    simpa [LazyRevealProbe.State.materialize] using hmember

theorem deferredCompletion_materializeResolvedPosition_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending =
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    DeferredCompletion table
        (materializeResolvedPosition context position result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  constructor
  · exact fun hcompletion => hcompletion.of_materializeResolvedPosition position result
      hstateValues (by rw [hpending]) hresolved
  · exact fun hcompletion => hcompletion.materializeResolvedPosition position result
      hstateValues hpending hresolved

theorem deferredCompletion_materializeResolvedChainStart_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hstarts : StartTableAgrees context.state table)
    (houtput : result.output = table index)
    (hstateValues : result.state.values = context.state.values)
    (hdeferredValues : result.values = context.values)
    (hpending : result.state.pending = context.state.pendingAway index.coordinate) :
    DeferredCompletion table
        (materializeResolvedChainStart context index result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  constructor
  · intro hcompletion
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      rw [hstateValues] at hvalue
      by_cases heq : coordinate = index.coordinate
      · subst coordinate
        have hcompletionTable := hcompletion.2.2.2 index
        have hsame : output = table index := hstarts index output hvalue
        rw [hsame]
        exact hcompletionTable
      · apply hcompletion.1 coordinate output
        simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize,
          Function.update_of_ne heq] using hvalue
    · intro position output hvalue
      apply hcompletion.2.1 position output
      simpa [materializeResolvedChainStart, hdeferredValues] using hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      rw [hpending] at hmember
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize] using hmember
  · intro hcompletion
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      by_cases heq : coordinate = index.coordinate
      · subst coordinate
        have hsame : output = result.output := by
          change (context.state.materialize index.coordinate result.output).values
            index.coordinate = some output at hvalue
          exact (Option.some.inj (by
            simpa [LazyRevealProbe.State.materialize] using hvalue)).symm
        rw [hsame, houtput]
        exact hcompletion.2.2.2 index
      · apply hcompletion.1 coordinate output
        rw [hstateValues]
        change (context.state.materialize index.coordinate result.output).values coordinate =
          some output at hvalue
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
    · intro position output hvalue
      apply hcompletion.2.1 position output
      simpa [materializeResolvedChainStart, hdeferredValues] using hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      rw [hpending]
      change (coordinate, candidate) ∈
        (context.state.materialize index.coordinate result.output).pending at hmember
      simpa [LazyRevealProbe.State.materialize] using hmember

theorem deferredCompletion_materializeResolvedReveal_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution) (hvalid : context.Valid)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    DeferredCompletion table
        (materializeResolvedPosition context position result) completion ↔
      DeferredCompletion table result.toDeferredContext completion := by
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context result
    hresult
  have hpending := resolveDeferredReveal_pendingAway_subset table position context result hresult
  have hresolved := resolveDeferredReveal_resolves table position context result hresult
  constructor
  · exact fun hcompletion => hcompletion.of_materializeResolvedPosition position result
      hstateValues hpending hresolved
  · intro hcompletion
    have hbase := hcompletion.of_resolveDeferredReveal hvalid.valuesConsistent hstarts position
      result hresult
    refine ⟨?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      by_cases heq : coordinate = .position position
      · subst coordinate
        change (context.state.materialize (.position position) result.output).values
          (.position position) = some output at hvalue
        have hsame : output = result.output := by
          exact (Option.some.inj (by
            simpa [LazyRevealProbe.State.materialize] using hvalue)).symm
        rw [hsame]
        exact hcompletion.eq_positionValue position result.output hresolved
      · apply hbase.1 coordinate output
        change (context.state.materialize (.position position) result.output).values
          coordinate = some output at hvalue
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
    · intro coordinate candidate hmember
      apply hbase.2.2.1 coordinate candidate
      change (coordinate, candidate) ∈
        (context.state.materialize (.position position) result.output).pending at hmember
      have haway : (coordinate, candidate) ∈
          context.state.pendingAway (.position position) := by
        simpa [LazyRevealProbe.State.materialize] using hmember
      exact (Finset.mem_filter.1 haway).1

def resolvedCompletionValue (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Coordinate → Option HashOutput
  | .chainStart lay tree leafIdx chainIdx => some (table ⟨lay, tree, leafIdx, chainIdx⟩)
  | .position position => context.positionValue position

theorem DeferredCompletion.eq_resolvedCompletionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : resolvedCompletionValue table context coordinate = some output) :
    completion coordinate = output := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      have houtput : output = table ⟨lay, tree, leafIdx, chainIdx⟩ := by
        simpa [resolvedCompletionValue] using hvalue.symm
      rw [houtput]
      exact hcompletion.2.2.2 ⟨lay, tree, leafIdx, chainIdx⟩
  | position position =>
      exact hcompletion.eq_positionValue position output
        (by simpa [resolvedCompletionValue] using hvalue)

noncomputable def completionOutputOfDigest (digest : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (digest, 0)

@[simp] theorem truncateHash_completionOutputOfDigest (digest : Digest) :
    truncateHash (completionOutputOfDigest digest) = digest := by
  change (splitHashOutput digestBits
    ((splitHashOutputEquiv digestBits (by decide)).symm (digest, 0))).1 = digest
  rw [show splitHashOutput digestBits = splitHashOutputEquiv digestBits (by decide) from rfl,
    Equiv.apply_symm_apply]

set_option maxRecDepth 100000 in
theorem pendingAt_eq_of_deferredCompletion_iff_of_value_none
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hleftCompletable : DeferredCompletable table left)
    (hcompletion : ∀ completion,
      DeferredCompletion table left completion ↔
        DeferredCompletion table right completion)
    (coordinate : Coordinate)
    (hleftValue : resolvedCompletionValue table left coordinate = none)
    (hrightValue : resolvedCompletionValue table right coordinate = none) :
    left.state.pendingAt coordinate = right.state.pendingAt coordinate := by
  rcases hleftCompletable with ⟨base, hbaseLeft⟩
  have hbaseRight := (hcompletion base).mp hbaseLeft
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [resolvedCompletionValue] at hleftValue
  | position position =>
      have hleftState : left.state.values (.position position) = none := by
        unfold resolvedCompletionValue DeferredContext.positionValue at hleftValue
        cases hstate : left.state.values (.position position) with
        | none => rfl
        | some output => simp [hstate] at hleftValue
      have hleftDeferred : left.values position = none := by
        unfold resolvedCompletionValue DeferredContext.positionValue at hleftValue
        simpa [hleftState] using hleftValue
      have hrightState : right.state.values (.position position) = none := by
        unfold resolvedCompletionValue DeferredContext.positionValue at hrightValue
        cases hstate : right.state.values (.position position) with
        | none => rfl
        | some output => simp [hstate] at hrightValue
      have hrightDeferred : right.values position = none := by
        unfold resolvedCompletionValue DeferredContext.positionValue at hrightValue
        simpa [hrightState] using hrightValue
      apply Finset.ext
      intro candidate
      rw [LazyRevealProbe.State.mem_pendingAt_iff,
        LazyRevealProbe.State.mem_pendingAt_iff]
      constructor
      · intro hleftPending
        by_contra hrightPending
        let output := completionOutputOfDigest candidate
        let updated := Function.update base (.position position) output
        have hupdatedRight : DeferredCompletion table right updated := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro other otherOutput hvalue
            have hne : other ≠ .position position := by
              intro heq
              subst other
              rw [hrightState] at hvalue
              contradiction
            simpa [updated, Function.update_of_ne hne] using
              hbaseRight.1 other otherOutput hvalue
          · intro other otherOutput hvalue
            by_cases heq : other = position
            · subst other
              rw [hrightDeferred] at hvalue
              contradiction
            have hcoordinate : Coordinate.position other ≠ Coordinate.position position := by
              simpa using heq
            simpa [updated, Function.update_of_ne hcoordinate] using
              hbaseRight.2.1 other otherOutput hvalue
          · intro other otherCandidate hpending
            by_cases heq : other = .position position
            · subst other
              have hcandidate : otherCandidate ≠ candidate := by
                intro hsame
                subst otherCandidate
                exact hrightPending hpending
              simpa [updated, output] using hcandidate.symm
            simpa [updated, Function.update_of_ne heq] using
              hbaseRight.2.2.1 other otherCandidate hpending
          · intro index
            have hne : index.coordinate ≠ .position position := by
              rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
              simp [OtsSecretIndex.coordinate]
            simpa [updated, Function.update_of_ne hne] using hbaseRight.2.2.2 index
        have hupdatedLeft := (hcompletion updated).mpr hupdatedRight
        have havoids := hupdatedLeft.2.2.1 (.position position) candidate hleftPending
        exact havoids (by simp [updated, output])
      · intro hrightPending
        by_contra hleftPending
        let output := completionOutputOfDigest candidate
        let updated := Function.update base (.position position) output
        have hupdatedLeft : DeferredCompletion table left updated := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro other otherOutput hvalue
            have hne : other ≠ .position position := by
              intro heq
              subst other
              rw [hleftState] at hvalue
              contradiction
            simpa [updated, Function.update_of_ne hne] using
              hbaseLeft.1 other otherOutput hvalue
          · intro other otherOutput hvalue
            by_cases heq : other = position
            · subst other
              rw [hleftDeferred] at hvalue
              contradiction
            have hcoordinate : Coordinate.position other ≠ Coordinate.position position := by
              simpa using heq
            simpa [updated, Function.update_of_ne hcoordinate] using
              hbaseLeft.2.1 other otherOutput hvalue
          · intro other otherCandidate hpending
            by_cases heq : other = .position position
            · subst other
              have hcandidate : otherCandidate ≠ candidate := by
                intro hsame
                subst otherCandidate
                exact hleftPending hpending
              simpa [updated, output] using hcandidate.symm
            simpa [updated, Function.update_of_ne heq] using
              hbaseLeft.2.2.1 other otherCandidate hpending
          · intro index
            have hne : index.coordinate ≠ .position position := by
              rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
              simp [OtsSecretIndex.coordinate]
            simpa [updated, Function.update_of_ne hne] using hbaseLeft.2.2.2 index
        have hupdatedRight := (hcompletion updated).mp hupdatedLeft
        have havoids := hupdatedRight.2.2.1 (.position position) candidate hrightPending
        exact havoids (by simp [updated, output])

structure FinalizationViewEq (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) : Prop where
  leftConsistent : left.ValuesConsistent
  rightConsistent : right.ValuesConsistent
  leftStarts : StartTableAgrees left.state table
  rightStarts : StartTableAgrees right.state table
  valueEq : resolvedCompletionValue table left = resolvedCompletionValue table right
  leftClean : ∀ coordinate output,
    resolvedCompletionValue table left coordinate = some output →
      ¬left.state.hitAt coordinate output
  rightClean : ∀ coordinate output,
    resolvedCompletionValue table right coordinate = some output →
      ¬right.state.hitAt coordinate output
  pendingEq : ∀ coordinate,
    resolvedCompletionValue table left coordinate = none →
      left.state.pendingAt coordinate = right.state.pendingAt coordinate

theorem FinalizationViewEq.refl (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (hvalid : context.Valid)
    (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    FinalizationViewEq table context context := by
  exact ⟨hvalid.valuesConsistent, hvalid.valuesConsistent, hstarts, hstarts, rfl,
    hclean, hclean, fun _ _ => rfl⟩

theorem FinalizationViewEq.symm
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) :
    FinalizationViewEq table right left := by
  refine ⟨hview.rightConsistent, hview.leftConsistent, hview.rightStarts,
    hview.leftStarts, hview.valueEq.symm, hview.rightClean, hview.leftClean, ?_⟩
  intro coordinate hvalue
  have hleftValue : resolvedCompletionValue table left coordinate = none := by
    rw [hview.valueEq]
    exact hvalue
  exact (hview.pendingEq coordinate hleftValue).symm

theorem FinalizationViewEq.trans
    {table : OtsSecretIndex → HashOutput} {left middle right : DeferredContext}
    (hleft : FinalizationViewEq table left middle)
    (hright : FinalizationViewEq table middle right) :
    FinalizationViewEq table left right := by
  refine ⟨hleft.leftConsistent, hright.rightConsistent, hleft.leftStarts,
    hright.rightStarts, hleft.valueEq.trans hright.valueEq, hleft.leftClean,
    hright.rightClean, ?_⟩
  intro coordinate hvalue
  have hmiddleValue : resolvedCompletionValue table middle coordinate = none := by
    rw [← hleft.valueEq]
    exact hvalue
  exact (hleft.pendingEq coordinate hvalue).trans
    (hright.pendingEq coordinate hmiddleValue)

theorem FinalizationViewEq.deferredCompletion_iff
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (completion : Coordinate → HashOutput) :
    DeferredCompletion table left completion ↔
      DeferredCompletion table right completion := by
  have transfer : ∀ {source target : DeferredContext},
      FinalizationViewEq table source target →
      DeferredCompletion table source completion →
      DeferredCompletion table target completion := by
    intro source target hsemantic hcompletion
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      have htargetValue : resolvedCompletionValue table target coordinate = some output := by
        cases coordinate with
        | chainStart lay tree leafIdx chainIdx =>
            have houtput := hsemantic.rightStarts
              ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
            simp [resolvedCompletionValue, houtput]
        | position position =>
            simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
      have hsourceValue : resolvedCompletionValue table source coordinate = some output := by
        rw [hsemantic.valueEq]
        exact htargetValue
      exact hcompletion.eq_resolvedCompletionValue coordinate output hsourceValue
    · intro position output hvalue
      have htargetValue : resolvedCompletionValue table target (.position position) =
          some output := by
        unfold resolvedCompletionValue DeferredContext.positionValue
        cases hstate : target.state.values (.position position) with
        | some cached =>
            have hsame := hsemantic.rightConsistent position cached hstate
            rw [hsame] at hvalue
            have hcached : cached = output := Option.some.inj hvalue
            simp [hstate, hcached]
        | none => simpa [hstate] using hvalue
      have hsourceValue : resolvedCompletionValue table source (.position position) =
          some output := by
        rw [hsemantic.valueEq]
        exact htargetValue
      exact hcompletion.eq_resolvedCompletionValue (.position position) output hsourceValue
    · intro coordinate candidate hmember
      cases hvalue : resolvedCompletionValue table target coordinate with
      | some output =>
          have hcompletionOutput : completion coordinate = output := by
            have hsourceValue : resolvedCompletionValue table source coordinate = some output := by
              rw [hsemantic.valueEq]
              exact hvalue
            exact hcompletion.eq_resolvedCompletionValue coordinate output hsourceValue
          intro hhit
          apply hsemantic.rightClean coordinate output hvalue
          unfold LazyRevealProbe.State.hitAt
          rw [LazyRevealProbe.State.mem_pendingAt_iff]
          have hcandidate : candidate = truncateHash output := by
            rw [← hhit, hcompletionOutput]
          simpa [hcandidate] using hmember
      | none =>
          have hsourceValue : resolvedCompletionValue table source coordinate = none := by
            rw [hsemantic.valueEq]
            exact hvalue
          have htargetPending : candidate ∈ target.state.pendingAt coordinate :=
            (LazyRevealProbe.State.mem_pendingAt_iff target.state coordinate candidate).2 hmember
          have hsourcePending : candidate ∈ source.state.pendingAt coordinate := by
            rw [hsemantic.pendingEq coordinate hsourceValue]
            exact htargetPending
          exact hcompletion.2.2.1 coordinate candidate
            ((LazyRevealProbe.State.mem_pendingAt_iff source.state coordinate candidate).1
              hsourcePending)
  constructor
  · exact transfer hview
  · exact transfer hview.symm

theorem deferredCompletion_resolveDeferredPositionValue_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (hconsistent : context.ValuesConsistent)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (completion : Coordinate → HashOutput) :
    DeferredCompletion table result.toDeferredContext completion ↔
      DeferredCompletion table context completion ∧
        completion (.position position) = result.output := by
  constructor
  · intro hcompletion
    exact ⟨hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent
      hconsistent position result hresult,
      hcompletion.eq_positionValue position result.output
        (resolveDeferredPositionValue_resolves position context result hresult)⟩
  · rintro ⟨hcompletion, htarget⟩
    have hstateValues := resolveDeferredPositionValue_preserves_state_values
      position context result hresult
    have hpending := resolveDeferredPositionValue_pending position context result hresult
    have hinstalled := resolveDeferredPositionValue_installs position context result hresult
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      apply hcompletion.1 coordinate output
      rw [← hstateValues]
      exact hvalue
    · intro other output hvalue
      by_cases heq : other = position
      · subst other
        have houtput : output = result.output := by
          rw [hinstalled] at hvalue
          exact Option.some.inj hvalue.symm
        rw [houtput]
        exact htarget
      · apply hcompletion.2.1 other output
        rw [← resolveDeferredPositionValue_preserves_other position other context result heq
          hresult]
        exact hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      have haway : (coordinate, candidate) ∈
          context.state.pendingAway (.position position) := by
        rw [← hpending]
        exact hmember
      exact (Finset.mem_filter.1 haway).1

theorem resolveDeferredPositionValue_positionValue_eq_update
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.toDeferredContext.positionValue =
      Function.update context.positionValue position (some result.output) := by
  funext other
  by_cases heq : other = position
  · subst other
    rw [resolveDeferredPositionValue_resolves position context result hresult]
    simp
  · have hstateValues := resolveDeferredPositionValue_preserves_state_values
      position context result hresult
    have hdeferred := resolveDeferredPositionValue_preserves_other
      position other context result heq hresult
    unfold DeferredContext.positionValue
    rw [hstateValues]
    cases hstate : context.state.values (.position other) with
    | some output => simp [hstate, Function.update_of_ne heq]
    | none => simp [hstate, hdeferred, Function.update_of_ne heq]

set_option maxRecDepth 100000 in
theorem finalizationViewEq_of_deferredCompletion_iff
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftStarts : StartTableAgrees left.state table)
    (hrightStarts : StartTableAgrees right.state table)
    (hvalueEq : resolvedCompletionValue table left =
      resolvedCompletionValue table right)
    (hleftCompletable : DeferredCompletable table left)
    (hcompletion : ∀ completion,
      DeferredCompletion table left completion ↔
        DeferredCompletion table right completion) :
    FinalizationViewEq table left right := by
  rcases hleftCompletable with ⟨completion, hcompletionLeft⟩
  have hcompletionRight := (hcompletion completion).mp hcompletionLeft
  refine ⟨hleftValid.valuesConsistent, hrightValid.valuesConsistent,
    hleftStarts, hrightStarts, hvalueEq, ?_, ?_, ?_⟩
  · intro coordinate output hvalue hhit
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    apply hcompletionLeft.2.2.1 coordinate (truncateHash output) hhit
    rw [hcompletionLeft.eq_resolvedCompletionValue coordinate output hvalue]
  · intro coordinate output hvalue hhit
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    apply hcompletionRight.2.2.1 coordinate (truncateHash output) hhit
    rw [hcompletionRight.eq_resolvedCompletionValue coordinate output hvalue]
  · intro coordinate hvalue
    apply pendingAt_eq_of_deferredCompletion_iff_of_value_none
      ⟨completion, hcompletionLeft⟩ hcompletion coordinate hvalue
    rw [← hvalueEq]
    exact hvalue

theorem finalizationViewEq_resolveDeferredPositionValue
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (position : Position) (leftResult rightResult : DeferredResolution)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left)
    (hleftResult : some leftResult ∈ support
      (resolveDeferredPositionValue position left))
    (hrightResult : some rightResult ∈ support
      (resolveDeferredPositionValue position right))
    (houtput : leftResult.output = rightResult.output) :
    FinalizationViewEq table leftResult.toDeferredContext
      rightResult.toDeferredContext := by
  have hleftResultValid := hleftValid.of_resolveDeferredPositionValue
    position leftResult hleftResult
  have hrightResultValid := hrightValid.of_resolveDeferredPositionValue
    position rightResult hrightResult
  have hleftStateValues := resolveDeferredPositionValue_preserves_state_values
    position left leftResult hleftResult
  have hrightStateValues := resolveDeferredPositionValue_preserves_state_values
    position right rightResult hrightResult
  have hleftPositionValues :=
    resolveDeferredPositionValue_positionValue_eq_update position left leftResult hleftResult
  have hrightPositionValues :=
    resolveDeferredPositionValue_positionValue_eq_update position right rightResult hrightResult
  have hvalueEq : resolvedCompletionValue table leftResult.toDeferredContext =
      resolvedCompletionValue table rightResult.toDeferredContext := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position other =>
        change leftResult.toDeferredContext.positionValue other =
          rightResult.toDeferredContext.positionValue other
        rw [hleftPositionValues, hrightPositionValues]
        by_cases heq : other = position
        · subst other
          simp [houtput]
        · simp only [Function.update_of_ne heq]
          exact congrFun hview.valueEq (.position other)
  have hcompletion : ∀ completion,
      DeferredCompletion table leftResult.toDeferredContext completion ↔
        DeferredCompletion table rightResult.toDeferredContext completion := by
    intro completion
    rw [deferredCompletion_resolveDeferredPositionValue_iff position leftResult
        hview.leftConsistent hleftResult completion,
      deferredCompletion_resolveDeferredPositionValue_iff position rightResult
        hview.rightConsistent hrightResult completion,
      ← houtput, hview.deferredCompletion_iff completion]
  apply finalizationViewEq_of_deferredCompletion_iff
  · exact hleftResultValid
  · exact hrightResultValid
  · exact hview.leftStarts.of_state_values_eq hleftStateValues
  · exact hview.rightStarts.of_state_values_eq hrightStateValues
  · exact hvalueEq
  · exact hleftCompletable.of_resolveDeferredPositionValue hleftValid position leftResult
      hleftResult
  · exact hcompletion

def FinalizationResolutionEq (table : OtsSecretIndex → HashOutput) :
    Option DeferredResolution → Option DeferredResolution → Prop
  | none, none => True
  | some left, some right =>
      left.output = right.output ∧
        FinalizationViewEq table left.toDeferredContext right.toDeferredContext ∧
        left.toDeferredContext.Valid ∧ right.toDeferredContext.Valid ∧
        DeferredCompletable table left.toDeferredContext
  | _, _ => False

theorem deferredCompletion_resolveDeferredChainStart_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (index : OtsSecretIndex) (result : DeferredResolution)
    (hstarts : StartTableAgrees context.state table)
    (hresult : resolveDeferredChainStart table index context = some result)
    (completion : Coordinate → HashOutput) :
    DeferredCompletion table result.toDeferredContext completion ↔
      DeferredCompletion table context completion := by
  constructor
  · intro hcompletion
    exact hcompletion.of_resolveDeferredChainStart hstarts index result hresult
  · intro hcompletion
    have hstateValues := resolveDeferredChainStart_state_values_eq table index context result hresult
    have hdeferredValues :=
      resolveDeferredChainStart_deferred_values_eq table index context result hresult
    have hpending := resolveDeferredChainStart_pending_eq table index context result hresult
    refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
    · intro coordinate output hvalue
      apply hcompletion.1 coordinate output
      rw [← hstateValues]
      exact hvalue
    · intro position output hvalue
      apply hcompletion.2.1 position output
      rw [← hdeferredValues]
      exact hvalue
    · intro coordinate candidate hmember
      apply hcompletion.2.2.1 coordinate candidate
      rw [hpending] at hmember
      exact (Finset.mem_filter.1 hmember).1

theorem finalizationViewEq_resolveDeferredChainStart
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (index : OtsSecretIndex) (leftResult rightResult : DeferredResolution)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left)
    (hleftResult : resolveDeferredChainStart table index left = some leftResult)
    (hrightResult : resolveDeferredChainStart table index right = some rightResult) :
    FinalizationViewEq table leftResult.toDeferredContext
      rightResult.toDeferredContext := by
  have hleftStateValues := resolveDeferredChainStart_state_values_eq table index left leftResult
    hleftResult
  have hrightStateValues := resolveDeferredChainStart_state_values_eq table index right rightResult
    hrightResult
  have hleftPositionValues := resolveDeferredChainStart_positionValue_eq table index left
    leftResult hleftResult
  have hrightPositionValues := resolveDeferredChainStart_positionValue_eq table index right
    rightResult hrightResult
  have hvalueEq : resolvedCompletionValue table leftResult.toDeferredContext =
      resolvedCompletionValue table rightResult.toDeferredContext := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position =>
        change leftResult.toDeferredContext.positionValue position =
          rightResult.toDeferredContext.positionValue position
        rw [hleftPositionValues, hrightPositionValues]
        exact congrFun hview.valueEq (.position position)
  have hcompletion : ∀ completion,
      DeferredCompletion table leftResult.toDeferredContext completion ↔
        DeferredCompletion table rightResult.toDeferredContext completion := by
    intro completion
    rw [deferredCompletion_resolveDeferredChainStart_iff index leftResult
        hview.leftStarts hleftResult completion,
      deferredCompletion_resolveDeferredChainStart_iff index rightResult
        hview.rightStarts hrightResult completion,
      hview.deferredCompletion_iff completion]
  apply finalizationViewEq_of_deferredCompletion_iff
  · exact hleftValid.of_resolveDeferredChainStart table index leftResult hleftResult
  · exact hrightValid.of_resolveDeferredChainStart table index rightResult hrightResult
  · exact hview.leftStarts.of_state_values_eq hleftStateValues
  · exact hview.rightStarts.of_state_values_eq hrightStateValues
  · exact hvalueEq
  · exact hleftCompletable.of_resolveDeferredChainStart index leftResult hleftResult
  · exact hcompletion

theorem relTriple_resolveDeferredChainStart_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (pure (resolveDeferredChainStart table index left) :
        ProbComp (Option DeferredResolution))
      (pure (resolveDeferredChainStart table index right) :
        ProbComp (Option DeferredResolution))
      (FinalizationResolutionEq table) := by
  have hrightCompletable : DeferredCompletable table right := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  have hleftClean := hleftCompletable.not_hitAt_chainStart index
  have hrightClean := hrightCompletable.not_hitAt_chainStart index
  let leftResult : DeferredResolution :=
    ⟨{ state := left.state.clearPending index.coordinate, values := left.values }, table index⟩
  let rightResult : DeferredResolution :=
    ⟨{ state := right.state.clearPending index.coordinate, values := right.values }, table index⟩
  have hleftResult : resolveDeferredChainStart table index left = some leftResult := by
    cases hstate : left.state.values index.coordinate with
    | some output =>
        have houtput := hview.leftStarts index output hstate
        simp [resolveDeferredChainStart, hstate, houtput, hleftClean, leftResult]
    | none => simp [resolveDeferredChainStart, hstate, hleftClean, leftResult]
  have hrightResult : resolveDeferredChainStart table index right = some rightResult := by
    cases hstate : right.state.values index.coordinate with
    | some output =>
        have houtput := hview.rightStarts index output hstate
        simp [resolveDeferredChainStart, hstate, houtput, hrightClean, rightResult]
    | none => simp [resolveDeferredChainStart, hstate, hrightClean, rightResult]
  rw [hleftResult, hrightResult]
  apply relTriple_pure_pure
  exact ⟨rfl, finalizationViewEq_resolveDeferredChainStart index leftResult rightResult hview
      hleftValid hrightValid hleftCompletable hleftResult hrightResult,
    hleftValid.of_resolveDeferredChainStart table index leftResult hleftResult,
    hrightValid.of_resolveDeferredChainStart table index rightResult hrightResult,
    hleftCompletable.of_resolveDeferredChainStart index leftResult hleftResult⟩

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredPositionValue_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (resolveDeferredPositionValue position left)
      (resolveDeferredPositionValue position right)
      (FinalizationResolutionEq table) := by
  have hpositionValue : left.positionValue position = right.positionValue position := by
    exact congrFun hview.valueEq (.position position)
  have relate (leftResult rightResult : DeferredResolution)
      (hleftResult : some leftResult ∈ support
        (resolveDeferredPositionValue position left))
      (hrightResult : some rightResult ∈ support
        (resolveDeferredPositionValue position right))
      (houtput : leftResult.output = rightResult.output) :
      FinalizationResolutionEq table (some leftResult) (some rightResult) := by
    exact ⟨houtput,
      finalizationViewEq_resolveDeferredPositionValue position leftResult rightResult hview
        hleftValid hrightValid hleftCompletable hleftResult hrightResult houtput,
      hleftValid.of_resolveDeferredPositionValue position leftResult hleftResult,
      hrightValid.of_resolveDeferredPositionValue position rightResult hrightResult,
      hleftCompletable.of_resolveDeferredPositionValue hleftValid position leftResult
        hleftResult⟩
  cases hleftState : left.state.values (.position position) with
  | some output =>
      have hleftValue : left.positionValue position = some output := by
        simp [DeferredContext.positionValue, hleftState]
      have hrightValue : right.positionValue position = some output := by
        rw [← hpositionValue]
        exact hleftValue
      have hleftClean : ¬left.state.hitAt (.position position) output :=
        hview.leftClean (.position position) output hleftValue
      rw [resolveDeferredPositionValue_of_state_value position left output hleftState,
        if_neg hleftClean]
      cases hrightState : right.state.values (.position position) with
      | some rightOutput =>
          have hrightOutput : rightOutput = output := by
            simpa [DeferredContext.positionValue, hrightState] using hrightValue
          subst rightOutput
          have hrightClean : ¬right.state.hitAt (.position position) output :=
            hview.rightClean (.position position) output hrightValue
          rw [resolveDeferredPositionValue_of_state_value position right output hrightState,
            if_neg hrightClean]
          apply relTriple_pure_pure
          apply relate <;>
            simp [resolveDeferredPositionValue, hleftState, hrightState, hleftClean,
              hrightClean]
      | none =>
          cases hrightDeferred : right.values position with
          | some rightOutput =>
              have hrightOutput : rightOutput = output := by
                simpa [DeferredContext.positionValue, hrightState, hrightDeferred] using
                  hrightValue
              subst rightOutput
              have hrightClean : ¬right.state.hitAt (.position position) output :=
                hview.rightClean (.position position) output hrightValue
              rw [resolveDeferredPositionValue_of_deferred_value position right output
                hrightState hrightDeferred, if_neg hrightClean]
              apply relTriple_pure_pure
              apply relate <;>
                simp [resolveDeferredPositionValue, hleftState, hrightState, hrightDeferred,
                  hleftClean, hrightClean]
          | none =>
              simp [DeferredContext.positionValue, hrightState, hrightDeferred] at hrightValue
  | none =>
      cases hleftDeferred : left.values position with
      | some output =>
          have hleftValue : left.positionValue position = some output := by
            simp [DeferredContext.positionValue, hleftState, hleftDeferred]
          have hrightValue : right.positionValue position = some output := by
            rw [← hpositionValue]
            exact hleftValue
          have hleftClean : ¬left.state.hitAt (.position position) output :=
            hview.leftClean (.position position) output hleftValue
          rw [resolveDeferredPositionValue_of_deferred_value position left output hleftState
            hleftDeferred, if_neg hleftClean]
          cases hrightState : right.state.values (.position position) with
          | some rightOutput =>
              have hrightOutput : rightOutput = output := by
                simpa [DeferredContext.positionValue, hrightState] using hrightValue
              subst rightOutput
              have hrightClean : ¬right.state.hitAt (.position position) output :=
                hview.rightClean (.position position) output hrightValue
              rw [resolveDeferredPositionValue_of_state_value position right output hrightState,
                if_neg hrightClean]
              apply relTriple_pure_pure
              apply relate <;>
                simp [resolveDeferredPositionValue, hleftState, hleftDeferred, hrightState,
                  hleftClean, hrightClean]
          | none =>
              cases hrightDeferred : right.values position with
              | some rightOutput =>
                  have hrightOutput : rightOutput = output := by
                    simpa [DeferredContext.positionValue, hrightState, hrightDeferred] using
                      hrightValue
                  subst rightOutput
                  have hrightClean : ¬right.state.hitAt (.position position) output :=
                    hview.rightClean (.position position) output hrightValue
                  rw [resolveDeferredPositionValue_of_deferred_value position right output
                    hrightState hrightDeferred, if_neg hrightClean]
                  apply relTriple_pure_pure
                  apply relate <;>
                    simp [resolveDeferredPositionValue, hleftState, hleftDeferred, hrightState,
                      hrightDeferred, hleftClean, hrightClean]
              | none =>
                  simp [DeferredContext.positionValue, hrightState, hrightDeferred] at hrightValue
      | none =>
          have hleftValue : left.positionValue position = none := by
            simp [DeferredContext.positionValue, hleftState, hleftDeferred]
          have hrightValue : right.positionValue position = none := by
            rw [← hpositionValue]
            exact hleftValue
          have hrightState : right.state.values (.position position) = none := by
            cases hstate : right.state.values (.position position) with
            | none => rfl
            | some output => simp [DeferredContext.positionValue, hstate] at hrightValue
          have hrightDeferred : right.values position = none := by
            simpa [DeferredContext.positionValue, hrightState] using hrightValue
          rw [resolveDeferredPositionValue_fresh position left hleftState hleftDeferred,
            resolveDeferredPositionValue_fresh position right hrightState hrightDeferred]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          have hpending := hview.pendingEq (.position position) hleftValue
          have hhit : left.state.hitAt (.position position) leftOutput ↔
              right.state.hitAt (.position position) leftOutput := by
            unfold LazyRevealProbe.State.hitAt
            rw [hpending]
          by_cases hleftHit : left.state.hitAt (.position position) leftOutput
          · rw [if_pos hleftHit, if_pos (hhit.mp hleftHit)]
            exact relTriple_pure_pure trivial
          · have hrightHit : ¬right.state.hitAt (.position position) leftOutput :=
              mt hhit.mpr hleftHit
            rw [if_neg hleftHit, if_neg hrightHit]
            apply relTriple_pure_pure
            apply relate
            · rw [resolveDeferredPositionValue_fresh position left hleftState hleftDeferred,
                mem_support_bind_iff]
              exact ⟨leftOutput, by simp [LazyRevealProbe.sampleHashOutput], by simp [hleftHit]⟩
            · rw [resolveDeferredPositionValue_fresh position right hrightState hrightDeferred,
                mem_support_bind_iff]
              exact ⟨leftOutput, by simp [LazyRevealProbe.sampleHashOutput], by simp [hrightHit]⟩
            · rfl

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredChainPrefix_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps left right,
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps left)
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps right)
        (FinalizationResolutionEq table)
  | 0, hsteps, left, right, hview, hleftValid, hrightValid, hleftCompletable => by
      simp only [resolveDeferredChainPrefix]
      exact relTriple_resolveDeferredChainStart_of_finalizationViewEq table
        ⟨lay, tree, leafIdx, chainIdx⟩ left right hview hleftValid hrightValid
          hleftCompletable
  | steps + 1, hsteps, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [resolveDeferredChainPrefix, resolveDeferredChainPrefix]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix_of_finalizationViewEq table lay tree leafIdx
          chainIdx steps (by omega) left right hview hleftValid hrightValid hleftCompletable)
      intro leftPrevious rightPrevious hprevious
      cases leftPrevious with
      | none =>
          cases rightPrevious <;> simp [FinalizationResolutionEq] at hprevious ⊢
      | some leftPrevious =>
          cases rightPrevious with
          | none => simp [FinalizationResolutionEq] at hprevious
          | some rightPrevious =>
              exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
                (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
                leftPrevious.toDeferredContext rightPrevious.toDeferredContext hprevious.2.1
                hprevious.2.2.1 hprevious.2.2.2.1 hprevious.2.2.2.2

def FinalizationContextEq (table : OtsSecretIndex → HashOutput) :
    Option DeferredContext → Option DeferredContext → Prop
  | none, none => True
  | some left, some right =>
      FinalizationViewEq table left right ∧ left.Valid ∧ right.Valid ∧
        DeferredCompletable table left
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredChains_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains left right,
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (resolveDeferredChains table lay tree leafIdx chains left)
        (resolveDeferredChains table lay tree leafIdx chains right)
        (FinalizationContextEq table)
  | [], left, right, hview, hleftValid, hrightValid, hleftCompletable => by
      simp only [resolveDeferredChains]
      exact relTriple_pure_pure ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  | chainIdx :: remaining, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [resolveDeferredChains, resolveDeferredChains]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix_of_finalizationViewEq table lay tree leafIdx
          chainIdx (chainLength - 1) (by omega) left right hview hleftValid hrightValid
          hleftCompletable)
      intro leftResolved rightResolved hresolved
      cases leftResolved with
      | none =>
          cases rightResolved with
          | none => exact relTriple_pure_pure trivial
          | some rightResolved => simp [FinalizationResolutionEq] at hresolved
      | some leftResolved =>
          cases rightResolved with
          | none => simp [FinalizationResolutionEq] at hresolved
          | some rightResolved =>
              exact relTriple_resolveDeferredChains_of_finalizationViewEq table lay tree leafIdx
                remaining leftResolved.toDeferredContext rightResolved.toDeferredContext
                hresolved.2.1 hresolved.2.2.1 hresolved.2.2.2.1 hresolved.2.2.2.2

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredOtsLeaf_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (left right : DeferredContext)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (resolveDeferredOtsLeaf table lay tree leafIdx left)
      (resolveDeferredOtsLeaf table lay tree leafIdx right)
      (FinalizationResolutionEq table) := by
  rw [resolveDeferredOtsLeaf, resolveDeferredOtsLeaf]
  apply relTriple_bind
    (relTriple_resolveDeferredChains_of_finalizationViewEq table lay tree leafIdx
      (List.ofFn fun chainIdx : ChainIndex => chainIdx) left right hview hleftValid
      hrightValid hleftCompletable)
  intro leftChains rightChains hchains
  cases leftChains with
  | none =>
      cases rightChains with
      | none => exact relTriple_pure_pure trivial
      | some rightChains => simp [FinalizationContextEq] at hchains
  | some leftChains =>
      cases rightChains with
      | none => simp [FinalizationContextEq] at hchains
      | some rightChains =>
          exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
            (.leaf lay tree leafIdx) leftChains rightChains hchains.1 hchains.2.1
            hchains.2.2.1 hchains.2.2.2

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredTreeNode_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel left right,
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel left)
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel right)
        (FinalizationResolutionEq table)
  | 0, nodeIdx, hlevel, left, right, hview, hleftValid, hrightValid,
      hleftCompletable =>
      relTriple_resolveDeferredOtsLeaf_of_finalizationViewEq table lay tree
        (leafOfNat nodeIdx) left right hview hleftValid hrightValid hleftCompletable
  | level + 1, nodeIdx, hlevel, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [resolveDeferredTreeNode, resolveDeferredTreeNode]
      apply relTriple_bind
        (relTriple_resolveDeferredTreeNode_of_finalizationViewEq table lay tree level
          (2 * nodeIdx) (by omega) left right hview hleftValid hrightValid hleftCompletable)
      intro leftNode rightNode hleftNode
      cases leftNode with
      | none =>
          cases rightNode <;> simp [FinalizationResolutionEq] at hleftNode ⊢
      | some leftNode =>
          cases rightNode with
          | none => simp [FinalizationResolutionEq] at hleftNode
          | some rightNode =>
              apply relTriple_bind
                (relTriple_resolveDeferredTreeNode_of_finalizationViewEq table lay tree level
                  (2 * nodeIdx + 1) (by omega) leftNode.toDeferredContext
                  rightNode.toDeferredContext hleftNode.2.1 hleftNode.2.2.1
                  hleftNode.2.2.2.1 hleftNode.2.2.2.2)
              intro leftSibling rightSibling hsibling
              cases leftSibling with
              | none =>
                  cases rightSibling <;> simp [FinalizationResolutionEq] at hsibling ⊢
              | some leftSibling =>
                  cases rightSibling with
                  | none => simp [FinalizationResolutionEq] at hsibling
                  | some rightSibling =>
                      exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
                        (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                        leftSibling.toDeferredContext rightSibling.toDeferredContext
                        hsibling.2.1 hsibling.2.2.1 hsibling.2.2.2.1
                        hsibling.2.2.2.2

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredPosition_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (resolveDeferredPosition table position left)
      (resolveDeferredPosition table position right)
      (FinalizationResolutionEq table) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact relTriple_resolveDeferredChainPrefix_of_finalizationViewEq table lay tree leafIdx
        chainIdx (step.val + 1) (by have := step.isLt; omega) left right hview hleftValid
        hrightValid hleftCompletable
  | leaf lay tree leafIdx =>
      exact relTriple_resolveDeferredOtsLeaf_of_finalizationViewEq table lay tree leafIdx
        left right hview hleftValid hrightValid hleftCompletable
  | node lay tree level nodeIdx =>
      exact relTriple_resolveDeferredTreeNode_of_finalizationViewEq table lay tree
        (level.val + 1) nodeIdx (by have := level.isLt; omega) left right hview hleftValid
        hrightValid hleftCompletable
  | ftsLeaf index tree leafIdx =>
      exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
        (.ftsLeaf index tree leafIdx) left right hview hleftValid hrightValid hleftCompletable
  | ftsNode index tree level nodeIdx =>
      exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
        (.ftsNode index tree level nodeIdx) left right hview hleftValid hrightValid
        hleftCompletable
  | ftsRoots index =>
      exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
        (.ftsRoots index) left right hview hleftValid hrightValid hleftCompletable

theorem relTriple_resolveDeferredReveal_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (resolveDeferredReveal table position left)
      (resolveDeferredReveal table position right)
      (FinalizationResolutionEq table) := by
  classical
  unfold resolveDeferredReveal
  by_cases hresolvable : ResolvableOtsPosition position
  · rw [if_pos hresolvable, if_pos hresolvable]
    exact relTriple_resolveDeferredPosition_of_finalizationViewEq table position left right
      hview hleftValid hrightValid hleftCompletable
  · rw [if_neg hresolvable, if_neg hresolvable]
    exact relTriple_resolveDeferredPositionValue_of_finalizationViewEq table position left right
      hview hleftValid hrightValid hleftCompletable

theorem finalizeResolvedCoordinates_cons_chainStart_of_clean
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (remaining : List Coordinate) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hclean : ¬context.state.hitAt index.coordinate (table index)) :
    finalizeResolvedCoordinates (index.coordinate :: remaining) context table =
      finalizeResolvedCoordinates remaining
        (context.completeResolved index.coordinate (table index)) table := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  simp only [OtsSecretIndex.coordinate] at hclean ⊢
  cases hstate : context.state.values (.chainStart lay tree leafIdx chainIdx) with
  | some output =>
      have houtput := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hstate
      subst output
      rw [finalizeResolvedCoordinates_cons_of_state_value
        (.chainStart lay tree leafIdx chainIdx) remaining context table
        (table ⟨lay, tree, leafIdx, chainIdx⟩) hstate]
      congr 1
      rcases context with ⟨state, values⟩
      simp only [DeferredContext.completeResolved]
      congr 1
      rcases state with ⟨pending, stateValues, revealed, ensured⟩
      simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.complete,
        LazyRevealProbe.State.pendingAway] at hstate ⊢
      congr 1
      funext coordinate
      by_cases heq : coordinate = .chainStart lay tree leafIdx chainIdx
      · subst coordinate
        simpa using hstate
      · simp [Function.update_of_ne heq]
  | none =>
      rw [finalizeResolvedCoordinates]
      simp only [hstate]
      rw [resolveDeferredChainStart_of_missing table ⟨lay, tree, leafIdx, chainIdx⟩ context
        hstate]
      simp [OtsSecretIndex.coordinate, hclean, DeferredContext.completeResolved,
        clearPending_complete_self]

theorem finalizeResolvedCoordinates_cons_position_of_known_clean
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (remaining : List Coordinate) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (output : HashOutput)
    (hvalue : context.positionValue position = some output)
    (hclean : ¬context.state.hitAt (.position position) output) :
    finalizeResolvedCoordinates (.position position :: remaining) context table =
      finalizeResolvedCoordinates remaining
        (context.completeResolved (.position position) output) table := by
  cases hstate : context.state.values (.position position) with
  | some cached =>
      have hcached : cached = output := by
        unfold DeferredContext.positionValue at hvalue
        rw [hstate] at hvalue
        exact Option.some.inj hvalue
      subst cached
      have hdeferred := hconsistent position output hstate
      rw [finalizeResolvedCoordinates_cons_of_state_value (.position position) remaining
        context table output hstate]
      congr 1
      rcases context with ⟨state, values⟩
      change values position = some output at hdeferred
      simp only [DeferredContext.completeResolved]
      congr 1
      · rcases state with ⟨pending, stateValues, revealed, ensured⟩
        simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.complete,
          LazyRevealProbe.State.pendingAway] at hstate ⊢
        congr 1
        funext coordinate
        by_cases heq : coordinate = Coordinate.position position
        · subst coordinate
          simpa using hstate
        · simp [Function.update_of_ne heq]
      · funext other
        by_cases heq : other = position
        · subst other
          simp [DeferredStructuralValues.install, hdeferred]
        · simp [DeferredStructuralValues.install, heq]
  | none =>
      have hdeferred : context.values position = some output := by
        unfold DeferredContext.positionValue at hvalue
        simpa [hstate] using hvalue
      rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position remaining
        context table output hstate hdeferred, if_neg hclean]
      congr 1
      rcases context with ⟨state, values⟩
      change values position = some output at hdeferred
      simp only [DeferredContext.completeResolved]
      congr 1
      funext other
      by_cases heq : other = position
      · subst other
        simp [DeferredStructuralValues.install, hdeferred]
      · simp [DeferredStructuralValues.install, heq]

theorem finalizeResolvedCoordinates_cons_position_of_unknown
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (remaining : List Coordinate) (context : DeferredContext)
    (hvalue : context.positionValue position = none) :
    finalizeResolvedCoordinates (.position position :: remaining) context table = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then
        pure none
      else (finalizeResolvedCoordinates remaining
        (context.completeResolved (.position position) output) table)) := by
  have hstate : context.state.values (.position position) = none := by
    unfold DeferredContext.positionValue at hvalue
    cases hstate : context.state.values (.position position) with
    | none => rfl
    | some output => simp [hstate] at hvalue
  have hdeferred : context.values position = none := by
    unfold DeferredContext.positionValue at hvalue
    simpa [hstate] using hvalue
  rw [finalizeResolvedCoordinates_cons_position_fresh position remaining context table hstate
    hdeferred]
  rfl

@[simp] theorem resolvedCompletionValue_completeResolved_position_self
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (output : HashOutput) :
    resolvedCompletionValue table
        (context.completeResolved (.position position) output) (.position position) =
      some output := by
  simp [resolvedCompletionValue, DeferredContext.positionValue,
    DeferredContext.completeResolved, LazyRevealProbe.State.complete,
    DeferredStructuralValues.install]

@[simp] theorem resolvedCompletionValue_completeResolved_start_self
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (index : OtsSecretIndex) :
    resolvedCompletionValue table
        (context.completeResolved index.coordinate (table index)) index.coordinate =
      some (table index) := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  rfl

theorem not_hitAt_complete_self
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) :
    ¬(state.complete coordinate output).hitAt coordinate output := by
  unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
  simp [LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway]

theorem resolvedCompletionValue_completeResolved_of_ne
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate other : Coordinate) (output : HashOutput) (hne : other ≠ coordinate) :
    resolvedCompletionValue table (context.completeResolved coordinate output) other =
      resolvedCompletionValue table context other := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      cases other with
      | chainStart => rfl
      | position position =>
          simp [resolvedCompletionValue, DeferredContext.positionValue,
            DeferredContext.completeResolved, values_complete_of_ne, hne]
  | position position =>
      cases other with
      | chainStart => rfl
      | position other =>
          have hposition : other ≠ position := by
            intro heq
            subst other
            exact hne rfl
          simp [resolvedCompletionValue, DeferredContext.positionValue,
            DeferredContext.completeResolved, DeferredStructuralValues.install,
            values_complete_of_ne, hne, hposition]

theorem DeferredContext.ValuesConsistent.completeResolved
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (coordinate : Coordinate) (output : HashOutput) :
    (context.completeResolved coordinate output).ValuesConsistent := by
  intro position cached hvalue
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      apply hconsistent position cached
      have hne : Coordinate.position position ≠
          Coordinate.chainStart lay tree leafIdx chainIdx := by simp
      simpa only [DeferredContext.completeResolved,
        values_complete_of_ne context.state
          (.chainStart lay tree leafIdx chainIdx) (.position position) output hne] using hvalue
  | position completed =>
      by_cases heq : position = completed
      · subst position
        have hcached : cached = output := by
          simpa [DeferredContext.completeResolved, LazyRevealProbe.State.complete] using
            hvalue.symm
        subst cached
        simp [DeferredContext.completeResolved, DeferredStructuralValues.install]
      · have hcoordinate : Coordinate.position position ≠ Coordinate.position completed := by
          simpa using heq
        have horiginal : context.state.values (.position position) = some cached := by
          simpa [DeferredContext.completeResolved, LazyRevealProbe.State.complete,
            Function.update_of_ne hcoordinate] using hvalue
        simpa [DeferredContext.completeResolved, DeferredStructuralValues.install, heq] using
          hconsistent position cached horiginal

set_option maxRecDepth 100000 in
theorem FinalizationViewEq.completeStart
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (index : OtsSecretIndex) :
    FinalizationViewEq table
      (left.completeResolved index.coordinate (table index))
      (right.completeResolved index.coordinate (table index)) := by
  have hleftState : (left.completeResolved index.coordinate (table index)).state =
      left.state.complete index.coordinate (table index) := by
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    rfl
  have hrightState : (right.completeResolved index.coordinate (table index)).state =
      right.state.complete index.coordinate (table index) := by
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    rfl
  refine ⟨hview.leftConsistent.completeResolved index.coordinate (table index),
    hview.rightConsistent.completeResolved index.coordinate (table index),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hleftState]
    exact hview.leftStarts.complete_start index
  · rw [hrightState]
    exact hview.rightStarts.complete_start index
  · funext other
    by_cases heq : other = index.coordinate
    · subst other
      simp
    · rw [resolvedCompletionValue_completeResolved_of_ne table left index.coordinate other
          (table index) heq,
        resolvedCompletionValue_completeResolved_of_ne table right index.coordinate other
          (table index) heq,
        hview.valueEq]
  · intro other otherOutput hvalue
    by_cases heq : other = index.coordinate
    · subst other
      have houtput : otherOutput = table index := by
        simpa using hvalue.symm
      subst otherOutput
      rw [hleftState]
      exact not_hitAt_complete_self left.state index.coordinate (table index)
    · have horiginal : resolvedCompletionValue table left other = some otherOutput := by
        rw [← resolvedCompletionValue_completeResolved_of_ne table left index.coordinate other
          (table index) heq]
        exact hvalue
      have hclean := hview.leftClean other otherOutput horiginal
      rw [hleftState]
      exact (hitAt_complete_of_ne left.state index.coordinate other (table index) otherOutput
        heq).not.mpr hclean
  · intro other otherOutput hvalue
    by_cases heq : other = index.coordinate
    · subst other
      have houtput : otherOutput = table index := by
        simpa using hvalue.symm
      subst otherOutput
      rw [hrightState]
      exact not_hitAt_complete_self right.state index.coordinate (table index)
    · have horiginal : resolvedCompletionValue table right other = some otherOutput := by
        rw [← resolvedCompletionValue_completeResolved_of_ne table right index.coordinate other
          (table index) heq]
        exact hvalue
      have hclean := hview.rightClean other otherOutput horiginal
      rw [hrightState]
      exact (hitAt_complete_of_ne right.state index.coordinate other (table index) otherOutput
        heq).not.mpr hclean
  · intro other hvalue
    have hne : other ≠ index.coordinate := by
      intro heq
      subst other
      simp at hvalue
    have horiginal : resolvedCompletionValue table left other = none := by
      rw [← resolvedCompletionValue_completeResolved_of_ne table left index.coordinate other
        (table index) hne]
      exact hvalue
    have hpending := hview.pendingEq other horiginal
    rw [hleftState, hrightState]
    rw [pendingAt_complete_of_ne left.state index.coordinate other (table index) hne,
      pendingAt_complete_of_ne right.state index.coordinate other (table index) hne,
      hpending]

set_option maxRecDepth 100000 in
theorem FinalizationViewEq.completePosition
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (position : Position) (output : HashOutput) :
    FinalizationViewEq table
      (left.completeResolved (.position position) output)
      (right.completeResolved (.position position) output) := by
  have hleftState : (left.completeResolved (.position position) output).state =
      left.state.complete (.position position) output := rfl
  have hrightState : (right.completeResolved (.position position) output).state =
      right.state.complete (.position position) output := rfl
  refine ⟨hview.leftConsistent.completeResolved (.position position) output,
    hview.rightConsistent.completeResolved (.position position) output,
    hview.leftStarts.complete_position position output,
    hview.rightStarts.complete_position position output, ?_, ?_, ?_, ?_⟩
  · funext other
    by_cases heq : other = .position position
    · subst other
      simp
    · rw [resolvedCompletionValue_completeResolved_of_ne table left (.position position)
          other output heq,
        resolvedCompletionValue_completeResolved_of_ne table right (.position position)
          other output heq,
        hview.valueEq]
  · intro other otherOutput hvalue
    by_cases heq : other = .position position
    · subst other
      have houtput : otherOutput = output := by simpa using hvalue.symm
      subst otherOutput
      rw [hleftState]
      exact not_hitAt_complete_self left.state (.position position) output
    · have horiginal : resolvedCompletionValue table left other = some otherOutput := by
        rw [← resolvedCompletionValue_completeResolved_of_ne table left (.position position)
          other output heq]
        exact hvalue
      have hclean := hview.leftClean other otherOutput horiginal
      rw [hleftState]
      exact (hitAt_complete_of_ne left.state (.position position) other output otherOutput
        heq).not.mpr hclean
  · intro other otherOutput hvalue
    by_cases heq : other = .position position
    · subst other
      have houtput : otherOutput = output := by simpa using hvalue.symm
      subst otherOutput
      rw [hrightState]
      exact not_hitAt_complete_self right.state (.position position) output
    · have horiginal : resolvedCompletionValue table right other = some otherOutput := by
        rw [← resolvedCompletionValue_completeResolved_of_ne table right (.position position)
          other output heq]
        exact hvalue
      have hclean := hview.rightClean other otherOutput horiginal
      rw [hrightState]
      exact (hitAt_complete_of_ne right.state (.position position) other output otherOutput
        heq).not.mpr hclean
  · intro other hvalue
    have hne : other ≠ .position position := by
      intro heq
      subst other
      simp at hvalue
    have horiginal : resolvedCompletionValue table left other = none := by
      rw [← resolvedCompletionValue_completeResolved_of_ne table left (.position position)
        other output hne]
      exact hvalue
    have hpending := hview.pendingEq other horiginal
    rw [hleftState, hrightState]
    rw [pendingAt_complete_of_ne left.state (.position position) other output hne,
      pendingAt_complete_of_ne right.state (.position position) other output hne,
      hpending]

set_option maxRecDepth 100000 in
theorem evalDist_map_isNone_finalizeResolvedCoordinates_congr
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates left table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates right table) := by
  induction coordinates generalizing left right with
  | nil => simp [finalizeResolvedCoordinates]
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
          change evalDist (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) left table) =
            evalDist (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) right table)
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
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              have hpending := hview.pendingEq (.position position) hvalue
              have hhit : left.state.hitAt (.position position) output ↔
                  right.state.hitAt (.position position) output := by
                unfold LazyRevealProbe.State.hitAt
                rw [hpending]
              by_cases hleftHit : left.state.hitAt (.position position) output
              · rw [if_pos hleftHit, if_pos (hhit.mp hleftHit)]
              · rw [if_neg hleftHit, if_neg (mt hhit.mpr hleftHit)]
                exact ih (left.completeResolved (.position position) output)
                  (right.completeResolved (.position position) output)
                  (hview.completePosition position output)

set_option maxRecDepth 100000 in
theorem finalizationViewEq_materializeResolvedReveal
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context))
    (hcompletable : DeferredCompletable table
      (materializeResolvedPosition context position result)) :
    FinalizationViewEq table
      (materializeResolvedPosition context position result)
      result.toDeferredContext := by
  have hresultValid := hvalid.of_resolveDeferredReveal table position result hresult
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context result
    hresult
  have hresolved := resolveDeferredReveal_resolves table position context result hresult
  have hvalueEq : resolvedCompletionValue table
      (materializeResolvedPosition context position result) =
      resolvedCompletionValue table result.toDeferredContext := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position other =>
        exact congrFun
          (materializeResolvedPosition_positionValue_eq context position result hstateValues
            hresolved) other
  apply finalizationViewEq_of_deferredCompletion_iff
  · exact hvalid.materializeResolvedPosition_of position result hresultValid hstateValues
      hresolved
  · exact hresultValid
  · simpa [materializeResolvedPosition] using
      hstarts.materialize_position position result.output
  · exact hstarts.of_state_values_eq hstateValues
  · exact hvalueEq
  · exact hcompletable
  · intro completion
    exact deferredCompletion_materializeResolvedReveal_iff position result hvalid hstarts hresult

theorem finalizationViewEq_materializeResolvedChainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (index : OtsSecretIndex) (result : DeferredResolution)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hresult : resolveDeferredChainStart table index context = some result)
    (hcompletable : DeferredCompletable table
      (materializeResolvedChainStart context index result)) :
    FinalizationViewEq table
      (materializeResolvedChainStart context index result)
      result.toDeferredContext := by
  have hresultValid := hvalid.of_resolveDeferredChainStart table index result hresult
  have hstateValues := resolveDeferredChainStart_state_values_eq table index context result hresult
  have hdeferredValues :=
    resolveDeferredChainStart_deferred_values_eq table index context result hresult
  have hpending := resolveDeferredChainStart_pending_eq table index context result hresult
  have houtput := resolveDeferredChainStart_output_of_agrees table index context result hstarts
    hresult
  have hleftValid : (materializeResolvedChainStart context index result).Valid := by
    rw [materializeResolvedChainStart, hdeferredValues]
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx result.output
  have hvalueEq : resolvedCompletionValue table
      (materializeResolvedChainStart context index result) =
      resolvedCompletionValue table result.toDeferredContext := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position =>
        change (materializeResolvedChainStart context index result).positionValue position =
          result.toDeferredContext.positionValue position
        rw [materializeResolvedChainStart_positionValue_eq table index context result hresult,
          resolveDeferredChainStart_positionValue_eq table index context result hresult]
  apply finalizationViewEq_of_deferredCompletion_iff
  · exact hleftValid
  · exact hresultValid
  · simpa [materializeResolvedChainStart, houtput] using
      hstarts.materialize_start index
  · exact hstarts.of_state_values_eq hstateValues
  · exact hvalueEq
  · exact hcompletable
  · intro completion
    exact deferredCompletion_materializeResolvedChainStart_iff index result hstarts houtput
      hstateValues hdeferredValues hpending

theorem evalDist_map_isNone_finalizeResolvedCoordinates_materializeResolvedReveal
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (coordinates : List Coordinate)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context))
    (hcompletable : DeferredCompletable table
      (materializeResolvedPosition context position result)) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates
        (materializeResolvedPosition context position result) table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates
        result.toDeferredContext table) :=
  evalDist_map_isNone_finalizeResolvedCoordinates_congr table coordinates
    (materializeResolvedPosition context position result) result.toDeferredContext
    (finalizationViewEq_materializeResolvedReveal position result hvalid hstarts hresult
      hcompletable)

set_option maxRecDepth 100000 in
theorem evalDist_map_isNone_finalizeResolvedCoordinates_completeResolved_of_not_mem
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate)
    (context : DeferredContext) (coordinate : Coordinate) (output : HashOutput)
    (hnotMem : coordinate ∉ coordinates) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates
        (context.completeResolved coordinate output) table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates context table) := by
  induction coordinates generalizing context with
  | nil => simp [finalizeResolvedCoordinates]
  | cons head remaining ih =>
      have hne : head ≠ coordinate := by
        intro heq
        subst head
        exact hnotMem (by simp)
      have htail : coordinate ∉ remaining := by
        intro hmem
        exact hnotMem (List.mem_cons_of_mem head hmem)
      have hstateComplete :
          (context.completeResolved coordinate output).state.values head =
            context.state.values head := by
        have hstate : (context.completeResolved coordinate output).state =
            context.state.complete coordinate output := by cases coordinate <;> rfl
        rw [hstate, values_complete_of_ne context.state coordinate head output hne]
      cases hstate : context.state.values head with
      | some headOutput =>
          have hstateLeft :
              (context.completeResolved coordinate output).state.values head =
                some headOutput := by rw [hstateComplete, hstate]
          rw [finalizeResolvedCoordinates_cons_of_state_value head remaining
                (context.completeResolved coordinate output) table headOutput hstateLeft,
            finalizeResolvedCoordinates_cons_of_state_value head remaining context table
              headOutput hstate]
          have hcommute := clearPending_completeResolved_comm context head coordinate output
          rw [← hcommute]
          exact ih { context with state := context.state.clearPending head } htail
      | none =>
          have hstateLeft :
              (context.completeResolved coordinate output).state.values head = none := by
            rw [hstateComplete, hstate]
          rw [finalizeResolvedCoordinates_cons_of_missing head remaining
                (context.completeResolved coordinate output) table hstateLeft,
            finalizeResolvedCoordinates_cons_of_missing head remaining context table hstate]
          rw [resolvedCompletionOutput_completeResolved_of_ne coordinate head context table output
            hne]
          simp only [map_eq_bind_pure_comp, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro headOutput
          have hleftState : (context.completeResolved coordinate output).state =
              context.state.complete coordinate output := by cases coordinate <;> rfl
          have hhit :
              (context.completeResolved coordinate output).state.hitAt head headOutput ↔
                context.state.hitAt head headOutput := by
            rw [hleftState]
            exact hitAt_complete_of_ne context.state coordinate head output headOutput hne
          by_cases hheadHit : context.state.hitAt head headOutput
          · rw [if_pos (hhit.mpr hheadHit), if_pos hheadHit]
          · rw [if_neg (mt hhit.mp hheadHit), if_neg hheadHit]
            rw [DeferredContext.completeResolved_comm context coordinate head output headOutput
              hne.symm]
            exact ih (context.completeResolved head headOutput) htail

set_option maxRecDepth 100000 in
theorem evalDist_map_isNone_finalizeResolvedCoordinates_cons_irrelevant
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hnotMem : coordinate ∉ coordinates)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ output, resolvedCompletionValue table context coordinate = some output →
      ¬context.state.hitAt coordinate output)
    (hunknown : resolvedCompletionValue table context coordinate = none →
      context.state.pendingAt coordinate = ∅) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates
        (coordinate :: coordinates) context table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates context table) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      have hcoordinate : index.coordinate =
          Coordinate.chainStart lay tree leafIdx chainIdx := rfl
      have hmiss : ¬context.state.hitAt index.coordinate (table index) :=
        hclean (table index) (by simp [index, resolvedCompletionValue])
      change evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (index.coordinate :: coordinates) context table) = _
      rw [finalizeResolvedCoordinates_cons_chainStart_of_clean table index coordinates context
        hstarts hmiss]
      exact evalDist_map_isNone_finalizeResolvedCoordinates_completeResolved_of_not_mem
        table coordinates context index.coordinate (table index) (by simpa [hcoordinate] using hnotMem)
  | position position =>
      cases hvalue : resolvedCompletionValue table context (.position position) with
      | some output =>
          have hmiss := hclean output hvalue
          rw [finalizeResolvedCoordinates_cons_position_of_known_clean table position coordinates
            context hconsistent output (by simpa [resolvedCompletionValue] using hvalue) hmiss]
          exact evalDist_map_isNone_finalizeResolvedCoordinates_completeResolved_of_not_mem
            table coordinates context (.position position) output hnotMem
      | none =>
          have hpending := hunknown hvalue
          rw [finalizeResolvedCoordinates_cons_position_of_unknown table position coordinates
            context (by simpa [resolvedCompletionValue] using hvalue)]
          simp only [map_eq_bind_pure_comp, bind_assoc]
          calc
            evalDist (LazyRevealProbe.sampleHashOutput >>= fun output =>
                (if context.state.hitAt (.position position) output then pure none
                else finalizeResolvedCoordinates coordinates
                  (context.completeResolved (.position position) output) table) >>=
                  fun result => pure result.isNone) =
                evalDist (LazyRevealProbe.sampleHashOutput >>= fun _ =>
                  Option.isNone <$> finalizeResolvedCoordinates coordinates context table) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              have hmiss : ¬context.state.hitAt (.position position) output := by
                unfold LazyRevealProbe.State.hitAt
                rw [hpending]
                simp
              rw [if_neg hmiss]
              exact evalDist_map_isNone_finalizeResolvedCoordinates_completeResolved_of_not_mem
                table coordinates context (.position position) output hnotMem
            _ = evalDist (Option.isNone <$>
                finalizeResolvedCoordinates coordinates context table) :=
              OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                LazyRevealProbe.sampleHashOutput (by simp [LazyRevealProbe.sampleHashOutput])
                (Option.isNone <$> finalizeResolvedCoordinates coordinates context table)

set_option maxRecDepth 100000 in
theorem evalDist_map_isNone_finalizeResolvedCoordinates_append_irrelevant
    (table : OtsSecretIndex → HashOutput) (extra coordinates : List Coordinate)
    (context : DeferredContext) (hextraNodup : extra.Nodup)
    (hdisjoint : ∀ coordinate, coordinate ∈ extra → coordinate ∉ coordinates)
    (hcovered : PendingCovered coordinates context)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates
        (extra ++ coordinates) context table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates context table) := by
  induction extra with
  | nil => rfl
  | cons coordinate remaining ih =>
      obtain ⟨hnotRemaining, hremainingNodup⟩ := List.nodup_cons.mp hextraNodup
      have hnotCoordinates := hdisjoint coordinate (by simp)
      have hnotAppend : coordinate ∉ remaining ++ coordinates := by
        simp [hnotRemaining, hnotCoordinates]
      have hunknown : resolvedCompletionValue table context coordinate = none →
          context.state.pendingAt coordinate = ∅ := by
        intro _hvalue
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨candidate, hcandidate⟩
        have hentry : (coordinate, candidate) ∈ context.state.pending :=
          (LazyRevealProbe.State.mem_pendingAt_iff context.state coordinate candidate).mp
            hcandidate
        exact hnotCoordinates (hcovered (coordinate, candidate) hentry)
      calc
        evalDist (Option.isNone <$> finalizeResolvedCoordinates
            ((coordinate :: remaining) ++ coordinates) context table) =
            evalDist (Option.isNone <$> finalizeResolvedCoordinates
              (remaining ++ coordinates) context table) :=
          evalDist_map_isNone_finalizeResolvedCoordinates_cons_irrelevant table coordinate
            (remaining ++ coordinates) context hnotAppend hconsistent hstarts
            (hclean coordinate) hunknown
        _ = evalDist (Option.isNone <$>
            finalizeResolvedCoordinates coordinates context table) :=
          ih hremainingNodup (fun other hmem =>
            hdisjoint other (List.mem_cons_of_mem coordinate hmem))

set_option maxRecDepth 100000 in
theorem evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered
    (table : OtsSecretIndex → HashOutput)
    (leftCoordinates rightCoordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewEq table left right)
    (hleftNodup : leftCoordinates.Nodup) (hrightNodup : rightCoordinates.Nodup)
    (hleftCovered : PendingCovered leftCoordinates left)
    (hrightCovered : PendingCovered rightCoordinates right) :
    evalDist (Option.isNone <$>
        finalizeResolvedCoordinates leftCoordinates left table) =
      evalDist (Option.isNone <$>
        finalizeResolvedCoordinates rightCoordinates right table) := by
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
  have hsameAug := evalDist_map_isNone_finalizeResolvedCoordinates_congr table
    (leftExtra ++ leftBase) left right hview
  have hpermAug :
      evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (leftExtra ++ leftBase) right table) =
        evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (rightExtra ++ rightBase) right table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm haugPerm right table]
  exact hleftPermDist.symm.trans (hleftAug.symm.trans
    (hsameAug.trans (hpermAug.trans (hrightAug.trans hrightPermDist))))

theorem evalDist_map_isNone_finalizeResolvedCoordinates_materializeResolvedReveal_dynamic
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context))
    (hcompletable : DeferredCompletable table
      (materializeResolvedPosition context position result)) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates
        (materializeResolvedPosition context position result).state.coordinates.toList
        (materializeResolvedPosition context position result) table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates
        result.state.coordinates.toList result.toDeferredContext table) := by
  apply evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table
    (materializeResolvedPosition context position result).state.coordinates.toList
    result.state.coordinates.toList
    (materializeResolvedPosition context position result) result.toDeferredContext
    (finalizationViewEq_materializeResolvedReveal position result hvalid hstarts hresult
      hcompletable)
  · exact Finset.nodup_toList _
  · exact Finset.nodup_toList _
  · exact pendingCovered_coordinates_toList _
  · exact pendingCovered_coordinates_toList _

noncomputable def selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (result : ResolvedRunResult DeferredLayerStore) :
    ProbComp (Option (ResolvedRunResult DeferredLayerStore)) := do
  let selected ← runResolvedFromTable result.context result.remaining table
    ((maskedSignLayer parameter ftsSecret index lay).run result.value.cache)
  match selected with
  | none => pure none
  | some selected => pure (some ⟨selected.context, selected.remaining,
      { selected := Function.update result.value.selected lay selected.value.1
        resolved := result.value.resolved
        cache := selected.value.2 }, table⟩)

noncomputable def resolveDeferredLayer
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (result : ResolvedRunResult DeferredLayerStore) :
    ProbComp (Option (ResolvedRunResult DeferredLayerStore)) :=
  match result.value.selected lay with
  | none => pure (some ⟨result.context, result.remaining,
      { result.value with resolved := Function.update result.value.resolved lay none },
      table⟩)
  | some (counter, encoding) => do
      let resolved ← resolveDeferredLayerValues table index lay encoding result.context
      match resolved with
      | none => pure none
      | some (context, values) =>
          let part : LayerPart := (counter, values.1, values.2)
          pure (some ⟨context, result.remaining,
            { result.value with
              resolved := Function.update result.value.resolved lay (some part) }, table⟩)

def mapResolvedLayerSchedule
    (table : OtsSecretIndex → HashOutput)
    (resolvedLay selectedLay : Layer) (counter : Counter)
    (store : DeferredLayerStore) :
    Option (ResolvedRunResult (DeferredLayerValues × DeferredLayerSelection)) →
      Option (ResolvedRunResult DeferredLayerStore)
  | none => none
  | some result => some ⟨result.context, result.remaining,
      { selected := Function.update store.selected selectedLay result.value.2.1
        resolved := Function.update store.resolved resolvedLay
          (some (counter, result.value.1.1, result.value.1.2))
        cache := result.value.2.2 }, table⟩

theorem evalDist_resolveDeferredLayer_then_selectDeferredLayer_eq
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (result : ResolvedRunResult DeferredLayerStore) :
    evalDist (resolveDeferredLayer table index resolvedLay result >>= fun resolved =>
      match resolved with
      | none => pure none
      | some resolved => selectDeferredLayer parameter table ftsSecret index selectedLay resolved) =
    evalDist (selectDeferredLayer parameter table ftsSecret index selectedLay result >>=
      fun selected =>
      match selected with
      | none => pure none
      | some selected => resolveDeferredLayer table index resolvedLay selected) := by
  classical
  have hne : selectedLay ≠ resolvedLay := by
    intro heq
    subst selectedLay
    omega
  have hne' : resolvedLay ≠ selectedLay := Ne.symm hne
  cases hselected : result.value.selected resolvedLay with
  | none =>
      rw [resolveDeferredLayer]
      simp only [hselected, pure_bind]
      unfold selectDeferredLayer
      simp only [bind_assoc]
      apply congrArg evalDist
      apply bind_congr
      intro selectedOption
      cases selectedOption with
      | none => rfl
      | some selected =>
          simp only [pure_bind]
          rw [resolveDeferredLayer]
          simp [Function.update, hne', hselected]
  | some selected =>
      rcases selected with ⟨counter, encoding⟩
      have hleft :
          (resolveDeferredLayer table index resolvedLay result >>= fun resolved =>
            match resolved with
            | none => pure none
            | some resolved =>
                selectDeferredLayer parameter table ftsSecret index selectedLay resolved) =
          (mapResolvedLayerSchedule table resolvedLay selectedLay counter result.value <$>
            resolveThenSelectLayer parameter table ftsSecret index resolvedLay selectedLay
              encoding result.context result.remaining result.value.cache) := by
        unfold resolveDeferredLayer resolveThenSelectLayer selectDeferredLayer
        simp only [hselected, map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro resolvedOption
        cases resolvedOption with
        | none => simp [mapResolvedLayerSchedule]
        | some resolved =>
            rcases resolved with ⟨resolvedContext, values⟩
            simp only [pure_bind]
            rw [bind_assoc]
            apply bind_congr
            intro selectedOption
            cases selectedOption <;> rfl
      have hright :
          (selectDeferredLayer parameter table ftsSecret index selectedLay result >>=
            fun selected =>
            match selected with
            | none => pure none
            | some selected => resolveDeferredLayer table index resolvedLay selected) =
          (mapResolvedLayerSchedule table resolvedLay selectedLay counter result.value <$>
            selectThenResolveLayer parameter table ftsSecret index resolvedLay selectedLay
              encoding result.context result.remaining result.value.cache) := by
        unfold selectDeferredLayer selectThenResolveLayer
        simp only [map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro selectedOption
        cases selectedOption with
        | none => simp [mapResolvedLayerSchedule]
        | some selected =>
            simp only [pure_bind]
            rw [resolveDeferredLayer]
            simp [Function.update, hne', hselected]
            apply bind_congr
            intro resolvedOption
            cases resolvedOption <;> rfl
      rw [hleft, hright]
      rw [evalDist_map, evalDist_map,
        evalDist_resolveThenSelectLayer_eq_selectThenResolveLayer_of_lt parameter table
          ftsSecret index resolvedLay selectedLay hlt encoding result.context result.remaining
          result.value.cache]

inductive DeferredLayerOperation where
  | select (lay : Layer)
  | resolve (lay : Layer)

noncomputable def runDeferredLayerOperation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (operation : DeferredLayerOperation) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult DeferredLayerStore))
  | none => pure none
  | some result =>
      match operation with
      | .select lay => selectDeferredLayer parameter table ftsSecret index lay result
      | .resolve lay => resolveDeferredLayer table index lay result

noncomputable def runDeferredLayerSchedule
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    List DeferredLayerOperation → Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (ResolvedRunResult DeferredLayerStore))
  | [], input => pure input
  | operation :: remaining, input => do
      let result ← runDeferredLayerOperation parameter table ftsSecret index operation input
      runDeferredLayerSchedule parameter table ftsSecret index remaining result

@[simp] theorem runDeferredLayerSchedule_none
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ operations : List DeferredLayerOperation,
      runDeferredLayerSchedule parameter table ftsSecret index operations none = pure none
  | [] => rfl
  | _ :: operations => by
      simp [runDeferredLayerSchedule, runDeferredLayerOperation,
        runDeferredLayerSchedule_none parameter table ftsSecret index operations]

theorem evalDist_runDeferredLayerSchedule_adjacent
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (remaining : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (.resolve resolvedLay :: .select selectedLay :: remaining) input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (.select selectedLay :: .resolve resolvedLay :: remaining) input) := by
  cases input with
  | none => simp [runDeferredLayerSchedule, runDeferredLayerOperation]
  | some result =>
      simp only [runDeferredLayerSchedule, runDeferredLayerOperation]
      simp only [← bind_assoc]
      have hswap := evalDist_resolveDeferredLayer_then_selectDeferredLayer_eq parameter table
        ftsSecret index resolvedLay selectedLay hlt result
      rw [evalDist_bind, evalDist_bind] at hswap
      rw [evalDist_bind, evalDist_bind, hswap]
      rw [evalDist_bind]
      rw [evalDist_bind]

theorem evalDist_runDeferredLayerSchedule_swap
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (resolvedLay selectedLay : Layer) (hlt : resolvedLay.val < selectedLay.val)
    (before remaining : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (before ++ .resolve resolvedLay :: .select selectedLay :: remaining) input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      (before ++ .select selectedLay :: .resolve resolvedLay :: remaining) input) := by
  induction before generalizing input with
  | nil =>
      simpa using evalDist_runDeferredLayerSchedule_adjacent parameter table ftsSecret index
        resolvedLay selectedLay hlt remaining input
  | cons operation before ih =>
      simp only [List.cons_append, runDeferredLayerSchedule]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro result
      exact ih result

theorem runDeferredLayerSchedule_append
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (before after : List DeferredLayerOperation)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    runDeferredLayerSchedule parameter table ftsSecret index (before ++ after) input =
      (runDeferredLayerSchedule parameter table ftsSecret index before input >>= fun result =>
        runDeferredLayerSchedule parameter table ftsSecret index after result) := by
  induction before generalizing input with
  | nil => simp [runDeferredLayerSchedule]
  | cons operation before ih =>
      simp only [List.cons_append, runDeferredLayerSchedule, bind_assoc]
      apply bind_congr
      intro result
      exact ih result

def chronologicalLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .resolve topLayer,
    .select middleLayer, .resolve middleLayer,
    .select bottomLayer, .resolve bottomLayer]

def deferredLayerSchedule : List DeferredLayerOperation :=
  [.select topLayer, .select middleLayer, .select bottomLayer,
    .resolve topLayer, .resolve middleLayer, .resolve bottomLayer]

def deferredLayerSelections : List DeferredLayerOperation :=
  [topLayer, middleLayer, bottomLayer].map DeferredLayerOperation.select

def deferredLayerResolutions : List DeferredLayerOperation :=
  [topLayer, middleLayer, bottomLayer].map DeferredLayerOperation.resolve

theorem deferredLayerSchedule_eq_append :
    deferredLayerSchedule = deferredLayerSelections ++ deferredLayerResolutions := by
  simp [deferredLayerSchedule, deferredLayerSelections, deferredLayerResolutions]

theorem evalDist_chronologicalLayerSchedule_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (input : Option (ResolvedRunResult DeferredLayerStore)) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      chronologicalLayerSchedule input) =
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
      deferredLayerSchedule input) := by
  have h01 : topLayer.val < middleLayer.val := by decide
  have h12 : middleLayer.val < bottomLayer.val := by decide
  have h02 : topLayer.val < bottomLayer.val := by decide
  calc
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        [.select topLayer, .select middleLayer, .resolve topLayer,
          .resolve middleLayer, .select bottomLayer, .resolve bottomLayer] input) := by
      simpa [chronologicalLayerSchedule] using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index topLayer
          middleLayer h01 [.select topLayer]
          [.resolve middleLayer, .select bottomLayer, .resolve bottomLayer] input
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        [.select topLayer, .select middleLayer, .resolve topLayer,
          .select bottomLayer, .resolve middleLayer, .resolve bottomLayer] input) := by
      simpa using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index middleLayer
          bottomLayer h12 [.select topLayer, .select middleLayer, .resolve topLayer]
          [.resolve bottomLayer] input
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule input) := by
      simpa [deferredLayerSchedule] using
        evalDist_runDeferredLayerSchedule_swap parameter table ftsSecret index topLayer
          bottomLayer h02 [.select topLayer, .select middleLayer]
          [.resolve middleLayer, .resolve bottomLayer] input

theorem evalDist_chronologicalLayerSchedule_bind_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (input : Option (ResolvedRunResult DeferredLayerStore))
    (next : Option (ResolvedRunResult DeferredLayerStore) → ProbComp α) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        chronologicalLayerSchedule input >>= next) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule input >>= next) := by
  rw [evalDist_bind, evalDist_bind,
    evalDist_chronologicalLayerSchedule_eq_deferred parameter table ftsSecret index input]

noncomputable def finalizeDeferredLayerSchedule
    (coordinates : List Coordinate) :
    Option (ResolvedRunResult DeferredLayerStore) →
      ProbComp (Option (LazyRevealProbe.State Coordinate))
  | none => pure none
  | some result => projectDeferredState <$>
      finalizeResolvedCoordinates coordinates result.context result.table

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerSchedule_then_finalize
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table → result.context.Valid →
      PendingCovered coordinates result.context →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.resolve) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates result.context result.table)
  | [], result, htable, hvalid, hcovered => by
      simp [runDeferredLayerSchedule, finalizeDeferredLayerSchedule]
  | lay :: layers, result, htable, hvalid, hcovered => by
      subst table
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation]
      rw [resolveDeferredLayer]
      cases hselected : result.value.selected lay with
      | none =>
          simp only [pure_bind]
          exact evalDist_resolveDeferredLayerSchedule_then_finalize parameter result.table ftsSecret
            index coordinates layers
            { result with
              value :=
                { result.value with
                  resolved := Function.update result.value.resolved lay none } }
            rfl hvalid hcovered
      | some selected =>
          rcases selected with ⟨counter, encoding⟩
          simp only [bind_assoc]
          calc
            _ = evalDist (resolveDeferredLayerValues result.table index lay encoding result.context >>=
                fun resolved =>
                  match resolved with
                  | none => pure none
                  | some (finalContext, _) => projectDeferredState <$>
                      finalizeResolvedCoordinates coordinates finalContext result.table) := by
              apply evalDist_bind_congr
              intro resolved hresolved
              cases resolved with
              | none =>
                  simp [finalizeDeferredLayerSchedule]
              | some resolved =>
                  rcases resolved with ⟨finalContext, values⟩
                  simp only [pure_bind]
                  have hfinalValid := hvalid.of_resolveDeferredLayerValues result.table index lay
                    encoding finalContext values hresolved
                  have hfinalCovered := hcovered.of_resolveDeferredLayerValues result.table index lay
                    encoding finalContext values hresolved
                  simpa only using
                    (evalDist_resolveDeferredLayerSchedule_then_finalize parameter result.table
                      ftsSecret index coordinates layers
                      { context := finalContext
                        remaining := result.remaining
                        value :=
                          { result.value with
                            resolved := Function.update result.value.resolved lay
                              (some (counter, values.1, values.2)) }
                        table := result.table }
                      rfl hfinalValid hfinalCovered)
            _ = _ := evalDist_map_resolveDeferredLayerValues_then_finalize result.table index lay
              encoding coordinates result.context hvalid hcovered

theorem valid_pendingCovered_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (coordinates : List Coordinate)
    (result output : ResolvedRunResult DeferredLayerStore)
    (hvalid : result.context.Valid) (hcovered : PendingCovered coordinates result.context)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay result)) :
    output.table = table ∧ output.context.Valid ∧
      PendingCovered coordinates output.context := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, hselected, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      have hinvariants := valid_pendingCovered_of_mem_runResolvedFromTable_of_probeFree
        ((maskedSignLayer parameter ftsSecret index lay).run result.value.cache)
        result.context result.remaining table selected coordinates
        (maskedSignLayer_probeFree parameter ftsSecret index lay result.value.cache)
        hvalid hcovered hselected
      exact ⟨rfl, hinvariants⟩

theorem valid_pendingCovered_of_mem_runDeferredLayerSelections
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) :
    ∀ (layers : List Layer) (result output : ResolvedRunResult DeferredLayerStore),
      result.table = table → result.context.Valid →
      PendingCovered coordinates result.context →
      some output ∈ support
        (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.select) (some result)) →
      output.table = table ∧ output.context.Valid ∧
        PendingCovered coordinates output.context
  | [], result, output, htable, hvalid, hcovered, houtput => by
      simp [runDeferredLayerSchedule] at houtput
      subst output
      exact ⟨htable, hvalid, hcovered⟩
  | lay :: layers, result, output, htable, hvalid, hcovered, houtput => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation,
        mem_support_bind_iff] at houtput
      obtain ⟨selectedOption, hselected, htail⟩ := houtput
      cases selectedOption with
      | none => simp at htail
      | some selected =>
          have hinvariants := valid_pendingCovered_of_mem_selectDeferredLayer parameter table
            ftsSecret index lay coordinates result selected hvalid hcovered hselected
          exact valid_pendingCovered_of_mem_runDeferredLayerSelections parameter table ftsSecret
            index coordinates layers selected output hinvariants.1 hinvariants.2.1
            hinvariants.2.2 htail

set_option maxRecDepth 100000 in
theorem evalDist_selectThenResolveDeferredLayerSchedule_then_finalize
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) (layers : List Layer)
    (result : ResolvedRunResult DeferredLayerStore)
    (htable : result.table = table) (hvalid : result.context.Valid)
    (hcovered : PendingCovered coordinates result.context) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        ((layers.map DeferredLayerOperation.select) ++
          layers.map DeferredLayerOperation.resolve) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        (layers.map DeferredLayerOperation.select) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) := by
  rw [runDeferredLayerSchedule_append, bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none => simp [finalizeDeferredLayerSchedule]
  | some selected =>
      have hinvariants : selected.table = table ∧ selected.context.Valid ∧
          PendingCovered coordinates selected.context :=
        valid_pendingCovered_of_mem_runDeferredLayerSelections parameter table ftsSecret index
          coordinates layers result selected htable hvalid hcovered hselected
      exact evalDist_resolveDeferredLayerSchedule_then_finalize parameter table ftsSecret index
        coordinates layers selected hinvariants.1
        hinvariants.2.1 hinvariants.2.2

set_option maxRecDepth 100000 in
theorem evalDist_deferredLayerSchedule_then_finalize_eq_selections
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) (result : ResolvedRunResult DeferredLayerStore)
    (htable : result.table = table) (hvalid : result.context.Valid)
    (hcovered : PendingCovered coordinates result.context) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSchedule (some result) >>= finalizeDeferredLayerSchedule coordinates) =
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSelections (some result) >>= finalizeDeferredLayerSchedule coordinates) := by
  rw [deferredLayerSchedule_eq_append]
  exact evalDist_selectThenResolveDeferredLayerSchedule_then_finalize parameter table ftsSecret
    index coordinates [topLayer, middleLayer, bottomLayer] result htable hvalid hcovered

noncomputable def runResolvedSequenceFin
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult ((Fin n → α) × SplitHashCache))) :=
  match n with
  | 0 => pure (some ⟨context, fuel, (Fin.elim0, cache), table⟩)
  | n + 1 => do
      let head ← runResolvedFromTable context fuel table ((computation 0).run cache)
      match head with
      | none => pure none
      | some head => do
          let tail ← runResolvedSequenceFin
            (fun position : Fin n => computation position.succ)
            head.context head.remaining table head.value.2
          match tail with
          | none => pure none
          | some tail => pure (some ⟨tail.context, tail.remaining,
              (Fin.cases head.value.1 tail.value.1, tail.value.2), table⟩)

set_option maxRecDepth 100000 in
theorem evalDist_runResolvedSequenceFin_eq
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runResolvedSequenceFin computation context fuel table cache) =
      evalDist (runResolvedFromTable context fuel table
        ((sequenceFin computation).run cache)) := by
  induction n generalizing context fuel cache with
  | zero => simp [runResolvedSequenceFin, sequenceFin, runResolvedFromTable]
  | succ n ih =>
      rw [runResolvedSequenceFin, sequenceFin, StateT.run_bind,
        runResolvedFromTable_bind]
      apply evalDist_bind_congr
      intro headOption hhead
      cases headOption with
      | none => simp
      | some head =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable
            ((computation 0).run cache) context fuel table head hconsistent hstarts hhead
          simp only
          rw [hcore.1, StateT.run_bind, runResolvedFromTable_bind]
          simp only [StateT.run_pure]
          rw [evalDist_bind, ih (fun position : Fin n => computation position.succ)
            head.context head.remaining head.value.2 hcore.2.1 hcore.2.2, ← evalDist_bind]
          apply evalDist_bind_congr
          intro tailOption htail
          cases tailOption with
          | none => simp
          | some tail =>
              have htailCore := resolvedCore_of_mem_runResolvedFromTable
                ((sequenceFin fun position : Fin n => computation position.succ).run
                  head.value.2)
                head.context head.remaining table tail hcore.2.1 hcore.2.2 htail
              simp [runResolvedFromTable, htailCore.1]

noncomputable def finalizeResolvedRunState
    (coordinates : List Coordinate) :
    Option (ResolvedRunResult α) →
      ProbComp (Option (LazyRevealProbe.State Coordinate))
  | none => pure none
  | some result => projectDeferredState <$>
      finalizeResolvedCoordinates coordinates result.context result.table

noncomputable def finalizeResolvedRunStateFromTable
    (coordinates : List Coordinate) (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult α) →
      ProbComp (Option (LazyRevealProbe.State Coordinate))
  | none => pure none
  | some result => projectDeferredState <$>
      finalizeResolvedCoordinates coordinates result.context table

noncomputable def runResolvedLayerList
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    List Layer → DeferredContext → Nat → SplitHashCache →
      ProbComp (Option (ResolvedRunResult SplitHashCache))
  | [], context, fuel, cache => pure (some ⟨context, fuel, cache, table⟩)
  | lay :: layers, context, fuel, cache => do
      let selected ← runResolvedFromTable context fuel table
        ((maskedSignLayer parameter ftsSecret index lay).run cache)
      match selected with
      | none => pure none
      | some selected =>
          runResolvedLayerList parameter table ftsSecret index layers selected.context
            selected.remaining selected.value.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredLayerSelections_then_finalize_eq_list
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (coordinates : List Coordinate) :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.select) (some result) >>=
        finalizeDeferredLayerSchedule coordinates) =
      evalDist (runResolvedLayerList parameter table ftsSecret index layers
          result.context result.remaining result.value.cache >>=
        finalizeResolvedRunStateFromTable coordinates table)
  | [], result, htable => by
      simp only [List.map_nil, runDeferredLayerSchedule, pure_bind,
        finalizeDeferredLayerSchedule, runResolvedLayerList,
        finalizeResolvedRunStateFromTable]
      rw [htable]
  | lay :: layers, result, _htable => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation,
        selectDeferredLayer, runResolvedLayerList, bind_assoc]
      apply evalDist_bind_congr
      intro selectedOption _hselected
      cases selectedOption with
      | none => simp [finalizeDeferredLayerSchedule, finalizeResolvedRunStateFromTable]
      | some selected =>
          simp only [pure_bind]
          exact evalDist_runDeferredLayerSelections_then_finalize_eq_list parameter table
            ftsSecret index coordinates layers
            { context := selected.context
              remaining := selected.remaining
              value :=
                { selected := Function.update result.value.selected lay selected.value.1
                  resolved := result.value.resolved
                  cache := selected.value.2 }
              table := table } rfl

noncomputable def runResolvedSequenceFinDiscard
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult SplitHashCache)) :=
  match n with
  | 0 => pure (some ⟨context, fuel, cache, table⟩)
  | n + 1 => do
      let head ← runResolvedFromTable context fuel table ((computation 0).run cache)
      match head with
      | none => pure none
      | some head =>
          runResolvedSequenceFinDiscard
            (fun position : Fin n => computation position.succ)
            head.context head.remaining table head.value.2

set_option maxRecDepth 100000 in
theorem evalDist_runResolvedSequenceFin_then_finalize_eq_discard
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinates : List Coordinate) :
    evalDist (runResolvedSequenceFin computation context fuel table cache >>=
        finalizeResolvedRunStateFromTable coordinates table) =
      evalDist (runResolvedSequenceFinDiscard computation context fuel table cache >>=
        finalizeResolvedRunStateFromTable coordinates table) := by
  induction n generalizing context fuel cache with
  | zero => simp [runResolvedSequenceFin, runResolvedSequenceFinDiscard,
      finalizeResolvedRunStateFromTable]
  | succ n ih =>
      simp only [runResolvedSequenceFin, runResolvedSequenceFinDiscard, bind_assoc]
      apply evalDist_bind_congr
      intro headOption _hhead
      cases headOption with
      | none => simp [finalizeResolvedRunStateFromTable]
      | some head =>
          calc
            _ = evalDist (runResolvedSequenceFin
                (fun position : Fin n => computation position.succ)
                head.context head.remaining table head.value.2 >>=
              finalizeResolvedRunStateFromTable coordinates table) := by
                simp only [bind_assoc]
                apply evalDist_bind_congr
                intro tailOption _htail
                cases tailOption <;>
                  simp [finalizeResolvedRunStateFromTable]
            _ = _ := ih (fun position : Fin n => computation position.succ)
              head.context head.remaining head.value.2

set_option maxRecDepth 100000 in
theorem runResolvedSequenceFinDiscard_layers_eq_list
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runResolvedSequenceFinDiscard
        (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
        context fuel table cache =
      runResolvedLayerList parameter table ftsSecret index
        [topLayer, middleLayer, bottomLayer] context fuel cache := by
  simp [runResolvedSequenceFinDiscard, runResolvedLayerList, numLayers,
    topLayer, middleLayer, bottomLayer]
  apply bind_congr
  intro topOption
  cases topOption with
  | none => rfl
  | some top =>
      apply bind_congr
      intro middleOption
      cases middleOption with
      | none => rfl
      | some middle =>
          apply bind_congr
          intro bottomOption
          cases bottomOption <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_deferredLayerSelections_then_finalize_eq_sequenceFin
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (coordinates : List Coordinate) (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        deferredLayerSelections
        (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
      finalizeDeferredLayerSchedule coordinates) =
      evalDist (runResolvedFromTable context fuel table
          ((sequenceFin fun lay : Layer =>
            maskedSignLayer parameter ftsSecret index lay).run cache) >>=
        finalizeResolvedRunStateFromTable coordinates table) := by
  calc
    _ = evalDist (runResolvedLayerList parameter table ftsSecret index
          [topLayer, middleLayer, bottomLayer] context fuel cache >>=
        finalizeResolvedRunStateFromTable coordinates table) :=
      evalDist_runDeferredLayerSelections_then_finalize_eq_list parameter table ftsSecret
        index coordinates [topLayer, middleLayer, bottomLayer]
        ⟨context, fuel, emptyDeferredLayerStore cache, table⟩ rfl
    _ = evalDist (runResolvedSequenceFinDiscard
          (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
          context fuel table cache >>= finalizeResolvedRunStateFromTable coordinates table) := by
      rw [runResolvedSequenceFinDiscard_layers_eq_list]
    _ = evalDist (runResolvedSequenceFin
          (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
          context fuel table cache >>= finalizeResolvedRunStateFromTable coordinates table) :=
      (evalDist_runResolvedSequenceFin_then_finalize_eq_discard
        (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
        context fuel table cache coordinates).symm
    _ = _ := by
      rw [evalDist_bind,
        evalDist_runResolvedSequenceFin_eq
          (fun lay : Layer => maskedSignLayer parameter ftsSecret index lay)
          context fuel table cache hconsistent hstarts, ← evalDist_bind]

set_option maxRecDepth 100000 in
theorem evalDist_chronologicalLayerSchedule_then_finalize_eq_sequenceFin
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (coordinates : List Coordinate) (hvalid : context.Valid)
    (hcovered : PendingCovered coordinates context)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (runDeferredLayerSchedule parameter table ftsSecret index
        chronologicalLayerSchedule
        (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
      finalizeDeferredLayerSchedule coordinates) =
      evalDist (runResolvedFromTable context fuel table
          ((sequenceFin fun lay : Layer =>
            maskedSignLayer parameter ftsSecret index lay).run cache) >>=
        finalizeResolvedRunStateFromTable coordinates table) := by
  calc
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          deferredLayerSchedule
          (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
        finalizeDeferredLayerSchedule coordinates) :=
      evalDist_chronologicalLayerSchedule_bind_eq_deferred parameter table ftsSecret index
        (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩)
        (finalizeDeferredLayerSchedule coordinates)
    _ = evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          deferredLayerSelections
          (some ⟨context, fuel, emptyDeferredLayerStore cache, table⟩) >>=
        finalizeDeferredLayerSchedule coordinates) :=
      evalDist_deferredLayerSchedule_then_finalize_eq_selections parameter table ftsSecret
        index coordinates ⟨context, fuel, emptyDeferredLayerStore cache, table⟩ rfl hvalid
        hcovered
    _ = _ := evalDist_deferredLayerSelections_then_finalize_eq_sequenceFin parameter table
      ftsSecret index context fuel cache coordinates hvalid.valuesConsistent hstarts

end SphincsSecurity.Concrete.OtsProbeSimulation
