import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinary

/-!
# One-sided ordinary boundary refinement

The canonical side can spend a probe at an unpublished structural value which the materialized
side can already read. A miss preserves finalization semantics while consuming one unit of fuel;
a hit is exactly the private structural outcome and imposes no ordinary-failure obligation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationViewEq table
      { left with state := left.state.addPending coordinate candidate } right := by
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingEq := ?_ }
  · intro other otherOutput hotherValue hhit
    by_cases heq : other = coordinate
    · subst other
      have houtput : otherOutput = output := by
        change resolvedCompletionValue table left coordinate = some otherOutput at hotherValue
        rw [hvalue] at hotherValue
        exact (Option.some.inj hotherValue).symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hhit
      exact hhit.elim (hview.leftClean coordinate output hvalue) hmiss
    · have hhitBase : left.state.hitAt other otherOutput := by
        rw [hitAt_addPending_of_ne left.state coordinate other candidate otherOutput (Ne.symm heq)]
          at hhit
        exact hhit
      exact hview.leftClean other otherOutput hotherValue hhitBase
  · intro other hnone
    have hne : other ≠ coordinate := by
      intro heq
      subst other
      change resolvedCompletionValue table left coordinate = none at hnone
      rw [hvalue] at hnone
      contradiction
    calc
      (left.state.addPending coordinate candidate).pendingAt other =
          left.state.pendingAt other := by
        ext digest
        simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending, hne]
      _ = right.state.pendingAt other := hview.pendingEq other hnone

theorem FinalizationContextEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationContextEq table
      (some { left with state := left.state.addPending coordinate candidate })
      (some right) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  obtain ⟨completion, hcompletion⟩ := hleftCompletable
  have hcompletionOutput : completion coordinate = output :=
    hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hcompletion' : DeferredCompletion table
      { left with state := left.state.addPending coordinate candidate } completion :=
    hcompletion.addPending_of_avoids coordinate candidate (by
      rwa [hcompletionOutput])
  have hleftCompletable' : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate } :=
    ⟨completion, hcompletion'⟩
  exact
    ⟨hview.addPending_left_of_resolved coordinate candidate output hvalue hmiss,
      hleftValid.addPending_of_completable coordinate candidate hleftCompletable',
      hrightValid, hleftCompletable'⟩

structure FinalizationViewLE (table : OtsSecretIndex → HashOutput)
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
  pendingLE : ∀ coordinate,
    resolvedCompletionValue table left coordinate = none →
      left.state.pendingAt coordinate ⊆ right.state.pendingAt coordinate

theorem FinalizationViewLE.of_eq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) :
    FinalizationViewLE table left right where
  leftConsistent := hview.leftConsistent
  rightConsistent := hview.rightConsistent
  leftStarts := hview.leftStarts
  rightStarts := hview.rightStarts
  valueEq := hview.valueEq
  leftClean := hview.leftClean
  rightClean := hview.rightClean
  pendingLE coordinate hnone := by
    rw [hview.pendingEq coordinate hnone]

theorem FinalizationViewLE.refl
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    FinalizationViewLE table context context :=
  FinalizationViewLE.of_eq
    (FinalizationViewEq.refl table context hvalid hstarts hclean)

theorem FinalizationViewLE.trans
    {table : OtsSecretIndex → HashOutput} {left middle right : DeferredContext}
    (hleft : FinalizationViewLE table left middle)
    (hright : FinalizationViewLE table middle right) :
    FinalizationViewLE table left right := by
  refine
    { leftConsistent := hleft.leftConsistent
      rightConsistent := hright.rightConsistent
      leftStarts := hleft.leftStarts
      rightStarts := hright.rightStarts
      valueEq := hleft.valueEq.trans hright.valueEq
      leftClean := hleft.leftClean
      rightClean := hright.rightClean
      pendingLE := ?_ }
  intro coordinate hvalue candidate hcandidate
  have hmiddleValue : resolvedCompletionValue table middle coordinate = none := by
    rw [← hleft.valueEq]
    exact hvalue
  exact hright.pendingLE coordinate hmiddleValue
    (hleft.pendingLE coordinate hvalue hcandidate)

theorem FinalizationViewLE.deferredCompletion_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table right completion) :
    DeferredCompletion table left completion := by
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    have hleftValue : resolvedCompletionValue table left coordinate = some output := by
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          have houtput := hview.leftStarts
            ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
          simp [resolvedCompletionValue, houtput]
      | position position =>
          simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
    have hrightValue : resolvedCompletionValue table right coordinate = some output := by
      rw [← hview.valueEq]
      exact hleftValue
    exact hcompletion.eq_resolvedCompletionValue coordinate output hrightValue
  · intro position output hvalue
    have hleftValue : resolvedCompletionValue table left (.position position) =
        some output := by
      unfold resolvedCompletionValue DeferredContext.positionValue
      cases hstate : left.state.values (.position position) with
      | some cached =>
          have hsame := hview.leftConsistent position cached hstate
          rw [hsame] at hvalue
          have hcached : cached = output := Option.some.inj hvalue
          simp [hstate, hcached]
      | none => simpa [hstate] using hvalue
    have hrightValue : resolvedCompletionValue table right (.position position) =
        some output := by
      rw [← hview.valueEq]
      exact hleftValue
    exact hcompletion.eq_resolvedCompletionValue (.position position) output hrightValue
  · intro coordinate candidate hmember
    cases hvalue : resolvedCompletionValue table left coordinate with
    | some output =>
        have hrightValue : resolvedCompletionValue table right coordinate = some output := by
          rw [← hview.valueEq]
          exact hvalue
        have hcompletionOutput : completion coordinate = output :=
          hcompletion.eq_resolvedCompletionValue coordinate output hrightValue
        intro hhit
        apply hview.leftClean coordinate output hvalue
        unfold LazyRevealProbe.State.hitAt
        rw [LazyRevealProbe.State.mem_pendingAt_iff]
        have hcandidate : candidate = truncateHash output := by
          rw [← hhit, hcompletionOutput]
        simpa [hcandidate] using hmember
    | none =>
        have hrightValue : resolvedCompletionValue table right coordinate = none := by
          rw [← hview.valueEq]
          exact hvalue
        have hleftPending : candidate ∈ left.state.pendingAt coordinate :=
          (LazyRevealProbe.State.mem_pendingAt_iff left.state coordinate candidate).2 hmember
        have hrightPending : candidate ∈ right.state.pendingAt coordinate :=
          hview.pendingLE coordinate hvalue hleftPending
        exact hcompletion.2.2.1 coordinate candidate
          ((LazyRevealProbe.State.mem_pendingAt_iff right.state coordinate candidate).1
            hrightPending)

structure FinalizationContextLE (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) : Prop where
  view : FinalizationViewLE table left right
  leftValid : left.Valid
  rightValid : right.Valid
  rightCompletable : DeferredCompletable table right

theorem FinalizationContextLE.of_eq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    FinalizationContextLE table left right := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  obtain ⟨completion, hcompletion⟩ := hleftCompletable
  exact
    { view := FinalizationViewLE.of_eq hview
      leftValid := hleftValid
      rightValid := hrightValid
      rightCompletable :=
        ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩ }

theorem FinalizationContextLE.leftCompletable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) :
    DeferredCompletable table left := by
  obtain ⟨completion, hcompletion⟩ := hcontext.rightCompletable
  exact ⟨completion, hcontext.view.deferredCompletion_left completion hcompletion⟩

theorem FinalizationViewLE.not_rightCompletable_of_not_leftCompletable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (hleft : ¬DeferredCompletable table left) :
    ¬DeferredCompletable table right := by
  rintro ⟨completion, hcompletion⟩
  exact hleft ⟨completion, hview.deferredCompletion_left completion hcompletion⟩

theorem FinalizationViewLE.addPending_right_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (coordinate : Coordinate)
    (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewLE table left
      { right with state := right.state.addPending coordinate candidate } := by
  refine
    { leftConsistent := hview.leftConsistent
      rightConsistent := hview.rightConsistent.addPending coordinate candidate
      leftStarts := hview.leftStarts
      rightStarts := hview.rightStarts.addPending coordinate candidate
      valueEq := hview.valueEq
      leftClean := hview.leftClean
      rightClean := ?_
      pendingLE := ?_ }
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hcompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue digest hdigest
    have hbase := hview.pendingLE other hvalue hdigest
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hbase ⊢
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
    exact Or.inr hbase

theorem FinalizationContextLE.addPending_right_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationContextLE table left
      { right with state := right.state.addPending coordinate candidate } where
  view := hcontext.view.addPending_right_of_completable coordinate candidate hcompletable
  leftValid := hcontext.leftValid
  rightValid := hcontext.rightValid.addPending_of_completable
    coordinate candidate hcompletable
  rightCompletable := hcompletable

theorem FinalizationViewLE.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationViewLE table
      { left with state := left.state.addPending coordinate candidate } right := by
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingLE := ?_ }
  · intro other otherOutput hotherValue hhit
    by_cases heq : other = coordinate
    · subst other
      have houtput : otherOutput = output := by
        change resolvedCompletionValue table left coordinate = some otherOutput at hotherValue
        rw [hvalue] at hotherValue
        exact (Option.some.inj hotherValue).symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hhit
      exact hhit.elim (hview.leftClean coordinate output hvalue) hmiss
    · have hhitBase : left.state.hitAt other otherOutput := by
        rw [hitAt_addPending_of_ne left.state coordinate other candidate otherOutput
          (Ne.symm heq)] at hhit
        exact hhit
      exact hview.leftClean other otherOutput hotherValue hhitBase
  · intro other hnone digest hdigest
    have hne : other ≠ coordinate := by
      intro heq
      subst other
      change resolvedCompletionValue table left coordinate = none at hnone
      rw [hvalue] at hnone
      contradiction
    have hbase : digest ∈ left.state.pendingAt other := by
      have hpending :
          (left.state.addPending coordinate candidate).pendingAt other =
            left.state.pendingAt other := by
        ext otherCandidate
        simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending, hne]
      rw [← hpending]
      exact hdigest
    exact hview.pendingLE other hnone hbase

theorem FinalizationContextLE.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationContextLE table
      { left with state := left.state.addPending coordinate candidate } right := by
  obtain ⟨completion, hcompletion⟩ := hcontext.leftCompletable
  have hcompletionOutput : completion coordinate = output :=
    hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hcompletion' : DeferredCompletion table
      { left with state := left.state.addPending coordinate candidate } completion :=
    hcompletion.addPending_of_avoids coordinate candidate (by
      rwa [hcompletionOutput])
  exact
    { view := hcontext.view.addPending_left_of_resolved
        coordinate candidate output hvalue hmiss
      leftValid := hcontext.leftValid.addPending_of_completable coordinate candidate
        ⟨completion, hcompletion'⟩
      rightValid := hcontext.rightValid
      rightCompletable := hcontext.rightCompletable }

theorem FinalizationViewLE.addPending_both_of_right_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewLE table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  obtain ⟨completion, hrightCompletion⟩ := hrightCompletable
  have hrightBase := hrightCompletion.of_addPending coordinate candidate
  have hleftBase := hview.deferredCompletion_left completion hrightBase
  have havoids := hrightCompletion.2.2.1 coordinate candidate (by
    simp [LazyRevealProbe.State.addPending])
  have hleftCompletion :=
    hleftBase.addPending_of_avoids coordinate candidate havoids
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent.addPending coordinate candidate
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts.addPending coordinate candidate
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := ?_
      pendingLE := ?_ }
  · intro other output hvalue hhit
    have houtput := hleftCompletion.eq_resolvedCompletionValue other output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hleftCompletion.2.2.1 other (truncateHash output) hhit (by rw [houtput])
  · intro other output hvalue hhit
    have houtput := hrightCompletion.eq_resolvedCompletionValue other output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hrightCompletion.2.2.1 other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue digest hdigest
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hdigest ⊢
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hdigest ⊢
    rcases hdigest with hnew | hold
    · exact Or.inl hnew
    · right
      rw [← LazyRevealProbe.State.mem_pendingAt_iff] at hold ⊢
      exact hview.pendingLE other hvalue hold

theorem FinalizationContextLE.addPending_both_of_right_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationContextLE table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  have hview := hcontext.view.addPending_both_of_right_completable
    coordinate candidate hrightCompletable
  have hleftCompletable : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate } := by
    obtain ⟨completion, hcompletion⟩ := hrightCompletable
    exact ⟨completion, hview.deferredCompletion_left completion hcompletion⟩
  exact
    { view := hview
      leftValid := hcontext.leftValid.addPending_of_completable coordinate candidate
        hleftCompletable
      rightValid := hcontext.rightValid.addPending_of_completable coordinate candidate
        hrightCompletable
      rightCompletable := hrightCompletable }

theorem FinalizationViewLE.privateValue_of_left_hidden_of_right_materialized
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (position : Position)
    (output : HashOutput)
    (hleft : left.state.values (.position position) = none)
    (hright : right.state.values (.position position) = some output) :
    left.values position = some output := by
  have hposition : left.positionValue position = some output := by
    change resolvedCompletionValue table left (.position position) = some output
    rw [hview.valueEq]
    simp [resolvedCompletionValue, DeferredContext.positionValue, hright]
  simpa [DeferredContext.positionValue, hleft] using hposition

set_option maxRecDepth 100000 in
theorem FinalizationViewLE.materialize_position_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (position : Position)
    (output : HashOutput)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    FinalizationViewLE table
      { left with state := left.state.materialize (.position position) output } right := by
  let materialized : DeferredContext :=
    { left with state := left.state.materialize (.position position) output }
  have hresolved : resolvedCompletionValue table materialized =
      resolvedCompletionValue table left := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position other =>
        by_cases heq : other = position
        · subst other
          simp [materialized, resolvedCompletionValue, DeferredContext.positionValue,
            LazyRevealProbe.State.materialize, hhidden, hprivate]
        · simp [materialized, resolvedCompletionValue, DeferredContext.positionValue,
            LazyRevealProbe.State.materialize, Function.update_of_ne,
            show Coordinate.position other ≠ Coordinate.position position by simpa using heq]
  refine
    { leftConsistent := ?_
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.materialize_position position output
      rightStarts := hview.rightStarts
      valueEq := hresolved.trans hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingLE := ?_ }
  · intro other cached hvalue
    by_cases heq : other = position
    · subst other
      have hsame : cached = output := by
        simpa [materialized, LazyRevealProbe.State.materialize] using hvalue.symm
      subst cached
      exact hprivate
    · apply hview.leftConsistent other cached
      simpa [materialized, LazyRevealProbe.State.materialize, Function.update_of_ne,
        show Coordinate.position other ≠ Coordinate.position position by simpa using heq]
        using hvalue
  · intro coordinate otherOutput hvalue
    have horiginal : resolvedCompletionValue table left coordinate = some otherOutput := by
      rw [← hresolved]
      exact hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      change ¬(left.state.clearPending (.position position)).hitAt
        (.position position) otherOutput
      exact not_hitAt_clearPending_self left.state (.position position) otherOutput
    · change ¬(left.state.clearPending (.position position)).hitAt coordinate otherOutput
      exact (hitAt_clearPending_of_ne left.state (.position position) coordinate
        otherOutput heq).not.mpr (hview.leftClean coordinate otherOutput horiginal)
  · intro coordinate hvalue candidate hcandidate
    have horiginal : resolvedCompletionValue table left coordinate = none := by
      rw [← hresolved]
      exact hvalue
    have hbase : candidate ∈ left.state.pendingAt coordinate := by
      by_cases heq : coordinate = .position position
      · subst coordinate
        change resolvedCompletionValue table materialized (.position position) = none at hvalue
        simp [materialized, resolvedCompletionValue, DeferredContext.positionValue,
          LazyRevealProbe.State.materialize] at hvalue
      · change candidate ∈
          (left.state.clearPending (.position position)).pendingAt coordinate at hcandidate
        rw [pendingAt_clearPending_of_ne left.state (.position position) coordinate heq]
          at hcandidate
        exact hcandidate
    exact hview.pendingLE coordinate horiginal hbase

theorem FinalizationContextLE.materialize_position_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (position : Position)
    (output : HashOutput)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    FinalizationContextLE table
      { left with state := left.state.materialize (.position position) output } right where
  view := hcontext.view.materialize_position_left position output hhidden hprivate
  leftValid := hcontext.leftValid.materialize_position position output hprivate
  rightValid := hcontext.rightValid
  rightCompletable := hcontext.rightCompletable

theorem FinalizationViewLE.leftValid_of_view
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) : left.Valid := by
  refine ⟨hview.leftConsistent, ?_⟩
  intro coordinate output hvalue
  apply hview.leftClean coordinate output
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      have hsame := hview.leftStarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
      simp [resolvedCompletionValue, hsame]
  | position position =>
      simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]

theorem FinalizationViewLE.rightValid_of_view
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) : right.Valid := by
  refine ⟨hview.rightConsistent, ?_⟩
  intro coordinate output hvalue
  apply hview.rightClean coordinate output
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      have hsame := hview.rightStarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
      simp [resolvedCompletionValue, hsame]
  | position position =>
      simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]

set_option maxRecDepth 100000 in
theorem FinalizationViewLE.materialize_position_both
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (position : Position)
    (output : HashOutput) :
    FinalizationViewLE table
      { state := left.state.materialize (.position position) output
        values := left.values.install position output }
      { state := right.state.materialize (.position position) output
        values := right.values.install position output } := by
  let leftMaterialized : DeferredContext :=
    { state := left.state.materialize (.position position) output
      values := left.values.install position output }
  let rightMaterialized : DeferredContext :=
    { state := right.state.materialize (.position position) output
      values := right.values.install position output }
  refine
    { leftConsistent := ?_
      rightConsistent := ?_
      leftStarts := hview.leftStarts.materialize_position position output
      rightStarts := hview.rightStarts.materialize_position position output
      valueEq := ?_
      leftClean := ?_
      rightClean := ?_
      pendingLE := ?_ }
  · intro other cached hvalue
    by_cases heq : other = position
    · subst other
      have hsame : cached = output := by
        simpa [leftMaterialized, LazyRevealProbe.State.materialize] using hvalue.symm
      subst cached
      simp [DeferredStructuralValues.install]
    · have hold := hview.leftConsistent other cached (by
        simpa [leftMaterialized, LazyRevealProbe.State.materialize, Function.update_of_ne,
        show Coordinate.position other ≠ Coordinate.position position by simpa using heq,
        DeferredStructuralValues.install, heq] using hvalue)
      simpa [leftMaterialized, DeferredStructuralValues.install, heq] using hold
  · intro other cached hvalue
    by_cases heq : other = position
    · subst other
      have hsame : cached = output := by
        simpa [rightMaterialized, LazyRevealProbe.State.materialize] using hvalue.symm
      subst cached
      simp [DeferredStructuralValues.install]
    · have hold := hview.rightConsistent other cached (by
        simpa [rightMaterialized, LazyRevealProbe.State.materialize, Function.update_of_ne,
        show Coordinate.position other ≠ Coordinate.position position by simpa using heq,
        DeferredStructuralValues.install, heq] using hvalue)
      simpa [rightMaterialized, DeferredStructuralValues.install, heq] using hold
  · funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position other =>
        by_cases heq : other = position
        · subst other
          simp [resolvedCompletionValue, DeferredContext.positionValue,
            LazyRevealProbe.State.materialize]
        · simpa [leftMaterialized, rightMaterialized, resolvedCompletionValue,
            DeferredContext.positionValue, LazyRevealProbe.State.materialize,
            Function.update_of_ne,
            show Coordinate.position other ≠ Coordinate.position position by simpa using heq,
            DeferredStructuralValues.install, heq] using congrFun hview.valueEq (.position other)
  · intro coordinate otherOutput hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      change ¬(left.state.clearPending (.position position)).hitAt
        (.position position) otherOutput
      exact not_hitAt_clearPending_self left.state (.position position) otherOutput
    · have horiginal : resolvedCompletionValue table left coordinate = some otherOutput := by
        cases coordinate with
        | chainStart => exact hvalue
        | position other =>
            have hother : other ≠ position := by simpa using heq
            simpa [leftMaterialized, resolvedCompletionValue, DeferredContext.positionValue,
              LazyRevealProbe.State.materialize, Function.update_of_ne,
              show Coordinate.position other ≠ Coordinate.position position by
                simpa using hother,
              DeferredStructuralValues.install, hother] using hvalue
      change ¬(left.state.clearPending (.position position)).hitAt coordinate otherOutput
      exact (hitAt_clearPending_of_ne left.state (.position position) coordinate
        otherOutput heq).not.mpr (hview.leftClean coordinate otherOutput horiginal)
  · intro coordinate otherOutput hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      change ¬(right.state.clearPending (.position position)).hitAt
        (.position position) otherOutput
      exact not_hitAt_clearPending_self right.state (.position position) otherOutput
    · have horiginal : resolvedCompletionValue table right coordinate = some otherOutput := by
        cases coordinate with
        | chainStart => exact hvalue
        | position other =>
            have hother : other ≠ position := by simpa using heq
            simpa [rightMaterialized, resolvedCompletionValue, DeferredContext.positionValue,
              LazyRevealProbe.State.materialize, Function.update_of_ne,
              show Coordinate.position other ≠ Coordinate.position position by
                simpa using hother,
              DeferredStructuralValues.install, hother] using hvalue
      change ¬(right.state.clearPending (.position position)).hitAt coordinate otherOutput
      exact (hitAt_clearPending_of_ne right.state (.position position) coordinate
        otherOutput heq).not.mpr (hview.rightClean coordinate otherOutput horiginal)
  · intro coordinate hvalue candidate hcandidate
    have hne : coordinate ≠ .position position := by
      intro heq
      subst coordinate
      change resolvedCompletionValue table leftMaterialized (.position position) = none at hvalue
      simp [leftMaterialized, resolvedCompletionValue, DeferredContext.positionValue,
        LazyRevealProbe.State.materialize] at hvalue
    have horiginal : resolvedCompletionValue table left coordinate = none := by
      cases coordinate with
      | chainStart => exact hvalue
      | position other =>
          have hother : other ≠ position := by simpa using hne
          simpa [leftMaterialized, resolvedCompletionValue, DeferredContext.positionValue,
            LazyRevealProbe.State.materialize, Function.update_of_ne,
            show Coordinate.position other ≠ Coordinate.position position by
              simpa using hother,
            DeferredStructuralValues.install, hother] using hvalue
    have hbase : candidate ∈ left.state.pendingAt coordinate := by
      change candidate ∈
        (left.state.clearPending (.position position)).pendingAt coordinate at hcandidate
      rw [pendingAt_clearPending_of_ne left.state (.position position) coordinate hne]
        at hcandidate
      exact hcandidate
    have hrightBase := hview.pendingLE coordinate horiginal hbase
    change candidate ∈
      (right.state.clearPending (.position position)).pendingAt coordinate
    rw [pendingAt_clearPending_of_ne right.state (.position position) coordinate hne]
    exact hrightBase

set_option maxRecDepth 100000 in
theorem FinalizationContextLE.materialize_position_both
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (position : Position)
    (output : HashOutput) :
    FinalizationContextLE table
      { state := left.state.materialize (.position position) output
        values := left.values.install position output }
      { state := right.state.materialize (.position position) output
        values := right.values.install position output } := by
  let leftMaterialized : DeferredContext :=
    { state := left.state.materialize (.position position) output
      values := left.values.install position output }
  let rightMaterialized : DeferredContext :=
    { state := right.state.materialize (.position position) output
      values := right.values.install position output }
  have hview := hcontext.view.materialize_position_both position output
  obtain ⟨completion, hcompletion⟩ := hcontext.rightCompletable
  let nextCompletion : Coordinate → HashOutput :=
    Function.update completion (.position position) output
  have hnextCompletion : DeferredCompletion table rightMaterialized nextCompletion := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro coordinate cached hvalue
      by_cases heq : coordinate = .position position
      · subst coordinate
        have hsame : cached = output := by
          simpa [rightMaterialized, LazyRevealProbe.State.materialize] using hvalue.symm
        simp [nextCompletion, hsame]
      · have hold := hcompletion.1 coordinate cached (by
          simpa [rightMaterialized, LazyRevealProbe.State.materialize,
            Function.update_of_ne heq] using hvalue)
        simpa [nextCompletion, Function.update_of_ne, heq] using hold
    · intro other cached hvalue
      by_cases heq : other = position
      · subst other
        have hsame : cached = output := by
          simpa [rightMaterialized, DeferredStructuralValues.install] using hvalue.symm
        simp [nextCompletion, hsame]
      · have hold := hcompletion.2.1 other cached (by
          simpa [rightMaterialized, DeferredStructuralValues.install, heq] using hvalue)
        simpa [nextCompletion, Function.update_of_ne,
          show Coordinate.position other ≠ Coordinate.position position by simpa using heq]
          using hold
    · intro coordinate candidate hmember
      have hparts : (coordinate, candidate) ∈ right.state.pending ∧
          coordinate ≠ .position position := by
        change (coordinate, candidate) ∈
          right.state.pendingAway (.position position) at hmember
        simpa [LazyRevealProbe.State.pendingAway] using hmember
      simpa [nextCompletion, Function.update_of_ne, hparts.2] using
        hcompletion.2.2.1 coordinate candidate hparts.1
    · intro index
      simpa [nextCompletion, Function.update_of_ne,
        show index.coordinate ≠ Coordinate.position position by
          simp [OtsSecretIndex.coordinate]] using hcompletion.2.2.2 index
  exact
    { view := hview
      leftValid := hview.leftValid_of_view
      rightValid := hview.rightValid_of_view
      rightCompletable := ⟨nextCompletion, hnextCompletion⟩ }

theorem LazyRevealProbe.ValuesLE.materialize_both
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : LazyRevealProbe.ValuesLE left right)
    (coordinate : Coordinate) (output : HashOutput) :
    LazyRevealProbe.ValuesLE (left.materialize coordinate output)
      (right.materialize coordinate output) := by
  intro other cached hvalue
  by_cases heq : other = coordinate
  · subst other
    have hsame : cached = output := by
      simpa [LazyRevealProbe.State.materialize] using hvalue.symm
    simp [LazyRevealProbe.State.materialize, hsame]
  · have hbase : left.values other = some cached := by
      simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue
    simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using
      hvalues other cached hbase

theorem LazyRevealProbe.ValuesLE.materialize_left
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : LazyRevealProbe.ValuesLE left right)
    (coordinate : Coordinate) (output : HashOutput)
    (hright : right.values coordinate = some output) :
    LazyRevealProbe.ValuesLE (left.materialize coordinate output) right := by
  intro other cached hvalue
  by_cases heq : other = coordinate
  · subst other
    have hsame : cached = output := by
      simpa [LazyRevealProbe.State.materialize] using hvalue.symm
    simpa [hsame] using hright
  · apply hvalues other cached
    simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hvalue

theorem FinalizationViewLE.publish
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewLE table left right) (coordinate : Coordinate) :
    FinalizationViewLE table
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } where
  leftConsistent := hview.leftConsistent.publish coordinate
  rightConsistent := hview.rightConsistent.publish coordinate
  leftStarts := hview.leftStarts
  rightStarts := hview.rightStarts
  valueEq := hview.valueEq
  leftClean := hview.leftClean
  rightClean := hview.rightClean
  pendingLE := hview.pendingLE

theorem FinalizationContextLE.publish
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) (coordinate : Coordinate) :
    FinalizationContextLE table
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } where
  view := hcontext.view.publish coordinate
  leftValid := hcontext.leftValid.publish coordinate
  rightValid := hcontext.rightValid.publish coordinate
  rightCompletable := hcontext.rightCompletable.publish coordinate

theorem PublishedValues.publish_of_value
    {state : LazyRevealProbe.State Coordinate} (hpublished : PublishedValues state)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    PublishedValues (state.publish coordinate) := by
  intro other hrevealed
  simp only [LazyRevealProbe.State.publish, Finset.mem_insert] at hrevealed
  rcases hrevealed with heq | hold
  · subst other
    simp [hvalue]
  · exact hpublished other hold

structure OrdinaryMaterializedRunEq (table : OtsSecretIndex → HashOutput)
    (left right : ResolvedRunResult (α × SplitHashCache)) : Prop where
  value_eq : left.value.1 = right.value.1
  context_le : FinalizationContextLE table left.context right.context
  remaining_le : left.remaining ≤ right.remaining
  left_table : left.table = table
  right_table : right.table = table
  cache_eq : ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2
  revealed_eq : left.context.state.revealed = right.context.state.revealed
  values_le : LazyRevealProbe.ValuesLE left.context.state right.context.state
  left_published : PublishedValues left.context.state
  right_materialized :
    right.context = directDeferredContext right.context.state

def OrdinaryMaterializedDoomedRun (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α) : Prop :=
  FinalizationDoomedRun table (some result) ∧
    result.context = directDeferredContext result.context.state

def DirectDetailedOrdinaryRunEq (table : OtsSecretIndex → HashOutput) :
    DirectDetailedResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .stopped .privateStructuralHit, _ => True
  | .stopped .ordinaryHit, .stopped .privateStructuralHit => False
  | .stopped .ordinaryHit, .stopped _ => True
  | .stopped .ordinaryHit, .done right =>
      OrdinaryMaterializedDoomedRun table right
  | .stopped .fuelExhausted, .stopped .ordinaryHit => True
  | .stopped .fuelExhausted, .stopped .fuelExhausted => True
  | .stopped .fuelExhausted, .done right =>
      OrdinaryMaterializedDoomedRun table right
  | .stopped .fuelExhausted, _ => False
  | .done _, .stopped .privateStructuralHit => False
  | .done _, .stopped _ => True
  | .done left, .done right =>
      OrdinaryMaterializedRunEq table left right ∨
        PrivateStructuralHit left.context ∨
        OrdinaryMaterializedDoomedRun table right

def DirectDetailedMaterialized : DirectDetailedResult α → Prop
  | .stopped .privateStructuralHit => False
  | .stopped _ => True
  | .done result =>
      result.context = directDeferredContext result.context.state

set_option maxRecDepth 100000 in
theorem directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : DirectDetailedResult α)
    (hresult : result ∈ support
      (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation)) :
    DirectDetailedMaterialized result := by
  induction computation using OracleComp.inductionOn generalizing state fuel result with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          have hcontext :
              { directDeferredContext state with state := state.ensure coordinate } =
                directDeferredContext (state.ensure coordinate) := by
            simp [directDeferredContext, directDeferredValues_ensure]
          exact ih () (state.ensure coordinate) fuel result (hcontext ▸ hresult)
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero =>
              simp at hresult
              subst result
              trivial
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih () state remaining result (by
                  simpa [directDeferredContext, hrevealed] using hresult)
              · simp only [directDeferredContext, hrevealed, ↓reduceIte] at hresult
                have hcontext :
                    { directDeferredContext state with
                      state := state.addPending coordinate candidate } =
                        directDeferredContext (state.addPending coordinate candidate) := by
                  simp [directDeferredContext, directDeferredValues_addPending]
                exact ih () (state.addPending coordinate candidate) remaining result
                  (hcontext ▸ hresult)
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel result hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel result (by
            simpa [directDeferredContext, directDeferredValues_publish] using hresult)
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              exact ih output state fuel result (by
                simpa only [directDeferredContext, hvalue] using hresult)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : state.hitAt index.coordinate output
                  · change state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [directDeferredContext, hvalue, hhit, ↓reduceIte] at hresult
                    simp at hresult
                    subst result
                    trivial
                  · have hcontext :
                        { state := state.materialize index.coordinate output
                          values := directDeferredValues state } =
                            directDeferredContext
                              (state.materialize index.coordinate output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_chainStart]
                    change ¬state.hitAt (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [directDeferredContext, hvalue, hhit, ↓reduceIte] at hresult
                    exact ih output (state.materialize index.coordinate output) fuel result
                      (hcontext ▸ hresult)
              | position position =>
                  simp only [directDeferredContext, directDeferredValues, hvalue,
                    mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                    subst result
                    trivial
                  · simp only [hhit, ↓reduceIte] at hrest
                    have hcontext :
                        { state := state.materialize (.position position) output
                          values := (directDeferredValues state).install position output } =
                            directDeferredContext
                              (state.materialize (.position position) output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_position]
                    exact ih output (state.materialize (.position position) output) fuel result
                      (hcontext ▸ hrest)

theorem finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (result : ResolvedRunResult α)
    (hdoomed : DoomedResolvedContext table context)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    FinalizationDoomedRun table (some result) := by
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
    computation context fuel table result hresult
  have hcore := resolvedCore_of_mem_runDirectResolvedFromTable computation context fuel table
    result hdoomed.1 hdoomed.2.1 hdirect
  exact ⟨hcore.1, hcore.2.1, hcore.2.2,
    not_deferredCompletable_of_mem_runDirectResolvedFromTable computation context fuel table
      result hdoomed.1 hdoomed.2.1 hdirect hdoomed.2.2⟩

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_of_right_materializedDoomed
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (right : DeferredContext) (rightFuel : Nat)
    (hrightDoomed : DoomedResolvedContext table right)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      leftRun
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectDetailedOrdinaryRunEq table) := by
  have hbase := relTriple_true
    leftRun
    (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support leftRun)
      (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro leftResult rightResult hrelation
  have hrightShape : DirectDetailedMaterialized rightResult := by
    have hsupport := hrelation.2
    rw [hrightMaterialized] at hsupport
    exact directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
      rightComputation right.state rightFuel table rightResult hsupport
  cases rightResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hrightShape
      | ordinaryHit =>
          cases leftResult with
          | stopped leftReason => cases leftReason <;> trivial
          | done _ => trivial
      | fuelExhausted =>
          cases leftResult with
          | stopped leftReason => cases leftReason <;> trivial
          | done _ => trivial
  | done rightResult =>
      have hdoomed :=
        finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
          rightComputation right rightFuel rightResult hrightDoomed hrelation.2
      have hmaterialized := hrightShape
      cases leftResult with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => trivial
          | ordinaryHit => exact ⟨hdoomed, hmaterialized⟩
          | fuelExhausted => exact ⟨hdoomed, hmaterialized⟩
      | done _ =>
          right
          right
          exact ⟨hdoomed, hmaterialized⟩

theorem relTriple_pure_privateStructuralHit_any
    (table : OtsSecretIndex → HashOutput)
    (rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache))) :
    RelTriple
      (pure (.stopped .privateStructuralHit) :
        ProbComp (DirectDetailedResult (α × SplitHashCache)))
      rightRun (DirectDetailedOrdinaryRunEq table) := by
  have hbase := relTriple_true
    (pure (.stopped .privateStructuralHit) :
      ProbComp (DirectDetailedResult (α × SplitHashCache))) rightRun
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (pure (.stopped .privateStructuralHit) :
          ProbComp (DirectDetailedResult (α × SplitHashCache))))
      (fun result hresult => hresult)
  apply relTriple_post_mono hsupported
  intro leftResult _ hrelation
  have hleft : leftResult = .stopped .privateStructuralHit := by
    simpa using hrelation.2
  subst leftResult
  trivial

theorem relTriple_any_pure_nonprivateStop
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (reason : DirectStopReason) (hreason : reason ≠ .privateStructuralHit) :
    RelTriple leftRun
      (pure (.stopped reason) :
        ProbComp (DirectDetailedResult (α × SplitHashCache)))
      (DirectDetailedOrdinaryRunEq table) := by
  have hbase := relTriple_true leftRun
    (pure (.stopped reason) :
      ProbComp (DirectDetailedResult (α × SplitHashCache)))
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro leftResult rightResult hrelation
  have hright : rightResult = .stopped reason := by
    simpa using hrelation.2
  subst rightResult
  cases reason with
  | privateStructuralHit => contradiction
  | ordinaryHit => cases leftResult with
    | stopped leftReason => cases leftReason <;> trivial
    | done _ => trivial
  | fuelExhausted => cases leftResult with
    | stopped leftReason => cases leftReason <;> trivial
    | done _ => trivial

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_bind
    (table : OtsSecretIndex → HashOutput)
    (left right : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (leftNext rightNext : α → SplitHashCache →
      OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftContext rightContext : DeferredContext) (leftFuel rightFuel : Nat)
    (hleft : RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table left)
      (runDirectResolvedDetailedFromTable rightContext rightFuel table right)
      (DirectDetailedOrdinaryRunEq table))
    (hclean : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryRunEq table))
    (hprivate : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      PrivateStructuralHit leftResult.context →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryRunEq table)) :
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left >>= fun value => leftNext value.1 value.2))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right >>= fun value => rightNext value.1 value.2))
      (DirectDetailedOrdinaryRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  apply relTriple_bind hleft
  intro leftResult rightResult hrelation
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_pure_privateStructuralHit_any table _
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
                (pure (.stopped .ordinaryHit))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
                (pure (.stopped .fuelExhausted))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_pure_nonprivateStop table _ .ordinaryHit (by decide)
          | fuelExhausted =>
              exact relTriple_any_pure_nonprivateStop table _ .fuelExhausted (by decide)
      | done rightResult =>
          rcases hrelation with hcleanRelation | hprivateRelation | hdoomedRelation
          · exact hclean leftResult rightResult hcleanRelation
          · exact hprivate leftResult rightResult hprivateRelation
          · simp only
            rw [hdoomedRelation.1.1]
            exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
              (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
                leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomedRelation.1.2
                hdoomedRelation.2

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_bind_with_support
    (table : OtsSecretIndex → HashOutput)
    (left right : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (leftNext rightNext : α → SplitHashCache →
      OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftContext rightContext : DeferredContext) (leftFuel rightFuel : Nat)
    (hleft : RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table left)
      (runDirectResolvedDetailedFromTable rightContext rightFuel table right)
      (DirectDetailedOrdinaryRunEq table))
    (hclean : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      DirectDetailedResult.done leftResult ∈ support
        (runDirectResolvedDetailedFromTable leftContext leftFuel table left) →
      DirectDetailedResult.done rightResult ∈ support
        (runDirectResolvedDetailedFromTable rightContext rightFuel table right) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryRunEq table))
    (hprivate : ∀ (leftResult rightResult :
      ResolvedRunResult (α × SplitHashCache)),
      DirectDetailedResult.done leftResult ∈ support
        (runDirectResolvedDetailedFromTable leftContext leftFuel table left) →
      DirectDetailedResult.done rightResult ∈ support
        (runDirectResolvedDetailedFromTable rightContext rightFuel table right) →
      PrivateStructuralHit leftResult.context →
      RelTriple
        (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
          leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
        (runDirectResolvedDetailedFromTable rightResult.context rightResult.remaining
          rightResult.table (rightNext rightResult.value.1 rightResult.value.2))
        (DirectDetailedOrdinaryRunEq table)) :
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left >>= fun value => leftNext value.1 value.2))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right >>= fun value => rightNext value.1 value.2))
      (DirectDetailedOrdinaryRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  have hleftWithSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hleft
      (fun result => result ∈ support
        (runDirectResolvedDetailedFromTable leftContext leftFuel table left))
      (fun result hresult => hresult)
  have hbothWithSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftWithSupport
  apply relTriple_bind hbothWithSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_pure_privateStructuralHit_any table _
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
                (pure (.stopped .ordinaryHit))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure trivial
              | fuelExhausted => exact relTriple_pure_pure trivial
          | done rightResult =>
              simp only
              rw [hrelation.1.1]
              exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
                (pure (.stopped .fuelExhausted))
                (rightNext rightResult.value.1 rightResult.value.2)
                rightResult.context rightResult.remaining hrelation.1.2 hrelation.2
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_pure_nonprivateStop table _ .ordinaryHit (by decide)
          | fuelExhausted =>
              exact relTriple_any_pure_nonprivateStop table _ .fuelExhausted (by decide)
      | done rightResult =>
          rcases hrelation with hcleanRelation | hprivateRelation | hdoomedRelation
          · exact hclean leftResult rightResult hleftSupport hrightSupport hcleanRelation
          · exact hprivate leftResult rightResult hleftSupport hrightSupport hprivateRelation
          · simp only
            rw [hdoomedRelation.1.1]
            exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
              (runDirectResolvedDetailedFromTable leftResult.context leftResult.remaining
                leftResult.table (leftNext leftResult.value.1 leftResult.value.2))
              (rightNext rightResult.value.1 rightResult.value.2)
              rightResult.context rightResult.remaining hdoomedRelation.1.2
                hdoomedRelation.2

def DirectPreservesPrivatePosition
    (position : Position)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table (computation.run cache)) →
    result.context.state.values (.position position) =
        context.state.values (.position position) ∧
      result.context.state.pendingAt (.position position) =
        context.state.pendingAt (.position position) ∧
      result.context.values position = context.values position

theorem directPreservesPrivatePosition_pure
    (position : Position) (value : α) :
    DirectPreservesPrivatePosition position
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro context fuel table cache result hresult
  simp [runDirectResolvedDetailedFromTable] at hresult
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem DirectPreservesPrivatePosition.bind
    {position : Position}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : DirectPreservesPrivatePosition position left)
    (hnext : ∀ value, DirectPreservesPrivatePosition position (next value)) :
    DirectPreservesPrivatePosition position (left >>= next) := by
  intro context fuel table cache result hresult
  change DirectDetailedResult.done result ∈ support
    (runDirectResolvedDetailedFromTable context fuel table
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [runDirectResolvedDetailedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨leftResult, hleftResult, hrest⟩ := hresult
  cases leftResult with
  | stopped reason => simp at hrest
  | done middle =>
      have hmiddle := hleft context fuel table cache middle hleftResult
      have hfinal := hnext middle.value.1 middle.context middle.remaining middle.table
        middle.value.2 result hrest
      exact ⟨hfinal.1.trans hmiddle.1,
        hfinal.2.1.trans hmiddle.2.1,
        hfinal.2.2.trans hmiddle.2.2⟩

theorem runDirectResolvedDetailedFromTable_peek_query_privateHelper
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) :
    runDirectResolvedDetailedFromTable context fuel table
        (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate))) =
      pure (.done ⟨context, fuel, context.state.values coordinate, table⟩) := by
  rw [← bind_pure
    (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
      (.peek coordinate)))]
  rw [runDirectResolvedDetailedFromTable_peek_query_bind,
    runDirectResolvedDetailedFromTable_pure]

theorem runDirectResolvedDetailedFromTable_peekCoordinate_privateHelper
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekCoordinate coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (truncateHash <$> context.state.values coordinate, cache), table⟩) := by
  unfold peekCoordinate
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  unfold LazyRevealProbe.peekQuery
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peek_query_privateHelper]
  simp [runDirectResolvedDetailedFromTable_pure]

theorem directPreservesPrivatePosition_peekCoordinate
    (position : Position) (coordinate : Coordinate) :
    DirectPreservesPrivatePosition position (peekCoordinate coordinate) := by
  intro context fuel table cache result hresult
  rw [runDirectResolvedDetailedFromTable_peekCoordinate_privateHelper] at hresult
  simp at hresult
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem directPreservesPrivatePosition_splitHashQuery
    (position : Position) (key : SplitHashKey) :
    DirectPreservesPrivatePosition position (splitHashQuery key) := by
  intro context fuel table cache result hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      simp only [hlookup] at hresult
      simp [runDirectResolvedDetailedFromTable] at hresult
      subst result
      exact ⟨rfl, rfl, rfl⟩
  | none =>
      simp only [hlookup, LazyRevealProbe.hashOutputQuery,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hrest⟩ := hresult
      simp [runDirectResolvedDetailedFromTable] at hrest
      subst result
      exact ⟨rfl, rfl, rfl⟩

theorem directPreservesPrivatePosition_publishCoordinate
    (position : Position) (coordinate : Coordinate) :
    DirectPreservesPrivatePosition position (publishCoordinate coordinate) := by
  intro context fuel table cache result hresult
  unfold publishCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.publishQuery,
    runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
  simp [runDirectResolvedDetailedFromTable] at hresult
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem directPreservesPrivatePosition_modify
    (position : Position) (update : SplitHashCache → SplitHashCache) :
    DirectPreservesPrivatePosition position
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro context fuel table cache result hresult
  simp [StateT.run_modify, runDirectResolvedDetailedFromTable] at hresult
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem directPreservesPrivatePosition_peekPositionValues
    (position : Position) : ∀ positions : List Position,
    DirectPreservesPrivatePosition position (peekPositionValues positions)
  | [] => directPreservesPrivatePosition_pure position (some [])
  | head :: remaining => by
      rw [peekPositionValues]
      exact (directPreservesPrivatePosition_peekCoordinate position (.position head)).bind
        fun value => match value with
        | none => directPreservesPrivatePosition_pure position none
        | some headValue =>
            (directPreservesPrivatePosition_peekPositionValues position remaining).bind
              fun values => match values with
              | none => directPreservesPrivatePosition_pure position none
              | some tailValues => directPreservesPrivatePosition_pure position
                  (some (headValue :: tailValues))

set_option maxRecDepth 100000 in
theorem directPreservesPrivatePosition_peekTableInput
    (position : Position) (parameter : PublicParameter) (coordinate : Coordinate) :
    DirectPreservesPrivatePosition position (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact directPreservesPrivatePosition_pure position none
  | position outputPosition =>
      cases outputPosition with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact
              (directPreservesPrivatePosition_peekCoordinate position
                (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                  match value with
                  | none => directPreservesPrivatePosition_pure position none
                  | some _ => directPreservesPrivatePosition_pure position (some _)
          · rw [if_neg hzero]
            exact (directPreservesPrivatePosition_peekPositionValues position
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => directPreservesPrivatePosition_pure position none
                | some _ => directPreservesPrivatePosition_pure position (some _)
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp)]
          exact (directPreservesPrivatePosition_peekPositionValues position
            (Position.leaf lay tree leafIdx).children).bind fun values =>
              match values with
              | none => directPreservesPrivatePosition_pure position none
              | some _ => directPreservesPrivatePosition_pure position (some _)
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp)]
          exact (directPreservesPrivatePosition_peekPositionValues position
            (Position.node lay tree level nodeIdx).children).bind fun values =>
              match values with
              | none => directPreservesPrivatePosition_pure position none
              | some _ => directPreservesPrivatePosition_pure position (some _)
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsLeaf index tree leafIdx) (by simp)]
          exact (directPreservesPrivatePosition_peekPositionValues position
            (Position.ftsLeaf index tree leafIdx).children).bind fun values =>
              match values with
              | none => directPreservesPrivatePosition_pure position none
              | some _ => directPreservesPrivatePosition_pure position (some _)
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsNode index tree level nodeIdx) (by simp)]
          exact (directPreservesPrivatePosition_peekPositionValues position
            (Position.ftsNode index tree level nodeIdx).children).bind fun values =>
              match values with
              | none => directPreservesPrivatePosition_pure position none
              | some _ => directPreservesPrivatePosition_pure position (some _)
      | ftsRoots index =>
          rw [peekTableInput.eq_3 parameter (.ftsRoots index) (by simp)]
          exact (directPreservesPrivatePosition_peekPositionValues position
            (Position.ftsRoots index).children).bind fun values =>
              match values with
              | none => directPreservesPrivatePosition_pure position none
              | some _ => directPreservesPrivatePosition_pure position (some _)

set_option maxRecDepth 100000 in
theorem directPreservesPrivatePosition_revealCoordinateOutput_of_ne
    (position : Position) (coordinate : Coordinate)
    (hne : coordinate ≠ .position position) :
    DirectPreservesPrivatePosition position (revealCoordinateOutput coordinate) := by
  intro context fuel table cache result hresult
  unfold revealCoordinateOutput at hresult
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind] at hresult
  simp only [StateT.run_liftM] at hresult
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
  cases hvalue : context.state.values coordinate with
  | some output =>
      simp only [hvalue] at hresult
      simp [StateT.run_modify, runDirectResolvedDetailedFromTable] at hresult
      subst result
      exact ⟨rfl, rfl, rfl⟩
  | none =>
      simp only [hvalue] at hresult
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let output := table ⟨lay, tree, leafIdx, chainIdx⟩
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output
          · simp [output, hhit] at hresult
          · simp only [output, hhit, ↓reduceIte] at hresult
            simp [StateT.run_modify, runDirectResolvedDetailedFromTable] at hresult
            subst result
            refine ⟨?_, ?_, rfl⟩
            · simp [LazyRevealProbe.State.materialize, Function.update_of_ne,
                show Coordinate.position position ≠
                    Coordinate.chainStart lay tree leafIdx chainIdx by simp]
            · change
                (context.state.clearPending (.chainStart lay tree leafIdx chainIdx)).pendingAt
                    (.position position) = context.state.pendingAt (.position position)
              rw [pendingAt_clearPending_of_ne]
              simp
      | position other =>
          have hother : other ≠ position := by
            intro heq
            subst other
            exact hne rfl
          cases hprivate : context.values other with
          | some output =>
              by_cases hhit : context.state.hitAt (.position other) output
              · simp [hprivate, hhit] at hresult
              · simp only [hprivate, hhit, ↓reduceIte] at hresult
                simp [StateT.run_modify, runDirectResolvedDetailedFromTable] at hresult
                subst result
                refine ⟨?_, ?_, ?_⟩
                · simp [LazyRevealProbe.State.materialize, Function.update_of_ne,
                    show Coordinate.position position ≠ Coordinate.position other by
                      simpa using Ne.symm hother]
                · change
                    (context.state.clearPending (.position other)).pendingAt
                        (.position position) = context.state.pendingAt (.position position)
                  exact pendingAt_clearPending_of_ne context.state (.position other)
                    (.position position) (by simpa using Ne.symm hother)
                · rfl
          | none =>
              simp only [hprivate, mem_support_bind_iff] at hresult
              obtain ⟨revealedResult, hreveal, hrest⟩ := hresult
              cases revealedResult with
              | stopped reason => simp at hrest
              | done middle =>
                  obtain ⟨output, _houtput, houtput⟩ := hreveal
                  by_cases hhit : context.state.hitAt (.position other) output
                  · simp [hhit] at houtput
                  · simp only [hhit, ↓reduceIte] at houtput
                    simp [runDirectResolvedDetailedFromTable] at houtput
                    subst middle
                    simp [StateT.run_modify, runDirectResolvedDetailedFromTable] at hrest
                    subst result
                    refine ⟨?_, ?_, ?_⟩
                    · simp [LazyRevealProbe.State.materialize, Function.update_of_ne,
                        show Coordinate.position position ≠ Coordinate.position other by
                          simpa using Ne.symm hother]
                    · change
                        (context.state.clearPending (.position other)).pendingAt
                            (.position position) = context.state.pendingAt (.position position)
                      exact pendingAt_clearPending_of_ne context.state (.position other)
                        (.position position) (by simpa using Ne.symm hother)
                    · simp [DeferredStructuralValues.install,
                        Function.update_of_ne (Ne.symm hother)]

theorem directPreservesPrivatePosition_publishOrdinaryInput
    (position : Position) (coordinate : Coordinate) (input : HashInput)
    (output : HashOutput) :
    DirectPreservesPrivatePosition position
      (publishOrdinaryInput coordinate input output) :=
  (directPreservesPrivatePosition_publishCoordinate position coordinate).bind fun _ =>
    (directPreservesPrivatePosition_modify position fun cache =>
      Function.update cache (.ordinary input) (some output)).bind fun _ =>
        directPreservesPrivatePosition_pure position output

set_option maxRecDepth 100000 in
theorem directPreservesPrivatePosition_resolveKnownInput_of_ne
    (position : Position) (parameter : PublicParameter) (coordinate : Coordinate)
    (input : HashInput) (hne : coordinate ≠ .position position) :
    DirectPreservesPrivatePosition position
      (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  exact (directPreservesPrivatePosition_peekTableInput position parameter coordinate).bind
    fun known => match known with
    | none => directPreservesPrivatePosition_splitHashQuery position (.ordinary input)
    | some knownInput => by
        simp only
        by_cases heq : knownInput = input
        · rw [if_pos heq]
          exact (directPreservesPrivatePosition_revealCoordinateOutput_of_ne position coordinate
            hne).bind fun output =>
              directPreservesPrivatePosition_publishOrdinaryInput position coordinate input output
        · rw [if_neg heq]
          exact directPreservesPrivatePosition_splitHashQuery position (.ordinary input)
theorem relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized
    (table : OtsSecretIndex → HashOutput) (value : α)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((pure value : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) α).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((pure value : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) α).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  rw [StateT.run_pure, StateT.run_pure,
    runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_pure]
  apply relTriple_pure_pure
  left
  exact
    { value_eq := rfl
      context_le := hcontext
      remaining_le := hfuel
      left_table := rfl
      right_table := rfl
      cache_eq := hcache
      revealed_eq := hrevealed
      values_le := hvalues
      left_published := hpublished
      right_materialized := hrightMaterialized }

theorem runDirectResolvedDetailedFromTable_peek_query
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) :
    runDirectResolvedDetailedFromTable context fuel table
        (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate))) =
      pure (.done ⟨context, fuel, context.state.values coordinate, table⟩) := by
  rw [← bind_pure
    (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
      (.peek coordinate)))]
  rw [runDirectResolvedDetailedFromTable_peek_query_bind,
    runDirectResolvedDetailedFromTable_pure]

theorem runDirectResolvedDetailedFromTable_peekCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekCoordinate coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (truncateHash <$> context.state.values coordinate, cache), table⟩) := by
  unfold peekCoordinate
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  unfold LazyRevealProbe.peekQuery
  rw [runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peek_query]
  simp [runDirectResolvedDetailedFromTable_pure]

theorem runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (slot : Nat)
    (coordinate : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((probeFirstMissingInputCoordinate input slot
          (coordinate :: remaining)).run cache) =
      match context.state.values coordinate with
      | none =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probe ⟨coordinate, slotDigest slot input⟩).run cache)
      | some _ =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probeFirstMissingInputCoordinate input (slot + 1) remaining).run cache) := by
  rw [probeFirstMissingInputCoordinate, StateT.run_bind,
    runDirectResolvedDetailedFromTable_bind]
  rw [runDirectResolvedDetailedFromTable_peekCoordinate]
  cases context.state.values coordinate <;> simp

theorem runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values
    (values : Coordinate → HashOutput) (input : HashInput)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) : ∀ (slot : Nat) (coordinates : List Coordinate),
      (∀ coordinate, coordinate ∈ coordinates →
        context.state.values coordinate = some (values coordinate)) →
      runDirectResolvedDetailedFromTable context fuel table
          ((probeFirstMissingInputCoordinate input slot coordinates).run cache) =
        pure (.done ⟨context, fuel, ((), cache), table⟩)
  | _, [], _ => by simp [probeFirstMissingInputCoordinate, runDirectResolvedDetailedFromTable]
  | slot, coordinate :: remaining, hvalues => by
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      rw [hvalues coordinate (by simp)]
      exact runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values values
        input context cache fuel table (slot + 1) remaining
          (fun other hother => hvalues other (by simp [hother]))

set_option maxRecDepth 10000 in
theorem runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
    (values : Coordinate → HashOutput) (input : HashInput)
    (context : DeferredContext) (cache : SplitHashCache)
    (fuel slot : Nat) (prior remaining : List Coordinate) (coordinate : Coordinate)
    (table : OtsSecretIndex → HashOutput)
    (hvalues : ∀ other, other ∈ prior →
      context.state.values other = some (values other))
    (hmissing : context.state.values coordinate = none)
    (hnotRevealed : coordinate ∉ context.state.revealed) :
    runDirectResolvedDetailedFromTable context (fuel + 1) table
        ((probeFirstMissingInputCoordinate input slot
          (prior ++ coordinate :: remaining)).run cache) =
      pure (.done ⟨
        { context with state := (context.state.addPending coordinate
            (slotDigest (slot + prior.length) input)) },
        fuel, ((), cache), table⟩) := by
  induction prior generalizing slot with
  | nil =>
      rw [List.nil_append,
        runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons, hmissing]
      unfold probe
      rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      simp [hnotRevealed, runDirectResolvedDetailedFromTable]
  | cons head tail ih =>
      rw [List.cons_append,
        runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons,
        hvalues head (by simp)]
      have htailValues : ∀ other, other ∈ tail →
          context.state.values other = some (values other) := by
        intro other hother
        exact hvalues other (by simp [hother])
      rw [ih (slot + 1) htailValues]
      simp [Nat.add_comm, Nat.add_left_comm]

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_pure_probe_right
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel + 1 ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hrightMissing : right.state.values coordinate = none) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((pure () : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probe ⟨coordinate, candidate⟩).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : rightFuel ≠ 0)
  unfold probe
  rw [StateT.run_pure, StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_pure,
    runDirectResolvedDetailedFromTable_probe_query_bind]
  have hrightNotRevealed : coordinate ∉ right.state.revealed := by
    intro hrightRevealed
    have hleftRevealed : coordinate ∈ left.state.revealed := by
      rw [hrevealed]
      exact hrightRevealed
    have hleftKnown := hpublished coordinate hleftRevealed
    cases hleftValue : left.state.values coordinate with
    | none => exact hleftKnown hleftValue
    | some output =>
        have hrightValue := hvalues coordinate output hleftValue
        rw [hrightMissing] at hrightValue
        contradiction
  simp only [hrightNotRevealed, ↓reduceIte]
  rw [runDirectResolvedDetailedFromTable_pure]
  apply relTriple_pure_pure
  let nextRight : DeferredContext :=
    { right with state := right.state.addPending coordinate candidate }
  by_cases hcompletable : DeferredCompletable table nextRight
  · left
    exact
      { value_eq := rfl
        context_le := hcontext.addPending_right_of_completable
          coordinate candidate hcompletable
        remaining_le := by
          show leftFuel ≤ remaining
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed
        values_le := hvalues
        left_published := hpublished
        right_materialized := by
          rw [hrightMaterialized]
          simp [directDeferredContext, directDeferredValues_addPending] }
  · right
    right
    refine ⟨⟨rfl, hcontext.view.rightConsistent.addPending coordinate candidate,
      hcontext.view.rightStarts.addPending coordinate candidate, hcompletable⟩, ?_⟩
    change { right with state := right.state.addPending coordinate candidate } =
      directDeferredContext (right.state.addPending coordinate candidate)
    rw [hrightMaterialized]
    simp [directDeferredContext, directDeferredValues_addPending]

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (coordinates : List Coordinate)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      FinalizationContextLE table left right →
      leftFuel + 1 ≤ rightFuel →
      ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
      left.state.revealed = right.state.revealed →
      LazyRevealProbe.ValuesLE left.state right.state →
      PublishedValues left.state →
      right = directDeferredContext right.state →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((pure () : StateT SplitHashCache
            (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hcontext, hfuel, hcache, hrevealed, hvalues, hpublished,
      hrightMaterialized => by
      simpa [probeFirstMissingInputCoordinate] using
        (relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
          left right leftFuel rightFuel leftCache rightCache hcontext (by omega)
          hcache hrevealed hvalues hpublished hrightMaterialized)
  | slot, coordinate :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hcontext, hfuel, hcache, hrevealed, hvalues,
      hpublished, hrightMaterialized => by
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hrightValue : right.state.values coordinate with
      | none =>
          exact relTriple_runDirectResolvedDetailed_pure_probe_right table coordinate
            (slotDigest slot input) left right leftFuel rightFuel leftCache rightCache
              hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
                hrightValue
      | some output =>
          exact relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right table input
            (slot + 1) remaining left right leftFuel rightFuel leftCache rightCache
              hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_aligned
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨coordinate, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probe ⟨coordinate, candidate⟩).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨leftRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : leftFuel ≠ 0)
  obtain ⟨rightRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : rightFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind,
    runDirectResolvedDetailedFromTable_probe_query_bind]
  by_cases hleftRevealed : coordinate ∈ left.state.revealed
  · have hrightRevealed : coordinate ∈ right.state.revealed := by
      rw [← hrevealed]
      exact hleftRevealed
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
    exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
      left right leftRemaining rightRemaining leftCache rightCache hcontext
        (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
  · have hrightRevealed : coordinate ∉ right.state.revealed := by
      rwa [← hrevealed]
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
    let nextLeft : DeferredContext :=
      { left with state := left.state.addPending coordinate candidate }
    let nextRight : DeferredContext :=
      { right with state := right.state.addPending coordinate candidate }
    by_cases hcompletable : DeferredCompletable table nextRight
    · have hnext := hcontext.addPending_both_of_right_completable
        coordinate candidate hcompletable
      have hnextPublished : PublishedValues nextLeft.state := by
        simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
      exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
        nextLeft nextRight leftRemaining rightRemaining leftCache rightCache hnext
          (by omega) hcache hrevealed hvalues hnextPublished (by
            change { right with state := right.state.addPending coordinate candidate } =
              directDeferredContext (right.state.addPending coordinate candidate)
            rw [hrightMaterialized]
            simp [directDeferredContext, directDeferredValues_addPending])
    · rw [runDirectResolvedDetailedFromTable_pure,
        runDirectResolvedDetailedFromTable_pure]
      apply relTriple_pure_pure
      right
      right
      refine ⟨⟨rfl, hcontext.view.rightConsistent.addPending coordinate candidate,
        hcontext.view.rightStarts.addPending coordinate candidate, hcompletable⟩, ?_⟩
      change { right with state := right.state.addPending coordinate candidate } =
        directDeferredContext (right.state.addPending coordinate candidate)
      rw [hrightMaterialized]
      simp [directDeferredContext, directDeferredValues_addPending]

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (coordinates : List Coordinate)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      PrivateStructuralHit left →
      leftFuel + 1 ≤ rightFuel →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((pure () : StateT SplitHashCache
            (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hprivate, hfuel => by
      rw [StateT.run_pure, runDirectResolvedDetailedFromTable_pure]
      simp only [probeFirstMissingInputCoordinate, StateT.run_pure,
        runDirectResolvedDetailedFromTable_pure]
      apply relTriple_pure_pure
      right
      left
      exact hprivate
  | slot, coordinate :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hprivate, hfuel => by
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hrightValue : right.state.values coordinate with
      | some output =>
          exact
            relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
              table input (slot + 1) remaining left right leftFuel rightFuel
                leftCache rightCache hprivate hfuel
      | none =>
          obtain ⟨rightRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (by omega : rightFuel ≠ 0)
          unfold probe
          rw [StateT.run_pure, StateT.run_liftM]
          unfold LazyRevealProbe.probeQuery
          simp only
          rw [runDirectResolvedDetailedFromTable_pure,
            runDirectResolvedDetailedFromTable_probe_query_bind]
          by_cases hrevealed : coordinate ∈ right.state.revealed <;>
            simp only [hrevealed, ↓reduceIte] <;>
            rw [runDirectResolvedDetailedFromTable_pure] <;>
            apply relTriple_pure_pure <;>
            right <;> left <;> exact hprivate

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_private_position_probeFirstMissing_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (slot : Nat)
    (coordinates : List Coordinate) (position : Position)
    (candidate : Digest) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨.position position, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probeFirstMissingInputCoordinate input slot coordinates).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : leftFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind]
  have hleftNotRevealed : Coordinate.position position ∉ left.state.revealed := by
    intro hrevealedPosition
    exact (hpublished (.position position) hrevealedPosition) hhidden
  simp only [hleftNotRevealed, ↓reduceIte]
  let nextLeft : DeferredContext :=
    { left with state := left.state.addPending (.position position) candidate }
  by_cases hhit : truncateHash output = candidate
  · have hprivateHit : PrivateStructuralHit nextLeft :=
      (privateStructuralHit_addPending_iff left position output candidate
        (not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable)
        hhidden hprivate).2 hhit
    exact
      relTriple_runDirectResolvedDetailed_privateHit_pure_probeFirstMissing_right
        table input slot coordinates nextLeft right remaining rightFuel leftCache rightCache
          hprivateHit (by omega)
  · have hnext := hcontext.addPending_left_of_resolved
      (.position position) candidate output (by
        change left.positionValue position = some output
        simp [DeferredContext.positionValue, hhidden, hprivate]) hhit
    have hnextPublished : PublishedValues nextLeft.state := by
      simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
    exact relTriple_runDirectResolvedDetailed_pure_probeFirstMissing_right table input
      slot coordinates nextLeft right remaining rightFuel leftCache rightCache hnext
        (by omega) hcache hrevealed hvalues hnextPublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probeFirstMissing_positions
    (table : OtsSecretIndex → HashOutput) (input : HashInput) :
    ∀ (slot : Nat) (positions : List Position)
      (left right : DeferredContext) (leftFuel rightFuel : Nat)
      (leftCache rightCache : SplitHashCache),
      FinalizationContextLE table left right →
      0 < leftFuel → leftFuel ≤ rightFuel →
      ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
      left.state.revealed = right.state.revealed →
      LazyRevealProbe.ValuesLE left.state right.state →
      PublishedValues left.state →
      right = directDeferredContext right.state →
      RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((probeFirstMissingInputCoordinate input slot
            (positions.map Coordinate.position)).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((probeFirstMissingInputCoordinate input slot
            (positions.map Coordinate.position)).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
  | slot, [], left, right, leftFuel, rightFuel, leftCache, rightCache,
      hcontext, hpositive, hfuel, hcache, hrevealed, hvalues, hpublished,
      hrightMaterialized => by
      simpa [probeFirstMissingInputCoordinate] using
        (relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table ()
          left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
            hrevealed hvalues hpublished hrightMaterialized)
  | slot, position :: remaining, left, right, leftFuel, rightFuel,
      leftCache, rightCache, hcontext, hpositive, hfuel, hcache, hrevealed,
      hvalues, hpublished, hrightMaterialized => by
      simp only [List.map_cons]
      rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons,
        runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_cons]
      cases hleftValue : left.state.values (.position position) with
      | some leftOutput =>
          have hrightValue := hvalues (.position position) leftOutput hleftValue
          rw [hrightValue]
          exact relTriple_runDirectResolvedDetailed_probeFirstMissing_positions table input
            (slot + 1) remaining left right leftFuel rightFuel leftCache rightCache
              hcontext hpositive hfuel hcache hrevealed hvalues hpublished
                hrightMaterialized
      | none =>
          cases hrightValue : right.state.values (.position position) with
          | none =>
              exact relTriple_runDirectResolvedDetailed_probe_aligned table
                (.position position) (slotDigest slot input) left right leftFuel rightFuel
                  leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed
                    hvalues hpublished hrightMaterialized
          | some output =>
              have hprivate :=
                hcontext.view.privateValue_of_left_hidden_of_right_materialized
                  position output hleftValue hrightValue
              exact
                relTriple_runDirectResolvedDetailed_probe_private_position_probeFirstMissing_right
                  table input (slot + 1) (remaining.map Coordinate.position) position
                    (slotDigest slot input) output left right leftFuel rightFuel
                      leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed
                        hvalues hpublished hrightMaterialized hleftValue hprivate

theorem runDirectResolvedDetailedFromTable_prepareLeafInputProbe
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache) =
      match context.state.values candidate.coordinate with
      | none =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probe candidate).run cache)
      | some _ =>
          runDirectResolvedDetailedFromTable context fuel table
            ((probeFirstMissingInputCoordinate input 0
              ((Position.leaf lay tree leafIdx).children.map
                Coordinate.position)).run cache) := by
  unfold prepareLeafInputProbe
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekCoordinate]
  cases context.state.values candidate.coordinate <;> simp

theorem runDirectResolvedDetailedFromTable_peekPositionValues_of_values
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ∀ positions : List Position,
      (∀ position, position ∈ positions →
        context.state.values (.position position) = some (completion (.position position))) →
      runDirectResolvedDetailedFromTable context fuel table
          ((peekPositionValues positions).run cache) =
        pure (.done ⟨context, fuel,
          (some (positions.map (tableValue completion)), cache), table⟩)
  | [], _ => by simp [peekPositionValues, runDirectResolvedDetailedFromTable]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate]
      rw [hvalues position (by simp)]
      rw [show truncateHash <$> some (completion (.position position)) =
        some (tableValue completion position) by rfl]
      simp only [pure_bind]
      rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context fuel
          table cache remaining (fun other hother => hvalues other (by simp [hother]))]
      simp [runDirectResolvedDetailedFromTable, tableValue]

theorem runDirectResolvedDetailedFromTable_peekPositionValues_of_prefix_values_of_missing
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (prior remaining : List Position) (position : Position)
    (hvalues : ∀ other, other ∈ prior →
      context.state.values (.position other) = some (completion (.position other)))
    (hmissing : context.state.values (.position position) = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekPositionValues (prior ++ position :: remaining)).run cache) =
      pure (.done ⟨context, fuel, (none, cache), table⟩) := by
  induction prior with
  | nil =>
      rw [List.nil_append, peekPositionValues, StateT.run_bind,
        runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate, hmissing]
      simp [runDirectResolvedDetailedFromTable]
  | cons head tail ih =>
      rw [List.cons_append, peekPositionValues, StateT.run_bind,
        runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate,
        hvalues head (by simp)]
      rw [show truncateHash <$> some (completion (.position head)) =
        some (tableValue completion head) by rfl]
      simp only [pure_bind]
      rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        ih (fun other hother => hvalues other (by simp [hother]))]
      simp [runDirectResolvedDetailedFromTable]

theorem runDirectResolvedDetailedFromTable_peekTableInput_of_available
    (parameter : PublicParameter) (completion : Coordinate → HashOutput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (havailable : TableInputAvailable completion context.state coordinate) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (some (tableInput parameter completion coordinate), cache), table⟩) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekCoordinate]
            rw [show context.state.values (.chainStart lay tree leafIdx chainIdx) =
                some (completion (.chainStart lay tree leafIdx chainIdx)) by
              simpa [TableInputAvailable, hzero] using havailable]
            simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload, hzero]
          · rw [if_neg hzero, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
                fuel table cache _ (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload, hzero]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
              fuel table cache _ havailable]
          simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
              fuel table cache _ havailable]
          simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload]
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsLeaf index tree leafIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
              fuel table cache _ havailable]
          simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload]
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsNode index tree level nodeIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
              fuel table cache _ havailable]
          simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload]
      | ftsRoots index =>
          rw [peekTableInput.eq_3 parameter (.ftsRoots index) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_of_values completion context
              fuel table cache _ havailable]
          simp [runDirectResolvedDetailedFromTable, tableInput, tablePayload]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_peekTableInput_of_unavailable
    (parameter : PublicParameter) (completion : Coordinate → HashOutput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hcompletion : DeferredCompletion table context completion)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hunavailable : ¬TableInputAvailable completion context.state coordinate) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (.done ⟨context, fuel, (none, cache), table⟩) := by
  have htable : ∀ coordinate output,
      context.state.values coordinate = some output → output = completion coordinate := by
    intro other output hvalue
    exact (hcompletion.1 other output hvalue).symm
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [peekTableInput, runDirectResolvedDetailedFromTable]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
            have hnone : context.state.values (.chainStart lay tree leafIdx chainIdx) = none := by
              cases hvalue : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | none => rfl
              | some output =>
                  have hsame := htable (.chainStart lay tree leafIdx chainIdx) output hvalue
                  exfalso
                  apply hunavailable
                  simpa [TableInputAvailable, hzero, hsame] using hvalue
            rw [runDirectResolvedDetailedFromTable_peekCoordinate, hnone]
            simp [runDirectResolvedDetailedFromTable]
          · rw [if_neg hzero, StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
            rcases positionValues_or_first_missing completion context.state
              (Position.chain lay tree leafIdx chainIdx step).children
              (fun other output hvalue =>
                htable (.position other) output hvalue) with havailable |
                ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
            · exact (hunavailable (by simpa [TableInputAvailable, hzero] using havailable)).elim
            · rw [hchildren,
                runDirectResolvedDetailedFromTable_peekPositionValues_of_prefix_values_of_missing
                  completion context fuel table cache prior remaining child hvalues hmissing]
              simp [runDirectResolvedDetailedFromTable]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
          rcases positionValues_or_first_missing completion context.state
            (Position.leaf lay tree leafIdx).children (fun other output hvalue =>
              htable (.position other) output hvalue) with havailable |
              ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
          · exact (hunavailable havailable).elim
          · rw [hchildren,
              runDirectResolvedDetailedFromTable_peekPositionValues_of_prefix_values_of_missing
                completion context fuel table cache prior remaining child hvalues hmissing]
            simp [runDirectResolvedDetailedFromTable]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
          rcases positionValues_or_first_missing completion context.state
            (Position.node lay tree level nodeIdx).children (fun other output hvalue =>
              htable (.position other) output hvalue) with havailable |
              ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
          · exact (hunavailable havailable).elim
          · rw [hchildren,
              runDirectResolvedDetailedFromTable_peekPositionValues_of_prefix_values_of_missing
                completion context fuel table cache prior remaining child hvalues hmissing]
            simp [runDirectResolvedDetailedFromTable]
      | ftsLeaf index tree leafIdx => simpa [IsOtsPosition] using hots _ rfl
      | ftsNode index tree level nodeIdx => simpa [IsOtsPosition] using hots _ rfl
      | ftsRoots index => simpa [IsOtsPosition] using hots _ rfl

theorem runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (output : HashOutput)
    (hvalue : context.state.values coordinate = some output) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealCoordinateOutput coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (output, Function.update cache (.hidden coordinate) (some output)), table⟩) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedDetailedFromTable_reveal_query_bind, hvalue]
  simp [StateT.run_modify, runDirectResolvedDetailedFromTable]

theorem runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_private
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (output : HashOutput)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealCoordinateOutput (.position position)).run cache) =
      if context.state.hitAt (.position position) output then
        pure (.stopped .privateStructuralHit)
      else
        pure (.done ⟨
          { state := context.state.materialize (.position position) output
            values := context.values },
          fuel,
          (output, Function.update cache (.hidden (.position position)) (some output)),
          table⟩) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedDetailedFromTable_reveal_query_bind]
  by_cases hhit : context.state.hitAt (.position position) output <;>
    simp [hhidden, hprivate, hhit, StateT.run_modify,
      runDirectResolvedDetailedFromTable]

theorem runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealCoordinateOutput (.position position)).run cache) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then
        pure (.stopped .ordinaryHit)
      else
        pure (.done ⟨
          { state := context.state.materialize (.position position) output
            values := context.values.install position output },
          fuel,
          (output, Function.update cache (.hidden (.position position)) (some output)),
          table⟩)) := by
  unfold revealCoordinateOutput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM]
  rw [LazyRevealProbe.revealQuery,
    runDirectResolvedDetailedFromTable_reveal_query_bind]
  simp [hhidden, hprivate, StateT.run_modify, runDirectResolvedDetailedFromTable]
  apply bind_congr
  intro output
  by_cases hhit : context.state.hitAt (.position position) output <;> simp [hhit]

theorem runDirectResolvedDetailedFromTable_publishOrdinaryInput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (output : HashOutput) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((publishOrdinaryInput coordinate input output).run cache) =
      pure (.done ⟨
        { context with state := context.state.publish coordinate },
        fuel,
        (output, Function.update cache (.ordinary input) (some output)),
        table⟩) := by
  unfold publishOrdinaryInput publishCoordinate
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  simp only [StateT.run_liftM, LazyRevealProbe.publishQuery]
  rw [runDirectResolvedDetailedFromTable_publish_query_bind]
  simp [StateT.run_modify, runDirectResolvedDetailedFromTable]

noncomputable def revealPublishOrdinaryInput
    (coordinate : Coordinate) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  let output ← revealCoordinateOutput coordinate
  publishOrdinaryInput coordinate input output

theorem runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_of_value
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (output : HashOutput)
    (hvalue : context.state.values coordinate = some output) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealPublishOrdinaryInput coordinate input).run cache) =
      pure (.done ⟨
        { context with state := context.state.publish coordinate },
        fuel,
        (output, Function.update
          (Function.update cache (.hidden coordinate) (some output))
          (.ordinary input) (some output)),
        table⟩) := by
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table coordinate
      context fuel cache output hvalue]
  simp only [pure_bind]
  rw [runDirectResolvedDetailedFromTable_publishOrdinaryInput]

theorem runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_position_of_private
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (output : HashOutput)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealPublishOrdinaryInput (.position position) input).run cache) =
      if context.state.hitAt (.position position) output then
        pure (.stopped .privateStructuralHit)
      else
        pure (.done ⟨
          { state := (context.state.materialize (.position position) output).publish
              (.position position)
            values := context.values },
          fuel,
          (output, Function.update
            (Function.update cache (.hidden (.position position)) (some output))
            (.ordinary input) (some output)),
          table⟩) := by
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_private table position
      context fuel cache output hhidden hprivate]
  by_cases hhit : context.state.hitAt (.position position) output <;> simp [hhit]
  rw [runDirectResolvedDetailedFromTable_publishOrdinaryInput]

theorem runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_position_of_fresh
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((revealPublishOrdinaryInput (.position position) input).run cache) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then
        pure (.stopped .ordinaryHit)
      else
        pure (.done ⟨
          { state := (context.state.materialize (.position position) output).publish
              (.position position)
            values := context.values.install position output },
          fuel,
          (output, Function.update
            (Function.update cache (.hidden (.position position)) (some output))
            (.ordinary input) (some output)),
          table⟩)) := by
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh table position
      context fuel cache hhidden hprivate]
  rw [bind_assoc]
  apply bind_congr
  intro output
  by_cases hhit : context.state.hitAt (.position position) output
  · simp [hhit]
  · simp only [hhit, ↓reduceIte, pure_bind]
    rw [runDirectResolvedDetailedFromTable_publishOrdinaryInput]

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary
    (table : OtsSecretIndex → HashOutput) (input : HashInput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((splitHashQuery (.ordinary input)).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((splitHashQuery (.ordinary input)).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hcacheAt : leftCache (.ordinary input) = rightCache (.ordinary input) :=
    congrFun hcache input
  cases hlookup : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table output
        left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
          hvalues hpublished hrightMaterialized
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hcacheAt]
        exact hlookup
      simp only [hright]
      rw [LazyRevealProbe.hashOutputQuery,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind,
        runDirectResolvedDetailedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runDirectResolvedDetailedFromTable]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]
          revealed_eq := hrevealed
          values_le := hvalues
          left_published := hpublished
          right_materialized := hrightMaterialized }

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_splitHashQuery_private_left_materialized_right
    (table : OtsSecretIndex → HashOutput) (input : HashInput)
    (left : DeferredContext) (leftFuel : Nat) (leftCache : SplitHashCache)
    (rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (HashOutput × SplitHashCache))
    (right : DeferredContext) (rightFuel : Nat)
    (hprivate : PrivateStructuralHit left)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((splitHashQuery (.ordinary input)).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectDetailedOrdinaryRunEq table) := by
  have hbase := relTriple_true
    (runDirectResolvedDetailedFromTable left leftFuel table
      ((splitHashQuery (.ordinary input)).run leftCache))
    (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((splitHashQuery (.ordinary input)).run leftCache)))
      (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_post_mono hbothSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨_trivial, hleftResult⟩, hrightResult⟩
  have hleftDone : ∃ result, leftResult = .done result ∧ result.context = left := by
    rw [splitHashQuery_run_eq] at hleftResult
    cases hlookup : leftCache (.ordinary input) with
    | some output =>
        simp only [hlookup] at hleftResult
        simp [runDirectResolvedDetailedFromTable] at hleftResult
        subst leftResult
        exact ⟨_, rfl, rfl⟩
    | none =>
        simp only [hlookup, LazyRevealProbe.hashOutputQuery,
          runDirectResolvedDetailedFromTable_hashOutput_query_bind,
          mem_support_bind_iff] at hleftResult
        obtain ⟨output, _houtput, hrest⟩ := hleftResult
        simp [runDirectResolvedDetailedFromTable] at hrest
        subst leftResult
        exact ⟨_, rfl, rfl⟩
  obtain ⟨leftRunResult, rfl, hleftContext⟩ := hleftDone
  have hrightShape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    rightComputation right.state rightFuel table rightResult (by
      rw [← hrightMaterialized]
      exact hrightResult)
  cases rightResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => contradiction
      | ordinaryHit => trivial
      | fuelExhausted => trivial
  | done rightRunResult =>
      right
      left
      rwa [hleftContext]

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_revealCoordinateOutput_position
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((revealCoordinateOutput (.position position)).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((revealCoordinateOutput (.position position)).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases hleftValue : left.state.values (.position position) with
  | some output =>
      have hrightValue : right.state.values (.position position) = some output :=
        hvalues (.position position) output hleftValue
      rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
          (.position position) left leftFuel leftCache output hleftValue,
        runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
          (.position position) right rightFuel rightCache output hrightValue]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
          revealed_eq := hrevealed
          values_le := hvalues
          left_published := hpublished
          right_materialized := hrightMaterialized }
  | none =>
      cases hrightValue : right.state.values (.position position) with
      | some output =>
          have hprivate := hcontext.view.privateValue_of_left_hidden_of_right_materialized
            position output hleftValue hrightValue
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_private
              table position left leftFuel leftCache output hleftValue hprivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_of_value table
              (.position position) right rightFuel rightCache output hrightValue]
          by_cases hhit : left.state.hitAt (.position position) output
          · simp only [hhit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · simp only [hhit, ↓reduceIte]
            apply relTriple_pure_pure
            left
            exact
              { value_eq := rfl
                context_le := hcontext.materialize_position_left position output
                  hleftValue hprivate
                remaining_le := hfuel
                left_table := rfl
                right_table := rfl
                cache_eq := by
                  rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
                revealed_eq := by
                  simpa [LazyRevealProbe.State.materialize] using hrevealed
                values_le := hvalues.materialize_left (.position position) output hrightValue
                left_published := hpublished.materialize (.position position) output
                right_materialized := hrightMaterialized }
      | none =>
          have hrightPrivate : right.values position = none := by
            rw [hrightMaterialized]
            simpa [directDeferredContext, directDeferredValues] using hrightValue
          have hleftPositionValue : left.positionValue position = none := by
            change resolvedCompletionValue table left (.position position) = none
            rw [hcontext.view.valueEq]
            simp [resolvedCompletionValue, DeferredContext.positionValue, hrightValue,
              hrightPrivate]
          have hleftPrivate : left.values position = none := by
            simpa [DeferredContext.positionValue, hleftValue] using hleftPositionValue
          rw [runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
              table position left leftFuel leftCache hleftValue hleftPrivate,
            runDirectResolvedDetailedFromTable_revealCoordinateOutput_position_of_fresh
              table position right rightFuel rightCache hrightValue hrightPrivate]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hleftHit : left.state.hitAt (.position position) leftOutput
          · have hresolvedNone :
                resolvedCompletionValue table left (.position position) = none := by
              simpa [resolvedCompletionValue] using hleftPositionValue
            have hrightHit : right.state.hitAt (.position position) leftOutput := by
              unfold LazyRevealProbe.State.hitAt at hleftHit ⊢
              exact hcontext.view.pendingLE (.position position) hresolvedNone hleftHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · by_cases hrightHit : right.state.hitAt (.position position) leftOutput
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              exact relTriple_pure_pure trivial
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              apply relTriple_pure_pure
              left
              exact
                { value_eq := rfl
                  context_le := hcontext.materialize_position_both position leftOutput
                  remaining_le := hfuel
                  left_table := rfl
                  right_table := rfl
                  cache_eq := by
                    rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
                      hcache]
                  revealed_eq := by
                    simpa [LazyRevealProbe.State.materialize] using hrevealed
                  values_le := hvalues.materialize_both (.position position) leftOutput
                  left_published := hpublished.materialize (.position position) leftOutput
                  right_materialized := by
                    rw [hrightMaterialized]
                    simp [directDeferredContext, directDeferredValues_materialize_position] }

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_revealPublishOrdinaryInput_position
    (table : OtsSecretIndex → HashOutput) (position : Position) (input : HashInput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((revealPublishOrdinaryInput (.position position) input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((revealPublishOrdinaryInput (.position position) input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases hleftValue : left.state.values (.position position) with
  | some output =>
      have hrightValue : right.state.values (.position position) = some output :=
        hvalues (.position position) output hleftValue
      rw [runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_of_value table
          (.position position) input left leftFuel leftCache output hleftValue,
        runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_of_value table
          (.position position) input right rightFuel rightCache output hrightValue]
      apply relTriple_pure_pure
      left
      exact
        { value_eq := rfl
          context_le := hcontext.publish (.position position)
          remaining_le := hfuel
          left_table := rfl
          right_table := rfl
          cache_eq := by
            rw [ordinaryQueryCache_update, ordinaryQueryCache_update,
              ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
          revealed_eq := by
            simpa [LazyRevealProbe.State.publish] using
              congrArg (insert (.position position)) hrevealed
          values_le := hvalues
          left_published :=
            hpublished.publish_of_value (.position position) output hleftValue
          right_materialized := by
            rw [hrightMaterialized]
            simp [directDeferredContext, directDeferredValues_publish] }
  | none =>
      cases hrightValue : right.state.values (.position position) with
      | some output =>
          have hprivate := hcontext.view.privateValue_of_left_hidden_of_right_materialized
            position output hleftValue hrightValue
          rw [runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_position_of_private
              table position input left leftFuel leftCache output hleftValue hprivate,
            runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_of_value table
              (.position position) input right rightFuel rightCache output hrightValue]
          by_cases hhit : left.state.hitAt (.position position) output
          · simp only [hhit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · simp only [hhit, ↓reduceIte]
            apply relTriple_pure_pure
            left
            exact
              { value_eq := rfl
                context_le :=
                  (hcontext.materialize_position_left position output hleftValue hprivate).publish
                    (.position position)
                remaining_le := hfuel
                left_table := rfl
                right_table := rfl
                cache_eq := by
                  rw [ordinaryQueryCache_update, ordinaryQueryCache_update,
                    ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]
                revealed_eq := by
                  simpa [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish] using
                    congrArg (insert (.position position)) hrevealed
                values_le := hvalues.materialize_left (.position position) output hrightValue
                left_published :=
                  (hpublished.materialize (.position position) output).publish_of_value
                    (.position position) output (by
                      simp [LazyRevealProbe.State.materialize])
                right_materialized := by
                  rw [hrightMaterialized]
                  simp [directDeferredContext, directDeferredValues_publish] }
      | none =>
          have hrightPrivate : right.values position = none := by
            rw [hrightMaterialized]
            simpa [directDeferredContext, directDeferredValues] using hrightValue
          have hleftPositionValue : left.positionValue position = none := by
            change resolvedCompletionValue table left (.position position) = none
            rw [hcontext.view.valueEq]
            simp [resolvedCompletionValue, DeferredContext.positionValue, hrightValue,
              hrightPrivate]
          have hleftPrivate : left.values position = none := by
            simpa [DeferredContext.positionValue, hleftValue] using hleftPositionValue
          rw [runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_position_of_fresh
              table position input left leftFuel leftCache hleftValue hleftPrivate,
            runDirectResolvedDetailedFromTable_revealPublishOrdinaryInput_position_of_fresh
              table position input right rightFuel rightCache hrightValue hrightPrivate]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hleftHit : left.state.hitAt (.position position) leftOutput
          · have hresolvedNone :
                resolvedCompletionValue table left (.position position) = none := by
              simpa [resolvedCompletionValue] using hleftPositionValue
            have hrightHit : right.state.hitAt (.position position) leftOutput := by
              unfold LazyRevealProbe.State.hitAt at hleftHit ⊢
              exact hcontext.view.pendingLE (.position position) hresolvedNone hleftHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            exact relTriple_pure_pure trivial
          · by_cases hrightHit : right.state.hitAt (.position position) leftOutput
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              exact relTriple_pure_pure trivial
            · simp only [hleftHit, hrightHit, ↓reduceIte]
              apply relTriple_pure_pure
              left
              exact
                { value_eq := rfl
                  context_le :=
                    (hcontext.materialize_position_both position leftOutput).publish
                      (.position position)
                  remaining_le := hfuel
                  left_table := rfl
                  right_table := rfl
                  cache_eq := by
                    rw [ordinaryQueryCache_update, ordinaryQueryCache_update,
                      ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden,
                      hcache]
                  revealed_eq := by
                    simpa [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish] using
                      congrArg (insert (.position position)) hrevealed
                  values_le := hvalues.materialize_both (.position position) leftOutput
                  left_published :=
                    (hpublished.materialize (.position position) leftOutput).publish_of_value
                      (.position position) leftOutput (by
                        simp [LazyRevealProbe.State.materialize])
                  right_materialized := by
                    rw [hrightMaterialized]
                    simp [directDeferredContext, directDeferredValues_materialize_position,
                      directDeferredValues_publish] }

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_resolveKnownInput_available
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (input : HashInput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (completion : Coordinate → HashOutput)
    (havailable : TableInputAvailable completion left.state (.position position))
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((resolveKnownInput parameter (.position position) input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((resolveKnownInput parameter (.position position) input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  have hrightAvailable :
      TableInputAvailable completion right.state (.position position) :=
    havailable.monoValues hvalues
  unfold resolveKnownInput
  rw [StateT.run_bind, StateT.run_bind,
    runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekTableInput_of_available parameter completion left
      leftFuel table leftCache (.position position) havailable,
    runDirectResolvedDetailedFromTable_peekTableInput_of_available parameter completion right
      rightFuel table rightCache (.position position) hrightAvailable]
  simp only [pure_bind]
  by_cases heq : tableInput parameter completion (.position position) = input
  · simp only [heq, ↓reduceIte]
    simpa [revealPublishOrdinaryInput, publishOrdinaryInput] using
      relTriple_runDirectResolvedDetailed_revealPublishOrdinaryInput_position table position
        input left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
          hvalues hpublished hrightMaterialized
  · simp only [heq, ↓reduceIte]
    exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
      left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
        hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hordinary : CompletionOrdinaryInput parameter table left input) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((resolveKnownInput parameter coordinate input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((resolveKnownInput parameter coordinate input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨completion, hrightCompletion⟩ := hcontext.rightCompletable
  have hleftCompletion : DeferredCompletion table left completion :=
    hcontext.view.deferredCompletion_left completion hrightCompletion
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      unfold resolveKnownInput
      simp only [peekTableInput, pure_bind]
      exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
        left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
          hvalues hpublished hrightMaterialized
  | position position =>
      have hotsPosition : IsOtsPosition position := hots position rfl
      unfold resolveKnownInput
      rw [StateT.run_bind, StateT.run_bind,
        runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_bind]
      by_cases hleftAvailable :
          TableInputAvailable completion left.state (.position position)
      · have hrightAvailable :
            TableInputAvailable completion right.state (.position position) :=
          hleftAvailable.monoValues hvalues
        rw [runDirectResolvedDetailedFromTable_peekTableInput_of_available parameter completion
            left leftFuel table leftCache (.position position) hleftAvailable,
          runDirectResolvedDetailedFromTable_peekTableInput_of_available parameter completion
            right rightFuel table rightCache (.position position) hrightAvailable]
        simp only [pure_bind]
        have hne : tableInput parameter completion (.position position) ≠ input := by
          intro heq
          exact hordinary completion hleftCompletion position hotsPosition heq.symm
        rw [if_neg hne]
        exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
          left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
            hvalues hpublished hrightMaterialized
      · rw [runDirectResolvedDetailedFromTable_peekTableInput_of_unavailable parameter completion
          left leftFuel table leftCache (.position position) hleftCompletion
            (fun other heq => by cases heq; exact hotsPosition) hleftAvailable]
        simp only [pure_bind]
        by_cases hrightAvailable :
            TableInputAvailable completion right.state (.position position)
        · rw [runDirectResolvedDetailedFromTable_peekTableInput_of_available parameter completion
            right rightFuel table rightCache (.position position) hrightAvailable]
          simp only [pure_bind]
          have hne : tableInput parameter completion (.position position) ≠ input := by
            intro heq
            exact hordinary completion hleftCompletion position hotsPosition heq.symm
          rw [if_neg hne]
          exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
            left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
              hvalues hpublished hrightMaterialized
        · rw [runDirectResolvedDetailedFromTable_peekTableInput_of_unavailable parameter completion
            right rightFuel table rightCache (.position position) hrightCompletion
              (fun other heq => by cases heq; exact hotsPosition) hrightAvailable]
          simp only [pure_bind]
          exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
            left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
              hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_prepareLeafInputProbe
    (table : OtsSecretIndex → HashOutput) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (position : Position)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcoordinate : candidate.coordinate = .position position)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  have hcandidate : candidate = ⟨.position position, candidate.candidate⟩ := by
    rcases candidate with ⟨coordinate, candidateDigest⟩
    simp only at hcoordinate ⊢
    subst coordinate
    rfl
  rw [runDirectResolvedDetailedFromTable_prepareLeafInputProbe,
    runDirectResolvedDetailedFromTable_prepareLeafInputProbe]
  cases hleftValue : left.state.values candidate.coordinate with
  | some leftOutput =>
      have hrightValue := hvalues candidate.coordinate leftOutput hleftValue
      rw [hrightValue]
      exact relTriple_runDirectResolvedDetailed_probeFirstMissing_positions table input
        0 (Position.leaf lay tree leafIdx).children left right leftFuel rightFuel
          leftCache rightCache hcontext hpositive hfuel hcache hrevealed hvalues hpublished
            hrightMaterialized
  | none =>
      cases hrightValue : right.state.values candidate.coordinate with
      | none =>
          exact relTriple_runDirectResolvedDetailed_probe_aligned table
            candidate.coordinate candidate.candidate left right leftFuel rightFuel
              leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed hvalues
                hpublished hrightMaterialized
      | some output =>
          have hleftPosition : left.state.values (.position position) = none := by
            simpa [hcoordinate] using hleftValue
          have hrightPosition : right.state.values (.position position) = some output := by
            simpa [hcoordinate] using hrightValue
          have hprivate :=
            hcontext.view.privateValue_of_left_hidden_of_right_materialized position output
              hleftPosition hrightPosition
          rw [hcandidate]
          exact
            relTriple_runDirectResolvedDetailed_probe_private_position_probeFirstMissing_right
              table input 0
              ((Position.leaf lay tree leafIdx).children.map Coordinate.position)
              position candidate.candidate output left right leftFuel rightFuel
                leftCache rightCache hcontext ⟨hpositive, hfuel⟩ hcache hrevealed hvalues
                  hpublished hrightMaterialized hleftPosition hprivate

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probe_skip_private_position
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (candidate : Digest) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : 0 < leftFuel ∧ leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : left.state.values (.position position) = none)
    (hprivate : left.values position = some output) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probe ⟨.position position, candidate⟩).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((pure () : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : leftFuel ≠ 0)
  unfold probe
  rw [StateT.run_liftM, StateT.run_pure]
  unfold LazyRevealProbe.probeQuery
  simp only
  rw [runDirectResolvedDetailedFromTable_probe_query_bind,
    runDirectResolvedDetailedFromTable_pure]
  have hleftNotRevealed : Coordinate.position position ∉ left.state.revealed := by
    intro hrevealedPosition
    exact (hpublished (.position position) hrevealedPosition) hhidden
  simp only [hleftNotRevealed, ↓reduceIte]
  apply relTriple_pure_pure
  by_cases hhit : truncateHash output = candidate
  · right
    left
    exact (privateStructuralHit_addPending_iff left position output candidate
      (not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable)
      hhidden hprivate).2 hhit
  · left
    exact
      { value_eq := rfl
        context_le := hcontext.addPending_left_of_resolved
          (.position position) candidate output (by
            change left.positionValue position = some output
            simp [DeferredContext.positionValue, hhidden, hprivate]) hhit
        remaining_le := by
          show remaining ≤ rightFuel
          omega
        left_table := rfl
        right_table := rfl
        cache_eq := hcache
        revealed_eq := hrevealed
        values_le := hvalues
        left_published := hpublished
        right_materialized := hrightMaterialized }

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingHashQuery_chain
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
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
        ((probingHashQuery parameter input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQuery parameter input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hprobe
  have houtput := decodeProbe?_outputCoordinate_eq_position parameter input candidate
    (.chain lay tree leafIdx chainIdx step) hprobe hposition
  obtain ⟨leftRemaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : leftFuel ≠ 0)
  obtain ⟨rightRemaining, hrightFuel⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : rightFuel ≠ 0)
  subst rightFuel
  have hremaining : leftRemaining ≤ rightRemaining := by omega
  unfold probingHashQuery
  rw [hprobe, hposition]
  simp only
  rw [StateT.run_bind, StateT.run_bind,
    runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_bind]
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.probeQuery,
    runDirectResolvedDetailedFromTable_probe_query_bind,
    runDirectResolvedDetailedFromTable_probe_query_bind]
  by_cases hleftNotRevealed : candidate.coordinate ∉ left.state.revealed
  · have hrightNotRevealed : candidate.coordinate ∉ right.state.revealed := by
      rwa [← hrevealed]
    simp only [hleftNotRevealed, hrightNotRevealed, ↓reduceIte,
      runDirectResolvedDetailedFromTable]
    let nextLeft : DeferredContext :=
      { left with state := left.state.addPending candidate.coordinate candidate.candidate }
    let nextRight : DeferredContext :=
      { right with state := right.state.addPending candidate.coordinate candidate.candidate }
    by_cases hnextCompletable : DeferredCompletable table nextRight
    · have hnextContext : FinalizationContextLE table nextLeft nextRight :=
        hcontext.addPending_both_of_right_completable candidate.coordinate
          candidate.candidate hnextCompletable
      have hpending : (candidate.coordinate, candidate.candidate) ∈
          nextLeft.state.pending := by
        simp [nextLeft, LazyRevealProbe.State.addPending]
      have hordinary := completionOrdinaryInput_of_pending_decodedProbe (table := table)
        hprobe hpending
      have hnextRightMaterialized :
          nextRight = directDeferredContext nextRight.state := by
        unfold nextRight
        rw [hrightMaterialized]
        simp only [directDeferredContext, directDeferredValues_addPending]
      rw [houtput]
      exact relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
        parameter table (.position (.chain lay tree leafIdx chainIdx step)) input
          nextLeft nextRight leftRemaining rightRemaining leftCache rightCache hnextContext
            hremaining hcache hrevealed hvalues
              (by simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using
                hpublished)
              hnextRightMaterialized
              (fun position heq => by cases heq; simp [IsOtsPosition]) hordinary
    · have hnextDoomed : DoomedResolvedContext table nextRight :=
        ⟨hcontext.view.rightConsistent.addPending candidate.coordinate candidate.candidate,
          hcontext.view.rightStarts.addPending candidate.coordinate candidate.candidate,
          hnextCompletable⟩
      have hnextRightMaterialized :
          nextRight = directDeferredContext nextRight.state := by
        unfold nextRight
        rw [hrightMaterialized]
        simp only [directDeferredContext, directDeferredValues_addPending]
      exact relTriple_runDirectResolvedDetailed_of_right_materializedDoomed table
        (runDirectResolvedDetailedFromTable nextLeft leftRemaining table
          ((resolveKnownInput parameter candidate.outputCoordinate input).run leftCache))
        ((resolveKnownInput parameter candidate.outputCoordinate input).run rightCache)
        nextRight rightRemaining hnextDoomed hnextRightMaterialized
  · have hleftRevealed : candidate.coordinate ∈ left.state.revealed := by
      simpa using hleftNotRevealed
    have hrightRevealed : candidate.coordinate ∈ right.state.revealed := by
      rwa [← hrevealed]
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
      runDirectResolvedDetailedFromTable]
    obtain ⟨completion, hrightCompletion⟩ := hcontext.rightCompletable
    have hleftCompletion :=
      hcontext.view.deferredCompletion_left completion hrightCompletion
    have havailable := tableInputAvailable_chain_of_probe_revealed hleftCompletion hpublished
      hmatches houtput hleftRevealed
    rw [houtput]
    exact relTriple_runDirectResolvedDetailed_resolveKnownInput_available parameter table
      (.chain lay tree leafIdx chainIdx step) input left right leftRemaining rightRemaining
        leftCache rightCache completion havailable hcontext hremaining hcache hrevealed hvalues
          hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem preparedLeaf_available_or_completionOrdinary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input = some (.leaf lay tree leafIdx))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion)
    (hpositive : 0 < fuel) (hpublished : PublishedValues context.state)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache))) :
    TableInputAvailable completion result.context.state
        (.position (.leaf lay tree leafIdx)) ∨
      CompletionOrdinaryInput parameter table result.context input := by
  obtain ⟨remainingFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [runDirectResolvedDetailedFromTable_prepareLeafInputProbe] at hresult
  cases hsourceValue : context.state.values candidate.coordinate with
  | none =>
      rw [hsourceValue] at hresult
      have hnotRevealed : candidate.coordinate ∉ context.state.revealed := by
        intro hrevealed
        exact (hpublished candidate.coordinate hrevealed) hsourceValue
      unfold probe at hresult
      rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
      simp [hnotRevealed, runDirectResolvedDetailedFromTable] at hresult
      subst result
      right
      apply completionOrdinaryInput_of_pending_decodedProbe (table := table) hprobe
      simp [LazyRevealProbe.State.addPending]
  | some sourceOutput =>
      rw [hsourceValue] at hresult
      rcases positionValues_or_first_missing completion context.state
        (Position.leaf lay tree leafIdx).children
        (fun other output hvalue => (hcompletion.1 (.position other) output hvalue).symm) with
        havailable | ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
      · let coordinates := (Position.leaf lay tree leafIdx).children.map Coordinate.position
        have hcoordinateValues : ∀ coordinate, coordinate ∈ coordinates →
            context.state.values coordinate = some (completion coordinate) := by
          intro coordinate hcoordinate
          obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
          exact havailable position hpositionMem
        rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values
          completion input context cache (remainingFuel + 1) table 0 coordinates
            hcoordinateValues] at hresult
        simp at hresult
        subst result
        left
        simpa [TableInputAvailable] using havailable
      · let priorCoordinates := prior.map Coordinate.position
        let remainingCoordinates := remaining.map Coordinate.position
        have hcoordinates :
            (Position.leaf lay tree leafIdx).children.map Coordinate.position =
              priorCoordinates ++ .position child :: remainingCoordinates := by
          simp [hchildren, priorCoordinates, remainingCoordinates]
        have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
            context.state.values coordinate = some (completion coordinate) := by
          intro coordinate hcoordinate
          obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
          exact hvalues position hpositionMem
        have hnotRevealed : .position child ∉ context.state.revealed := by
          intro hrevealed
          exact (hpublished (.position child) hrevealed) hmissing
        rw [hcoordinates,
          runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
            completion input context cache remainingFuel 0 priorCoordinates remainingCoordinates
              (.position child) table hcoordinateValues hmissing hnotRevealed] at hresult
        simp at hresult
        subst result
        right
        apply completionOrdinaryInput_of_pending_leaf_child (table := table)
          hposition hchildren
        have hlength : priorCoordinates.length = prior.length := by simp [priorCoordinates]
        simp [hlength, LazyRevealProbe.State.addPending]

set_option maxRecDepth 100000 in
theorem preparedLeaf_privateStructuralHit_has_missingChild
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input = some (.leaf lay tree leafIdx))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hcompletable : DeferredCompletable table context)
    (hpositive : 0 < fuel) (hpublished : PublishedValues context.state)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache)))
    (hprivate : PrivateStructuralHit result.context) :
    ∃ child ∈ (Position.leaf lay tree leafIdx).children,
      result.context.state.values (.position child) = none := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hclean := hcompletion.not_privateStructuralHit
  have hcandidate := decodeProbe?_leaf_eq parameter input candidate lay tree leafIdx
    hprobe hposition
  subst candidate
  obtain ⟨remainingFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [runDirectResolvedDetailedFromTable_prepareLeafInputProbe] at hresult
  cases hsourceValue : context.state.values
      (.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
        Position.lastChainStep)) with
  | none =>
      rw [hsourceValue] at hresult
      have hnotRevealed :
          (.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep) : Coordinate) ∉ context.state.revealed := by
        intro hrevealed
        exact (hpublished _ hrevealed) hsourceValue
      unfold probe at hresult
      rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
      simp [hnotRevealed, runDirectResolvedDetailedFromTable] at hresult
      subst result
      have hnew := privateStructuralHit_addPending_imp context
        (.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
          Position.lastChainStep)) (slotDigest 0 input) hprivate
      rcases hnew with hold | ⟨child, output, hcoordinate, hhidden, _hvalue, _hmatch⟩
      · exact False.elim (hclean hold)
      · have hchild : child =
            .chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
              Position.lastChainStep := by
          simpa using hcoordinate.symm
        subst child
        refine ⟨.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
          Position.lastChainStep, ?_, ?_⟩
        · simp [Position.children]
        · simpa [LazyRevealProbe.State.addPending] using hhidden
  | some sourceOutput =>
      rw [hsourceValue] at hresult
      rcases positionValues_or_first_missing completion context.state
        (Position.leaf lay tree leafIdx).children
        (fun other output hvalue => (hcompletion.1 (.position other) output hvalue).symm) with
        havailable | ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
      · let coordinates := (Position.leaf lay tree leafIdx).children.map Coordinate.position
        have hcoordinateValues : ∀ coordinate, coordinate ∈ coordinates →
            context.state.values coordinate = some (completion coordinate) := by
          intro coordinate hcoordinate
          obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
          exact havailable position hpositionMem
        rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values
          completion input context cache (remainingFuel + 1) table 0 coordinates
            hcoordinateValues] at hresult
        simp at hresult
        subst result
        exact False.elim (hclean hprivate)
      · let priorCoordinates := prior.map Coordinate.position
        let remainingCoordinates := remaining.map Coordinate.position
        have hcoordinates :
            (Position.leaf lay tree leafIdx).children.map Coordinate.position =
              priorCoordinates ++ .position child :: remainingCoordinates := by
          simp [hchildren, priorCoordinates, remainingCoordinates]
        have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
            context.state.values coordinate = some (completion coordinate) := by
          intro coordinate hcoordinate
          obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
          exact hvalues position hpositionMem
        have hnotRevealed : .position child ∉ context.state.revealed := by
          intro hrevealed
          exact (hpublished (.position child) hrevealed) hmissing
        rw [hcoordinates,
          runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
            completion input context cache remainingFuel 0 priorCoordinates remainingCoordinates
              (.position child) table hcoordinateValues hmissing hnotRevealed] at hresult
        simp at hresult
        subst result
        have hnew := privateStructuralHit_addPending_imp context (.position child)
          (slotDigest priorCoordinates.length input) hprivate
        rcases hnew with hold | ⟨other, output, hcoordinate, hhidden, _hvalue, _hmatch⟩
        · exact False.elim (hclean hold)
        · have hother : other = child := by simpa using hcoordinate.symm
          subst other
          refine ⟨child, by simp [hchildren], ?_⟩
          simpa [LazyRevealProbe.State.addPending] using hhidden

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_peekPositionValues_of_mem_none
    (positions : List Position) (child : Position)
    (hchild : child ∈ positions)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hmissing : context.state.values (.position child) = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekPositionValues positions).run cache) =
      pure (.done ⟨context, fuel, (none, cache), table⟩) := by
  induction positions with
  | nil => simp at hchild
  | cons head remaining ih =>
      rw [peekPositionValues, StateT.run_bind,
        runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate]
      by_cases heq : head = child
      · subst head
        rw [hmissing]
        simp [runDirectResolvedDetailedFromTable]
      · have htail : child ∈ remaining := by
          rcases List.mem_cons.1 hchild with hsame | htail
          · exact False.elim (heq hsame.symm)
          · exact htail
        cases hhead : context.state.values (.position head) with
        | none => simp [runDirectResolvedDetailedFromTable]
        | some output =>
            rw [show truncateHash <$> some output = some (truncateHash output) by rfl]
            simp only [pure_bind]
            rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              ih htail]
            rfl

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_resolveKnownInput_leaf_of_missingChild
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (child : Position) (hchild : child ∈ (Position.leaf lay tree leafIdx).children)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hmissing : context.state.values (.position child) = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((resolveKnownInput parameter (.position (.leaf lay tree leafIdx)) input).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache) := by
  unfold resolveKnownInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
    StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekPositionValues_of_mem_none
      (Position.leaf lay tree leafIdx).children child hchild context fuel table cache hmissing]
  simp [runDirectResolvedDetailedFromTable]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingHashQuery_leaf
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input = some (.leaf lay tree leafIdx))
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
        ((probingHashQuery parameter input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQuery parameter input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  have hcandidate := decodeProbe?_leaf_eq parameter input candidate lay tree leafIdx
    hprobe hposition
  have hcoordinate : candidate.coordinate =
      .position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
        Position.lastChainStep) := by
    rw [hcandidate]
  have houtput := decodeProbe?_outputCoordinate_eq_position parameter input candidate
    (.leaf lay tree leafIdx) hprobe hposition
  unfold probingHashQuery
  rw [hprobe, hposition]
  simp only
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_with_support table
    ((prepareLeafInputProbe input candidate lay tree leafIdx).run leftCache)
    ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache)
    (fun _ cache =>
      (resolveKnownInput parameter candidate.outputCoordinate input).run cache)
    (fun _ cache =>
      (resolveKnownInput parameter candidate.outputCoordinate input).run cache)
    left right leftFuel rightFuel
  · exact relTriple_runDirectResolvedDetailed_prepareLeafInputProbe table input candidate
      lay tree leafIdx
      (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩ Position.lastChainStep)
      left right leftFuel rightFuel leftCache rightCache hcoordinate hcontext hpositive hfuel hcache
        hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hleftSupport hrightSupport hrelation
    have hrightResultMaterialized :
        rightResult.context = directDeferredContext rightResult.context.state := by
      have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache)
        right.state rightFuel table (.done rightResult) (by
          rw [← hrightMaterialized]
          exact hrightSupport)
      exact hshape
    obtain ⟨completion, hcompletion⟩ := hcontext.leftCompletable
    rcases preparedLeaf_available_or_completionOrdinary parameter table input candidate
      lay tree leafIdx hprobe hposition left leftFuel leftCache completion hcompletion
        hpositive hpublished leftResult hleftSupport with havailable | hordinary
    · rw [hrelation.left_table, hrelation.right_table, houtput]
      exact relTriple_runDirectResolvedDetailed_resolveKnownInput_available parameter table
        (.leaf lay tree leafIdx) input leftResult.context rightResult.context
          leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
          completion havailable hrelation.context_le hrelation.remaining_le
            hrelation.cache_eq hrelation.revealed_eq hrelation.values_le
              hrelation.left_published hrightResultMaterialized
    · rw [hrelation.left_table, hrelation.right_table, houtput]
      exact relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
        parameter table (.position (.leaf lay tree leafIdx)) input leftResult.context
          rightResult.context leftResult.remaining rightResult.remaining leftResult.value.2
            rightResult.value.2 hrelation.context_le hrelation.remaining_le
              hrelation.cache_eq hrelation.revealed_eq hrelation.values_le
                hrelation.left_published hrightResultMaterialized
                (fun position heq => by cases heq; simp [IsOtsPosition]) hordinary
  · intro leftResult rightResult hleftSupport hrightSupport hprivate
    have hleftCore := resolvedCore_of_mem_runDirectResolvedFromTable
      ((prepareLeafInputProbe input candidate lay tree leafIdx).run leftCache)
      left leftFuel table leftResult hcontext.view.leftConsistent hcontext.view.leftStarts
        (mem_support_runDirectResolvedFromTable_of_done_detailed
          ((prepareLeafInputProbe input candidate lay tree leafIdx).run leftCache)
          left leftFuel table leftResult hleftSupport)
    have hrightCore := resolvedCore_of_mem_runDirectResolvedFromTable
      ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache)
      right rightFuel table rightResult hcontext.view.rightConsistent hcontext.view.rightStarts
        (mem_support_runDirectResolvedFromTable_of_done_detailed
          ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache)
          right rightFuel table rightResult hrightSupport)
    have hrightResultMaterialized :
        rightResult.context = directDeferredContext rightResult.context.state := by
      have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        ((prepareLeafInputProbe input candidate lay tree leafIdx).run rightCache)
        right.state rightFuel table (.done rightResult) (by
          rw [← hrightMaterialized]
          exact hrightSupport)
      exact hshape
    obtain ⟨child, hchild, hmissing⟩ :=
      preparedLeaf_privateStructuralHit_has_missingChild parameter table input candidate
        lay tree leafIdx hprobe hposition left leftFuel leftCache hcontext.leftCompletable
          hpositive hpublished leftResult hleftSupport hprivate
    rw [hleftCore.1, hrightCore.1, houtput,
      runDirectResolvedDetailedFromTable_resolveKnownInput_leaf_of_missingChild
        parameter table input lay tree leafIdx child hchild leftResult.context
          leftResult.remaining leftResult.value.2 hmissing]
    exact relTriple_runDirectResolvedDetailed_splitHashQuery_private_left_materialized_right
      table input leftResult.context leftResult.remaining leftResult.value.2
        ((resolveKnownInput parameter (.position (.leaf lay tree leafIdx)) input).run
          rightResult.value.2)
        rightResult.context rightResult.remaining hprivate hrightResultMaterialized

set_option maxRecDepth 100000 in
theorem scannedNode_available_or_completionOrdinary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hposition : decodePosition? parameter input = some (.node lay tree level nodeIdx))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion)
    (hpositive : 0 < fuel) (hpublished : PublishedValues context.state)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((probeFirstMissingInputCoordinate input 0
          ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run cache))) :
    TableInputAvailable completion result.context.state
        (.position (.node lay tree level nodeIdx)) ∨
      CompletionOrdinaryInput parameter table result.context input := by
  obtain ⟨remainingFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rcases positionValues_or_first_missing completion context.state
    (Position.node lay tree level nodeIdx).children
    (fun other output hvalue => (hcompletion.1 (.position other) output hvalue).symm) with
    havailable | ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
  · let coordinates := (Position.node lay tree level nodeIdx).children.map Coordinate.position
    have hcoordinateValues : ∀ coordinate, coordinate ∈ coordinates →
        context.state.values coordinate = some (completion coordinate) := by
      intro coordinate hcoordinate
      obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
      exact havailable position hpositionMem
    rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values
      completion input context cache (remainingFuel + 1) table 0 coordinates
        hcoordinateValues] at hresult
    simp at hresult
    subst result
    left
    simpa [TableInputAvailable] using havailable
  · let priorCoordinates := prior.map Coordinate.position
    let remainingCoordinates := remaining.map Coordinate.position
    have hcoordinates :
        (Position.node lay tree level nodeIdx).children.map Coordinate.position =
          priorCoordinates ++ .position child :: remainingCoordinates := by
      simp [hchildren, priorCoordinates, remainingCoordinates]
    have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
        context.state.values coordinate = some (completion coordinate) := by
      intro coordinate hcoordinate
      obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
      exact hvalues position hpositionMem
    have hnotRevealed : .position child ∉ context.state.revealed := by
      intro hrevealed
      exact (hpublished (.position child) hrevealed) hmissing
    rw [hcoordinates,
      runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
        completion input context cache remainingFuel 0 priorCoordinates remainingCoordinates
          (.position child) table hcoordinateValues hmissing hnotRevealed] at hresult
    simp at hresult
    subst result
    right
    apply completionOrdinaryInput_of_pending_node_child (table := table)
      hposition hchildren
    have hlength : priorCoordinates.length = prior.length := by simp [priorCoordinates]
    simp [hlength, LazyRevealProbe.State.addPending]

set_option maxRecDepth 100000 in
theorem scannedNode_privateStructuralHit_has_missingChild
    (table : OtsSecretIndex → HashOutput) (input : HashInput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (hcompletable : DeferredCompletable table context)
    (hpositive : 0 < fuel) (hpublished : PublishedValues context.state)
    (result : ResolvedRunResult (Unit × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table
        ((probeFirstMissingInputCoordinate input 0
          ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run cache)))
    (hprivate : PrivateStructuralHit result.context) :
    ∃ child ∈ (Position.node lay tree level nodeIdx).children,
      result.context.state.values (.position child) = none := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hclean := hcompletion.not_privateStructuralHit
  obtain ⟨remainingFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rcases positionValues_or_first_missing completion context.state
    (Position.node lay tree level nodeIdx).children
    (fun other output hvalue => (hcompletion.1 (.position other) output hvalue).symm) with
    havailable | ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
  · let coordinates := (Position.node lay tree level nodeIdx).children.map Coordinate.position
    have hcoordinateValues : ∀ coordinate, coordinate ∈ coordinates →
        context.state.values coordinate = some (completion coordinate) := by
      intro coordinate hcoordinate
      obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
      exact havailable position hpositionMem
    rw [runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_values
      completion input context cache (remainingFuel + 1) table 0 coordinates
        hcoordinateValues] at hresult
    simp at hresult
    subst result
    exact False.elim (hclean hprivate)
  · let priorCoordinates := prior.map Coordinate.position
    let remainingCoordinates := remaining.map Coordinate.position
    have hcoordinates :
        (Position.node lay tree level nodeIdx).children.map Coordinate.position =
          priorCoordinates ++ .position child :: remainingCoordinates := by
      simp [hchildren, priorCoordinates, remainingCoordinates]
    have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
        context.state.values coordinate = some (completion coordinate) := by
      intro coordinate hcoordinate
      obtain ⟨position, hpositionMem, rfl⟩ := List.mem_map.1 hcoordinate
      exact hvalues position hpositionMem
    have hnotRevealed : .position child ∉ context.state.revealed := by
      intro hrevealed
      exact (hpublished (.position child) hrevealed) hmissing
    rw [hcoordinates,
      runDirectResolvedDetailedFromTable_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
        completion input context cache remainingFuel 0 priorCoordinates remainingCoordinates
          (.position child) table hcoordinateValues hmissing hnotRevealed] at hresult
    simp at hresult
    subst result
    have hnew := privateStructuralHit_addPending_imp context (.position child)
      (slotDigest priorCoordinates.length input) hprivate
    rcases hnew with hold | ⟨other, output, hcoordinate, hhidden, _hvalue, _hmatch⟩
    · exact False.elim (hclean hold)
    · have hother : other = child := by simpa using hcoordinate.symm
      subst other
      refine ⟨child, by simp [hchildren], ?_⟩
      simpa [LazyRevealProbe.State.addPending] using hhidden

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_resolveKnownInput_node_of_missingChild
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (child : Position) (hchild : child ∈ (Position.node lay tree level nodeIdx).children)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hmissing : context.state.values (.position child) = none) :
    runDirectResolvedDetailedFromTable context fuel table
        ((resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache) := by
  unfold resolveKnownInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
    StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekPositionValues_of_mem_none
      (Position.node lay tree level nodeIdx).children child hchild context fuel table cache hmissing]
  simp [runDirectResolvedDetailedFromTable]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingHashQuery_node
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some (.node lay tree level nodeIdx))
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
        ((probingHashQuery parameter input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQuery parameter input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  unfold probingHashQuery
  rw [hprobe, hposition]
  simp only
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_with_support table
    ((probeFirstMissingInputCoordinate input 0
      ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run leftCache)
    ((probeFirstMissingInputCoordinate input 0
      ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run rightCache)
    (fun _ cache =>
      (resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input).run cache)
    (fun _ cache =>
      (resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input).run cache)
    left right leftFuel rightFuel
  · exact relTriple_runDirectResolvedDetailed_probeFirstMissing_positions table input 0
      (Position.node lay tree level nodeIdx).children left right leftFuel rightFuel
        leftCache rightCache hcontext hpositive hfuel hcache hrevealed hvalues hpublished
          hrightMaterialized
  · intro leftResult rightResult hleftSupport hrightSupport hrelation
    have hrightResultMaterialized :
        rightResult.context = directDeferredContext rightResult.context.state := by
      have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        ((probeFirstMissingInputCoordinate input 0
          ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run
            rightCache)
        right.state rightFuel table (.done rightResult) (by
          rw [← hrightMaterialized]
          exact hrightSupport)
      exact hshape
    obtain ⟨completion, hcompletion⟩ := hcontext.leftCompletable
    rcases scannedNode_available_or_completionOrdinary parameter table input lay tree level
      nodeIdx hposition left leftFuel leftCache completion hcompletion hpositive hpublished
        leftResult hleftSupport with havailable | hordinary
    · rw [hrelation.left_table, hrelation.right_table]
      exact relTriple_runDirectResolvedDetailed_resolveKnownInput_available parameter table
        (.node lay tree level nodeIdx) input leftResult.context rightResult.context
          leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
          completion havailable hrelation.context_le hrelation.remaining_le
            hrelation.cache_eq hrelation.revealed_eq hrelation.values_le
              hrelation.left_published hrightResultMaterialized
    · rw [hrelation.left_table, hrelation.right_table]
      exact relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
        parameter table (.position (.node lay tree level nodeIdx)) input leftResult.context
          rightResult.context leftResult.remaining rightResult.remaining leftResult.value.2
            rightResult.value.2 hrelation.context_le hrelation.remaining_le
              hrelation.cache_eq hrelation.revealed_eq hrelation.values_le
                hrelation.left_published hrightResultMaterialized
                (fun position heq => by cases heq; simp [IsOtsPosition]) hordinary
  · intro leftResult rightResult hleftSupport hrightSupport hprivate
    have hleftCore := resolvedCore_of_mem_runDirectResolvedFromTable
      ((probeFirstMissingInputCoordinate input 0
        ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run leftCache)
      left leftFuel table leftResult hcontext.view.leftConsistent hcontext.view.leftStarts
        (mem_support_runDirectResolvedFromTable_of_done_detailed
          ((probeFirstMissingInputCoordinate input 0
            ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run
              leftCache)
          left leftFuel table leftResult hleftSupport)
    have hrightCore := resolvedCore_of_mem_runDirectResolvedFromTable
      ((probeFirstMissingInputCoordinate input 0
        ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run rightCache)
      right rightFuel table rightResult hcontext.view.rightConsistent hcontext.view.rightStarts
        (mem_support_runDirectResolvedFromTable_of_done_detailed
          ((probeFirstMissingInputCoordinate input 0
            ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run
              rightCache)
          right rightFuel table rightResult hrightSupport)
    have hrightResultMaterialized :
        rightResult.context = directDeferredContext rightResult.context.state := by
      have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        ((probeFirstMissingInputCoordinate input 0
          ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).run
            rightCache)
        right.state rightFuel table (.done rightResult) (by
          rw [← hrightMaterialized]
          exact hrightSupport)
      exact hshape
    obtain ⟨child, hchild, hmissing⟩ :=
      scannedNode_privateStructuralHit_has_missingChild table input lay tree level nodeIdx
        left leftFuel leftCache hcontext.leftCompletable hpositive hpublished leftResult
          hleftSupport hprivate
    rw [hleftCore.1, hrightCore.1,
      runDirectResolvedDetailedFromTable_resolveKnownInput_node_of_missingChild
        parameter table input lay tree level nodeIdx child hchild leftResult.context
          leftResult.remaining leftResult.value.2 hmissing]
    exact relTriple_runDirectResolvedDetailed_splitHashQuery_private_left_materialized_right
      table input leftResult.context leftResult.remaining leftResult.value.2
        ((resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input).run
          rightResult.value.2)
        rightResult.context rightResult.remaining hprivate hrightResultMaterialized

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingHashQuery
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (left right : DeferredContext)
    (leftFuel rightFuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probingHashQuery parameter input).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQuery parameter input).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      rcases decodePosition?_chain_or_leaf_of_decodeProbe? parameter input candidate hprobe with
        ⟨lay, tree, leafIdx, chainIdx, step, hposition⟩ |
          ⟨lay, tree, leafIdx, hposition⟩
      · exact relTriple_runDirectResolvedDetailed_probingHashQuery_chain parameter table
          input candidate lay tree leafIdx chainIdx step hprobe hposition left right leftFuel
            rightFuel leftCache rightCache hcontext hpositive hfuel hcache hrevealed hvalues
              hpublished hrightMaterialized
      · exact relTriple_runDirectResolvedDetailed_probingHashQuery_leaf parameter table
          input candidate lay tree leafIdx hprobe hposition left right leftFuel rightFuel
            leftCache rightCache hcontext hpositive hfuel hcache hrevealed hvalues hpublished
              hrightMaterialized
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          unfold probingHashQuery
          rw [hprobe, hposition]
          exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
            left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
              hvalues hpublished hrightMaterialized
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              have hordinary := completionOrdinaryInput_of_decodeProbe_none_chain
                (table := table) (context := left) hprobe hposition
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
                parameter table (.position (.chain lay tree leafIdx chainIdx step)) input
                  left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
                    hrevealed hvalues hpublished hrightMaterialized
                      (fun other heq => by cases heq; simp [IsOtsPosition]) hordinary
          | leaf lay tree leafIdx =>
              have hordinary := completionOrdinaryInput_of_decodeProbe_none_leaf
                (table := table) (context := left) hprobe hposition
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact relTriple_runDirectResolvedDetailed_resolveKnownInput_completionOrdinary
                parameter table (.position (.leaf lay tree leafIdx)) input left right leftFuel
                  rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
                    hpublished hrightMaterialized
                      (fun other heq => by cases heq; simp [IsOtsPosition]) hordinary
          | node lay tree level nodeIdx =>
              exact relTriple_runDirectResolvedDetailed_probingHashQuery_node parameter table
                input lay tree level nodeIdx hprobe hposition left right leftFuel rightFuel
                  leftCache rightCache hcontext hpositive hfuel hcache hrevealed hvalues
                    hpublished hrightMaterialized
          | ftsLeaf index tree leafIdx =>
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
                left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
                  hrevealed hvalues hpublished hrightMaterialized
          | ftsNode index tree level nodeIdx =>
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
                left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
                  hrevealed hvalues hpublished hrightMaterialized
          | ftsRoots index =>
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact relTriple_runDirectResolvedDetailed_splitHashQuery_ordinary table input
                left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
                  hrevealed hvalues hpublished hrightMaterialized

end SphincsSecurity.Concrete.OtsProbeSimulation
