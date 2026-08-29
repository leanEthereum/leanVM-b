import SphincsSecurity.Proof.OtsProbeResolvedPrivateSchedule

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedSignLayer

def canonicalizeDeferredResolution (table : OtsSecretIndex → HashOutput)
    (result : DeferredResolution) : DeferredResolution :=
  { toDeferredContext := canonicalizeMaterializedValues table result.toDeferredContext
    output := result.output }

theorem publicMaterializedValues_eq_of_privateStateAgrees
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hagrees : PrivateStateAgrees left right)
    (hpublished : PublishedValues right.state) :
    publicMaterializedValues table left = publicMaterializedValues table right := by
  funext coordinate
  unfold publicMaterializedValues
  have hrevealed : left.state.revealed = right.state.revealed := hagrees.2.1
  by_cases hright : coordinate ∈ right.state.revealed
  · have hleft : coordinate ∈ left.state.revealed := by rwa [hrevealed]
    simp only [hleft, hright, ↓reduceIte]
    cases coordinate with
    | chainStart => rfl
    | position position =>
        unfold resolvedCompletionValue DeferredContext.positionValue
        have hvalue := hpublished (.position position) hright
        cases hstate : right.state.values (.position position) with
        | none => exact False.elim (hvalue hstate)
        | some output =>
            have hleftState : left.state.values (.position position) = some output := by
              rw [hagrees.1]
              exact hstate
            simp [hstate, hleftState]
  · have hleft : coordinate ∉ left.state.revealed := by rwa [hrevealed]
    simp [hleft, hright]

theorem publicMaterializedValues_clearPending_values
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate) (values : DeferredStructuralValues)
    (hpublished : PublishedValues context.state) :
    publicMaterializedValues table
        { state := context.state.clearPending coordinate, values := values } =
      publicMaterializedValues table context := by
  apply publicMaterializedValues_eq_of_privateStateAgrees table _ context
  · exact ⟨rfl, rfl, rfl⟩
  · exact hpublished

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_canonicalize
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) :
    evalDist ((Option.map (canonicalizeDeferredResolution table)) <$>
      resolveDeferredPositionValue position context) =
      evalDist (resolveDeferredPositionValue position
        (canonicalizeMaterializedValues table context)) := by
  apply congrArg evalDist
  unfold resolveDeferredPositionValue canonicalizeDeferredResolution
  simp only [map_eq_bind_pure_comp]
  simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt]
  cases hstate : context.state.values (.position position) with
  | none =>
      by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
      · exact False.elim ((hpublished (.position position) hrevealed) hstate)
      · simp only [canonicalizeMaterializedValues, publicMaterializedValues,
          hrevealed, ↓reduceIte]
        cases hvalue : context.values position with
        | none =>
            simp only [bind_assoc]
            apply bind_congr
            intro output
            by_cases hhit : context.state.hitAt (.position position) output
            · have hmem : (Coordinate.position position, truncateHash output) ∈
                  context.state.pending := by
                simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
              simp [hmem]
            · have hpublic := publicMaterializedValues_clearPending_values table context
                  (.position position) (context.values.install position output) hpublished
              have hmem : (Coordinate.position position, truncateHash output) ∉
                  context.state.pending := by
                simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
              simp [hmem]
              rw [hpublic]
              rfl
        | some output =>
            simp only
            by_cases hhit : context.state.hitAt (.position position) output
            · have hmem : (Coordinate.position position, truncateHash output) ∈
                  context.state.pending := by
                simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
              simp [hmem]
            · have hpublic := publicMaterializedValues_clearPending_values table context
                  (.position position) context.values hpublished
              have hmem : (Coordinate.position position, truncateHash output) ∉
                  context.state.pending := by
                simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
              simp [hmem]
              rw [hpublic]
              rfl
  | some output =>
      have hvalue := hconsistent position output hstate
      by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
      · simp only [hstate, canonicalizeMaterializedValues, publicMaterializedValues,
          hrevealed, ↓reduceIte, resolvedCompletionValue, DeferredContext.positionValue]
        by_cases hhit : context.state.hitAt (.position position) output
        · have hmem : (Coordinate.position position, truncateHash output) ∈
              context.state.pending := by
            simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
          simp [hmem]
        · have hpublic := publicMaterializedValues_clearPending_values table context
              (.position position) (context.values.install position output) hpublished
          have hmem : (Coordinate.position position, truncateHash output) ∉
              context.state.pending := by
            simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
          simp [hmem]
          rw [hpublic]
          rfl
      · simp only [canonicalizeMaterializedValues, publicMaterializedValues,
          hrevealed, ↓reduceIte, hvalue]
        by_cases hhit : context.state.hitAt (.position position) output
        · have hmem : (Coordinate.position position, truncateHash output) ∈
              context.state.pending := by
            simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
          simp [hmem]
        · have hpublic := publicMaterializedValues_clearPending_values table context
              (.position position) (context.values.install position output) hpublished
          have hmem : (Coordinate.position position, truncateHash output) ∉
              context.state.pending := by
            simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
          simp [hmem, DeferredStructuralValues.install, hvalue]
          unfold DeferredStructuralValues.install at hpublic
          rw [hpublic]
          rfl

@[simp] noncomputable def finishObserve
    (observe : DeferredContext → Nat → α → ProbComp Bool) :
    Option (ResolvedRunResult α) → ProbComp Bool
  | none => pure true
  | some result => observe result.context result.remaining result.value

noncomputable def runResolvedObserve
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool :=
  runResolvedFromTable context fuel table computation >>= finishObserve observe

class ObserverDooms (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool) : Prop where
  eq_true : ∀ context fuel value,
    context.ValuesConsistent →
    StartTableAgrees context.state table →
    ¬DeferredCompletable table context →
    evalDist (observe context fuel value) = evalDist (pure true : ProbComp Bool)

class ObserverSynchronized (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool) : Prop where
  eq_of_synchronized : ∀ left right fuel value,
    FinalizationContextEq table (some left) (some right) →
    left.state.values = right.state.values →
    left.state.revealed = right.state.revealed →
    evalDist (observe left fuel value) = evalDist (observe right fuel value)

class ObserverPositionNeutral (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool) : Prop where
  eq_resolve : ∀ position context fuel value,
    context.Valid → DeferredCompletable table context →
    Coordinate.position position ∈ context.state.ensured →
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved => observe resolved.toDeferredContext fuel value) =
      evalDist (observe context fuel value)

theorem evalDist_runResolvedObserve_eq_true_of_not_completable
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context)
    (hobserve : ∀ nextContext remaining value,
      nextContext.ValuesConsistent →
      StartTableAgrees nextContext.state table →
      ¬DeferredCompletable table nextContext →
      evalDist (observe nextContext remaining value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (runResolvedObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  unfold runResolvedObserve
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ =>
          pure true) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel
            table result hconsistent hstarts hresult
          have hstillDoomed := not_deferredCompletable_of_mem_runResolvedFromTable
            computation context fuel table result hconsistent hstarts hresult hdoomed
          exact hobserve result.context result.remaining result.value hcore.2.1 hcore.2.2
            hstillDoomed
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runResolvedFromTable context fuel table computation) (by simp [runResolvedFromTable])
      (pure true)

theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_true_of_not_completable
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context)
    (hobserve : ∀ nextContext remaining value,
      nextContext.ValuesConsistent →
      StartTableAgrees nextContext.state table →
      ¬DeferredCompletable table nextContext →
      evalDist (observe nextContext remaining value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= fun _ => pure true) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedNotCompletable :
              ¬DeferredCompletable table resolved.toDeferredContext := by
            intro hresolvedCompletable
            obtain ⟨completion, hcompletion⟩ := hresolvedCompletable
            have hback :=
              (deferredCompletion_resolveDeferredPositionValue_iff position resolved
                hconsistent hresolved completion).mp hcompletion
            exact hdoomed ⟨completion, hback.1⟩
          exact evalDist_runResolvedObserve_eq_true_of_not_completable observe
            resolved.toDeferredContext fuel table computation
            (hconsistent.of_resolveDeferredPositionValue position resolved hresolved)
            (hstarts.of_state_values_eq
              (resolveDeferredPositionValue_preserves_state_values position context resolved
                hresolved))
            hresolvedNotCompletable hobserve
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolveDeferredPositionValue position context) (by
        simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
      (pure true)

theorem evalDist_runResolvedObserve_eq_true_of_not_completable_auto
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    [ObserverDooms table observe]
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runResolvedObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) :=
  evalDist_runResolvedObserve_eq_true_of_not_completable observe context fuel table computation
    hconsistent hstarts hdoomed ObserverDooms.eq_true

theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_true_of_not_completable_auto
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) [ObserverDooms table observe]
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (pure true : ProbComp Bool) :=
  evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_true_of_not_completable
    position context fuel table computation observe hconsistent hstarts hdoomed
      ObserverDooms.eq_true

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_after_materialized_reveal_observe
    (observe : DeferredContext → ProbComp Bool)
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredReveal table revealed context)) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            observe
              { state := (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output
                values := targetResult.values }) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedPosition context revealed revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult => observe targetResult.toDeferredContext) := by
  let materialized := materializeResolvedPosition context revealed revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredReveal table revealed revealedResult hrevealed
  have hstateValues := resolveDeferredReveal_preserves_state_values table revealed context
    revealedResult hrevealed
  have hresolved := resolveDeferredReveal_resolves table revealed context revealedResult
    hrevealed
  have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed revealedResult
    hrevealedValid hstateValues hresolved
  have hrevealedCompletable := hcompletable.of_resolveDeferredReveal hvalid revealed
    revealedResult hrevealed
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    refine ⟨completion, ?_⟩
    exact (deferredCompletion_materializeResolvedReveal_iff revealed revealedResult hvalid
      hstarts hrevealed).2 hcompletion
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedReveal revealed revealedResult hvalid hstarts
      hrevealed hmaterializedCompletable
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    revealedResult.toDeferredContext materialized hview.symm hrevealedValid
      hmaterializedValid hrevealedCompletable
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support
      (resolveDeferredPositionValue target revealedResult.toDeferredContext))
    (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel
  apply OracleComp.ProgramLogic.Relational.relTriple_bind hboth
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
      | some rightResult => simp [FinalizationResolutionEq] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResult =>
          simp only
          have hvalues : leftResult.values = rightResult.values :=
            resolveDeferredPositionValue_values_eq_of_values_eq target
              revealedResult.toDeferredContext materialized leftResult rightResult
              hleftSupport hrightSupport (by rfl) hrelation.1
          have hrightState := resolveDeferredPositionValue_state_eq_clearPending target
            materialized rightResult hrightSupport
          have hstate :
              (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output = rightResult.state := by
            rw [hrightState]
            exact clearPending_materialize_comm context.state (.position target)
              (.position revealed) revealedResult.output
          apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq
          rw [hstate, hvalues]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_after_materialized_chainStart_observe
    (observe : DeferredContext → ProbComp Bool)
    (target : Position) (index : OtsSecretIndex) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : resolveDeferredChainStart table index context = some revealedResult) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            observe
              { state := (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output
                values := targetResult.values }) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedChainStart context index revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult => observe targetResult.toDeferredContext) := by
  let materialized := materializeResolvedChainStart context index revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredChainStart table index revealedResult hrevealed
  have hstateValues := resolveDeferredChainStart_state_values_eq table index context
    revealedResult hrevealed
  have hdeferredValues := resolveDeferredChainStart_deferred_values_eq table index context
    revealedResult hrevealed
  have hrevealedCompletable := hcompletable.of_resolveDeferredChainStart index revealedResult
    hrevealed
  have houtput := resolveDeferredChainStart_output_of_agrees table index context revealedResult
    hstarts hrevealed
  have hmaterializedValid : materialized.Valid := by
    dsimp only [materialized]
    rw [materializeResolvedChainStart, hdeferredValues]
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx revealedResult.output
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    refine ⟨completion, ?_⟩
    exact (deferredCompletion_materializeResolvedChainStart_iff index revealedResult hstarts
      houtput hstateValues hdeferredValues
      (resolveDeferredChainStart_pending_eq table index context revealedResult hrevealed)).2
        hcompletion
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedChainStart index revealedResult hvalid hstarts
      hrevealed hmaterializedCompletable
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    revealedResult.toDeferredContext materialized hview.symm hrevealedValid
      hmaterializedValid hrevealedCompletable
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support
      (resolveDeferredPositionValue target revealedResult.toDeferredContext))
    (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel
  apply OracleComp.ProgramLogic.Relational.relTriple_bind hboth
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
      | some rightResult => simp [FinalizationResolutionEq] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResult =>
          simp only
          have hvalues : leftResult.values = rightResult.values :=
            resolveDeferredPositionValue_values_eq_of_values_eq target
              revealedResult.toDeferredContext materialized leftResult rightResult
              hleftSupport hrightSupport (by rfl) hrelation.1
          have hrightState := resolveDeferredPositionValue_state_eq_clearPending target
            materialized rightResult hrightSupport
          have hstate :
              (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output = rightResult.state := by
            rw [hrightState]
            exact clearPending_materialize_comm context.state (.position target)
              index.coordinate revealedResult.output
          apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq
          rw [hstate, hvalues]

theorem evalDist_resolveDeferredPositionValue_after_materialized_reveal_runResolvedObserve
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredReveal table revealed context)) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runResolvedObserve observe
              { state := (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedPosition context revealed revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runResolvedObserve observe targetResult.toDeferredContext fuel table computation) :=
  evalDist_resolveDeferredPositionValue_after_materialized_reveal_observe
    (fun nextContext => runResolvedObserve observe nextContext fuel table computation)
    target revealed context revealedResult table hvalid hcompletable hrevealed

theorem evalDist_resolveDeferredPositionValue_after_materialized_chainStart_runResolvedObserve
    (target : Position) (index : OtsSecretIndex) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : resolveDeferredChainStart table index context = some revealedResult) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runResolvedObserve observe
              { state := (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedChainStart context index revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runResolvedObserve observe targetResult.toDeferredContext fuel table computation) :=
  evalDist_resolveDeferredPositionValue_after_materialized_chainStart_observe
    (fun nextContext => runResolvedObserve observe nextContext fuel table computation)
    target index context revealedResult table hvalid hcompletable hrevealed

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured)
    (hbase : ∀ nextContext remaining value,
      nextContext.Valid → DeferredCompletable table nextContext →
      Coordinate.position position ∈ nextContext.state.ensured →
      evalDist (resolveDeferredPositionValue position nextContext >>= fun resolved =>
        match resolved with
        | none => pure true
        | some resolved => observe resolved.toDeferredContext remaining value) =
        evalDist (observe nextContext remaining value))
    [ObserverDooms table observe] :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      unfold runResolvedObserve
      simp only [runResolvedFromTable, pure_bind]
      exact hbase context fuel value hvalid hcompletable hensured
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_uniform_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none =>
                  exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                    (by simp) (pure true)).symm
              | some resolved => rfl
            _ = evalDist ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
                resolveDeferredPositionValue position context >>= fun resolved =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | hashOutput =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_hashOutput_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                LazyRevealProbe.sampleHashOutput >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none =>
                  exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                    LazyRevealProbe.sampleHashOutput (by
                      simp [LazyRevealProbe.sampleHashOutput]) (pure true)).symm
              | some resolved => rfl
            _ = evalDist (LazyRevealProbe.sampleHashOutput >>= fun output =>
                resolveDeferredPositionValue position context >>= fun resolved =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                LazyRevealProbe.sampleHashOutput _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | ensure coordinate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_ensure_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.ensure coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishObserve observe) := by
              rw [resolveDeferredPositionValue_ensure]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply congrArg evalDist
              apply bind_congr
              intro resolved
              cases resolved <;> rfl
            _ = _ := ih () { context with state := context.state.ensure coordinate } fuel
              (hvalid.ensure coordinate) (hcompletable.ensure coordinate) (by
                exact Finset.mem_insert.mpr (Or.inr hensured))
      | probe coordinate candidate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero =>
              simp only [pure_bind]
              have hnone : finishObserve observe
                  (none : Option (ResolvedRunResult α)) = pure true := by
                simp [finishObserve]
              simp_rw [hnone]
              calc
                _ = evalDist (resolveDeferredPositionValue position context >>= fun _ =>
                      pure true) := by
                  apply congrArg evalDist
                  apply bind_congr
                  intro resolved
                  cases resolved <;> rfl
                _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                  (resolveDeferredPositionValue position context) (by
                    simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
                  (pure true)
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · calc
                  _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                        match resolved with
                        | none => pure true
                        | some resolved =>
                            runResolvedFromTable resolved.toDeferredContext remaining table
                                (next ()) >>=
                              finishObserve observe) := by
                      apply evalDist_bind_congr
                      intro resolved hresolved
                      cases resolved with
                      | none => rfl
                      | some resolved =>
                          have hstate := resolveDeferredPositionValue_state_eq_clearPending
                            position context resolved hresolved
                          simp [hstate, LazyRevealProbe.State.clearPending, hrevealed]
                  _ = _ := by
                    simpa [runResolvedObserve, hrevealed] using
                      ih () context remaining hvalid hcompletable hensured
              · by_cases heq : coordinate = .position position
                · subst coordinate
                  let nextContext : DeferredContext :=
                    { context with
                      state := context.state.addPending (.position position) candidate }
                  let continuation : Option DeferredResolution → ProbComp Bool
                    | none => pure true
                    | some resolved =>
                        runResolvedFromTable resolved.toDeferredContext remaining table
                            (next ()) >>=
                          finishObserve observe
                  calc
                    _ = evalDist (resolveDeferredPositionValue position context >>=
                          fun first =>
                            match first with
                            | none => pure true
                            | some first =>
                                resolveDeferredPositionValue position
                                    { first.toDeferredContext with
                                      state := first.state.addPending (.position position)
                                        candidate } >>=
                                  continuation) := by
                        apply evalDist_bind_congr
                        intro first hfirst
                        cases first with
                        | none => rfl
                        | some first =>
                            let added : DeferredContext :=
                              { first.toDeferredContext with
                                state := first.state.addPending (.position position) candidate }
                            have hfirstValid :=
                              hvalid.of_resolveDeferredPositionValue position first hfirst
                            have hfirstCompletable :=
                              hcompletable.of_resolveDeferredPositionValue hvalid position first
                                hfirst
                            have hfirstState := resolveDeferredPositionValue_state_eq_clearPending
                              position context first hfirst
                            have hnotRevealed :
                                Coordinate.position position ∉ first.state.revealed := by
                              simpa [hfirstState, LazyRevealProbe.State.clearPending] using
                                hrevealed
                            have haddedEnsured :
                                Coordinate.position position ∈ added.state.ensured := by
                              simpa [added, hfirstState, LazyRevealProbe.State.clearPending,
                                LazyRevealProbe.State.addPending] using hensured
                            by_cases haddedCompletable : DeferredCompletable table added
                            · simpa [added, continuation, DeferredResolution.addPending,
                                hnotRevealed, runResolvedObserve] using
                                (ih () added remaining
                                  (hfirstValid.addPending_of_completable
                                    (.position position) candidate haddedCompletable)
                                  haddedCompletable haddedEnsured).symm
                            · have haddedConsistent : added.ValuesConsistent :=
                                hfirstValid.valuesConsistent.addPending (.position position)
                                  candidate
                              have hfirstStarts : StartTableAgrees first.state table :=
                                startTableAgrees_of_deferredCompletable hfirstCompletable
                              have haddedStarts : StartTableAgrees added.state table := by
                                exact hfirstStarts
                              calc
                                _ = evalDist (pure true : ProbComp Bool) := by
                                  simpa [added, hnotRevealed, runResolvedObserve] using
                                    evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                                      (observe := observe)
                                      added remaining table (next ()) haddedConsistent haddedStarts
                                      haddedCompletable
                                _ = _ := by
                                  symm
                                  exact
                                    evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_true_of_not_completable_auto
                                      position added remaining table (next ()) haddedConsistent
                                      haddedStarts haddedCompletable
                    _ = evalDist ((do
                          let first ← resolveDeferredPositionValue position context
                          match first with
                          | none => (pure none : ProbComp (Option DeferredResolution))
                          | some first =>
                              resolveDeferredPositionValue position
                                { first.toDeferredContext with
                                  state := first.state.addPending (.position position)
                                    candidate }) >>= continuation) := by
                        simp only [bind_assoc]
                        apply congrArg evalDist
                        apply bind_congr
                        intro first
                        cases first <;> rfl
                    _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                          continuation) := by
                        dsimp only [nextContext]
                        exact congrArg evalDist (congrArg (fun resolver => resolver >>= continuation)
                          (resolveDeferredPositionValue_then_addPending_self_resolve position
                            context candidate))
                    _ = _ := by
                        have hnextConsistent : nextContext.ValuesConsistent :=
                          hvalid.valuesConsistent.addPending (.position position) candidate
                        have hstarts : StartTableAgrees context.state table :=
                          startTableAgrees_of_deferredCompletable hcompletable
                        have hnextStarts : StartTableAgrees nextContext.state table := by
                          exact hstarts
                        have hnextEnsured :
                            Coordinate.position position ∈ nextContext.state.ensured := hensured
                        by_cases hnextCompletable : DeferredCompletable table nextContext
                        · simpa [nextContext, continuation, hrevealed,
                              runResolvedObserve] using
                            ih () nextContext remaining
                              (hvalid.addPending_of_completable (.position position) candidate
                                hnextCompletable)
                              hnextCompletable hnextEnsured
                        · calc
                            _ = evalDist (pure true : ProbComp Bool) :=
                              evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_true_of_not_completable_auto
                                position nextContext remaining table (next ()) hnextConsistent
                                hnextStarts hnextCompletable
                            _ = _ := by
                              symm
                              simpa [nextContext, hrevealed, runResolvedObserve] using
                                evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                                  (observe := observe)
                                  nextContext remaining table (next ()) hnextConsistent hnextStarts
                                  hnextCompletable
                · let nextContext : DeferredContext :=
                    { context with state := context.state.addPending coordinate candidate }
                  by_cases hnextCompletable : DeferredCompletable table nextContext
                  · calc
                      _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                            fun resolved =>
                              match resolved with
                              | none => pure true
                              | some resolved =>
                                  runResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishObserve observe) := by
                          dsimp only [nextContext]
                          rw [resolveDeferredPositionValue_addPending_of_ne position context
                            coordinate candidate heq]
                          simp only [map_eq_bind_pure_comp, bind_assoc]
                          apply evalDist_bind_congr
                          intro resolved hresolved
                          cases resolved with
                          | none => rfl
                          | some resolved =>
                              have hstate := resolveDeferredPositionValue_state_eq_clearPending
                                position context resolved hresolved
                              have hnotRevealed : coordinate ∉ resolved.state.revealed := by
                                simpa [hstate, LazyRevealProbe.State.clearPending] using hrevealed
                              simp [DeferredResolution.addPending, hnotRevealed]
                      _ = _ := by
                        simpa [nextContext, hrevealed, runResolvedObserve] using
                          ih () nextContext remaining
                            (hvalid.addPending_of_completable coordinate candidate
                              hnextCompletable)
                            hnextCompletable (by exact hensured)
                  · have hnextConsistent : nextContext.ValuesConsistent :=
                      hvalid.valuesConsistent.addPending coordinate candidate
                    have hstarts : StartTableAgrees context.state table :=
                      startTableAgrees_of_deferredCompletable hcompletable
                    have hnextStarts : StartTableAgrees nextContext.state table := by
                      exact hstarts
                    calc
                      _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                            fun resolved =>
                              match resolved with
                              | none => pure true
                              | some resolved =>
                                  runResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishObserve observe) := by
                          dsimp only [nextContext]
                          rw [resolveDeferredPositionValue_addPending_of_ne position context
                            coordinate candidate heq]
                          simp only [map_eq_bind_pure_comp, bind_assoc]
                          apply evalDist_bind_congr
                          intro resolved hresolved
                          cases resolved with
                          | none => rfl
                          | some resolved =>
                              have hstate := resolveDeferredPositionValue_state_eq_clearPending
                                position context resolved hresolved
                              have hnotRevealed : coordinate ∉ resolved.state.revealed := by
                                simpa [hstate, LazyRevealProbe.State.clearPending] using hrevealed
                              simp [DeferredResolution.addPending, hnotRevealed]
                      _ = evalDist (pure true : ProbComp Bool) := by
                        calc
                          _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                                fun _ => pure true) := by
                            apply evalDist_bind_congr
                            intro resolved hresolved
                            cases resolved with
                            | none => rfl
                            | some resolved =>
                                have hresolvedNotCompletable :
                                    ¬DeferredCompletable table resolved.toDeferredContext := by
                                  intro hresolvedCompletable
                                  obtain ⟨completion, hcompletion⟩ := hresolvedCompletable
                                  have hback :=
                                    (deferredCompletion_resolveDeferredPositionValue_iff position
                                      resolved hnextConsistent hresolved completion).mp hcompletion
                                  exact hnextCompletable ⟨completion, hback.1⟩
                                exact
                                  evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                                    resolved.toDeferredContext remaining table (next ())
                                    (hnextConsistent.of_resolveDeferredPositionValue position
                                      resolved hresolved)
                                    (hnextStarts.of_state_values_eq
                                      (resolveDeferredPositionValue_preserves_state_values position
                                        nextContext resolved hresolved))
                                    hresolvedNotCompletable
                          _ = _ :=
                            OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                              (resolveDeferredPositionValue position nextContext) (by
                                simp [resolveDeferredPositionValue,
                                  LazyRevealProbe.sampleHashOutput])
                              (pure true)
                      _ = _ := by
                        symm
                        simpa [nextContext, hrevealed, runResolvedObserve] using
                          evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                            (observe := observe)
                            nextContext remaining table (next ()) hnextConsistent hnextStarts
                            hnextCompletable
      | peek coordinate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_peek_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table
                        (next (context.state.values coordinate)) >>=
                      finishObserve observe) := by
              apply evalDist_bind_congr
              intro resolved hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  have hvalues := resolveDeferredPositionValue_preserves_state_values position
                    context resolved hresolved
                  simp [hvalues]
            _ = _ := ih (context.state.values coordinate) context fuel hvalid hcompletable
              hensured
      | publish coordinate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_publish_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.publish coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishObserve observe) := by
              rw [resolveDeferredPositionValue_publish]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply congrArg evalDist
              apply bind_congr
              intro resolved
              cases resolved <;> rfl
            _ = _ := ih () { context with state := context.state.publish coordinate } fuel
              (hvalid.publish coordinate) (hcompletable.publish coordinate) hensured
      | reveal coordinate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              let continuation : Option RevealedResolution → ProbComp Bool
                | none => pure true
                | some resolved =>
                    runResolvedObserve observe
                      { state := (context.state.clearPending (.position position)).materialize
                          index.coordinate resolved.output
                        values := resolved.context.values }
                      fuel table (next resolved.output)
              simp only
              calc
                _ = evalDist (resolvePositionThenChainStart position table index context >>=
                      continuation) := by
                    unfold resolvePositionThenChainStart continuation
                    simp only [bind_assoc]
                    apply evalDist_bind_congr
                    intro positionResult hpositionResult
                    cases positionResult with
                    | none => rfl
                    | some positionResult =>
                        have hstate := resolveDeferredPositionValue_state_eq_clearPending
                          position context positionResult hpositionResult
                        cases hrevealedResult : resolveDeferredChainStart table index
                          positionResult.toDeferredContext with
                        | none =>
                            dsimp only [index] at hrevealedResult ⊢
                            simp [hrevealedResult, finishObserve]
                        | some revealedResult =>
                            dsimp only [index] at hrevealedResult ⊢
                            simp only [hrevealedResult, pure_bind]
                            rw [hstate]
                            rfl
                _ = evalDist (resolveChainStartThenPosition position table index context >>=
                      continuation) :=
                    evalDist_bind_eq_of_evalDist_eq
                      (evalDist_resolvePosition_chainStart_comm position table index context
                        hcompletable)
                      continuation
                _ = evalDist (match resolveDeferredChainStart table index context with
                      | none => pure true
                      | some revealedResult =>
                          resolveDeferredPositionValue position
                              revealedResult.toDeferredContext >>=
                            fun targetResult =>
                              match targetResult with
                              | none => pure true
                              | some targetResult =>
                                  runResolvedObserve observe
                                    { state := (context.state.clearPending
                                          (.position position)).materialize
                                        index.coordinate revealedResult.output
                                      values := targetResult.values }
                                    fuel table (next revealedResult.output)) := by
                    unfold resolveChainStartThenPosition continuation
                    cases resolveDeferredChainStart table index context with
                    | none => rfl
                    | some revealedResult =>
                        simp only [bind_assoc]
                        apply congrArg evalDist
                        apply bind_congr
                        intro targetResult
                        cases targetResult <;> rfl
                _ = evalDist (match resolveDeferredChainStart table index context with
                      | none => pure true
                      | some revealedResult =>
                          runResolvedObserve observe
                            (materializeResolvedChainStart context index revealedResult)
                            fuel table (next revealedResult.output)) := by
                    cases hrevealedResult : resolveDeferredChainStart table index context with
                    | none => rfl
                    | some revealedResult =>
                        have htransport :=
                          evalDist_resolveDeferredPositionValue_after_materialized_chainStart_runResolvedObserve
                            position index context revealedResult table fuel
                              (next revealedResult.output) observe hvalid hcompletable hrevealedResult
                        have hstarts := startTableAgrees_of_deferredCompletable hcompletable
                        have hdeferredValues :=
                          resolveDeferredChainStart_deferred_values_eq table index context
                            revealedResult hrevealedResult
                        have hrevealedValid := hvalid.of_resolveDeferredChainStart table index
                          revealedResult hrevealedResult
                        have hrevealedCompletable :=
                          hcompletable.of_resolveDeferredChainStart index revealedResult
                            hrevealedResult
                        have hstateValues := resolveDeferredChainStart_state_values_eq table index
                          context revealedResult hrevealedResult
                        have houtput := resolveDeferredChainStart_output_of_agrees table index
                          context revealedResult hstarts hrevealedResult
                        have hmaterializedValid :
                            (materializeResolvedChainStart context index revealedResult).Valid := by
                          rw [materializeResolvedChainStart, hdeferredValues]
                          exact hvalid.materialize_chainStart lay tree leafIdx chainIdx
                            revealedResult.output
                        have hmaterializedCompletable : DeferredCompletable table
                            (materializeResolvedChainStart context index revealedResult) := by
                          obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
                          refine ⟨completion, ?_⟩
                          exact (deferredCompletion_materializeResolvedChainStart_iff index
                            revealedResult hstarts houtput hstateValues hdeferredValues
                              (resolveDeferredChainStart_pending_eq table index context
                                revealedResult hrevealedResult)).2 hcompletion
                        have hmaterializedEnsured : Coordinate.position position ∈
                            (materializeResolvedChainStart context index
                              revealedResult).state.ensured := by
                          change Coordinate.position position ∈
                            insert index.coordinate context.state.ensured
                          exact Finset.mem_insert.mpr (Or.inr hensured)
                        exact htransport.trans
                          (ih revealedResult.output
                            (materializeResolvedChainStart context index revealedResult) fuel
                            hmaterializedValid hmaterializedCompletable
                              hmaterializedEnsured)
                _ = _ := by
                    cases hrevealedResult : resolveDeferredChainStart table index context with
                    | none =>
                        simp [finishObserve]
                    | some revealedResult =>
                        simp only [pure_bind, materializeResolvedChainStart]
                        rfl
          | position revealed =>
              let resolver : PrivateResolver := fun nextContext =>
                resolveDeferredReveal table revealed nextContext
              let continuation : Option RevealedResolution → ProbComp Bool
                | none => pure true
                | some resolved =>
                    runResolvedObserve observe
                      { state := (context.state.clearPending (.position position)).materialize
                          (.position revealed) resolved.output
                        values := resolved.context.values }
                      fuel table (next resolved.output)
              simp only
              calc
                _ = evalDist (resolvePositionThenResolver position resolver context >>=
                      continuation) := by
                    unfold resolvePositionThenResolver resolver continuation
                    simp only [bind_assoc]
                    apply evalDist_bind_congr
                    intro positionResult hpositionResult
                    cases positionResult with
                    | none => rfl
                    | some positionResult =>
                        simp only [bind_assoc]
                        apply evalDist_bind_congr
                        intro revealedResult _hrevealedResult
                        cases revealedResult with
                        | none => rfl
                        | some revealedResult =>
                            have hstate := resolveDeferredPositionValue_state_eq_clearPending
                              position context positionResult hpositionResult
                            simp only
                            rw [hstate]
                            simp only [pure_bind]
                            rfl
                _ = evalDist (resolveResolverThenPosition position resolver context >>=
                      continuation) :=
                    evalDist_bind_eq_of_evalDist_eq
                      (positionResolutionCommutes_reveal position table revealed context hvalid
                        hcompletable)
                      continuation
                _ = evalDist (resolveDeferredReveal table revealed context >>=
                      fun revealedResult =>
                        match revealedResult with
                        | none => pure true
                        | some revealedResult =>
                            resolveDeferredPositionValue position
                                revealedResult.toDeferredContext >>=
                              fun targetResult =>
                                match targetResult with
                                | none => pure true
                                | some targetResult =>
                                    runResolvedObserve observe
                                      { state := (context.state.clearPending
                                            (.position position)).materialize
                                          (.position revealed) revealedResult.output
                                        values := targetResult.values }
                                      fuel table (next revealedResult.output)) := by
                    unfold resolveResolverThenPosition resolver continuation
                    simp only [bind_assoc]
                    apply congrArg evalDist
                    apply bind_congr
                    intro revealedResult
                    cases revealedResult with
                    | none => rfl
                    | some revealedResult =>
                        simp only [bind_assoc]
                        apply bind_congr
                        intro targetResult
                        cases targetResult <;> rfl
                _ = evalDist (resolveDeferredReveal table revealed context >>=
                      fun revealedResult =>
                        match revealedResult with
                        | none => pure true
                        | some revealedResult =>
                            runResolvedObserve observe
                              (materializeResolvedPosition context revealed revealedResult)
                              fuel table (next revealedResult.output)) := by
                    apply evalDist_bind_congr
                    intro revealedResult hrevealedResult
                    cases revealedResult with
                    | none => rfl
                    | some revealedResult =>
                        have htransport :=
                          evalDist_resolveDeferredPositionValue_after_materialized_reveal_runResolvedObserve
                            position revealed context revealedResult table fuel
                              (next revealedResult.output) observe hvalid hcompletable hrevealedResult
                        have hstarts := startTableAgrees_of_deferredCompletable hcompletable
                        have hrevealedValid := hvalid.of_resolveDeferredReveal table revealed
                          revealedResult hrevealedResult
                        have hstateValues := resolveDeferredReveal_preserves_state_values table
                          revealed context revealedResult hrevealedResult
                        have hresolved := resolveDeferredReveal_resolves table revealed context
                          revealedResult hrevealedResult
                        have hmaterializedValid :=
                          hvalid.materializeResolvedPosition_of revealed revealedResult
                            hrevealedValid hstateValues hresolved
                        have hrevealedCompletable :=
                          hcompletable.of_resolveDeferredReveal hvalid revealed revealedResult
                            hrevealedResult
                        have hmaterializedCompletable : DeferredCompletable table
                            (materializeResolvedPosition context revealed revealedResult) := by
                          obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
                          refine ⟨completion, ?_⟩
                          exact (deferredCompletion_materializeResolvedReveal_iff revealed
                            revealedResult hvalid hstarts hrevealedResult).2 hcompletion
                        have hmaterializedEnsured : Coordinate.position position ∈
                            (materializeResolvedPosition context revealed
                              revealedResult).state.ensured := by
                          change Coordinate.position position ∈
                            insert (.position revealed) context.state.ensured
                          exact Finset.mem_insert.mpr (Or.inr hensured)
                        exact htransport.trans
                          (ih revealedResult.output
                            (materializeResolvedPosition context revealed revealedResult) fuel
                            hmaterializedValid hmaterializedCompletable
                              hmaterializedEnsured)
                _ = _ := by
                    simp only [materializeResolvedPosition, bind_assoc]
                    apply congrArg evalDist
                    apply bind_congr
                    intro revealedResult
                    cases revealedResult <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured)
    [ObserverDooms table observe] [ObserverPositionNeutral table observe] :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  apply evalDist_resolveDeferredPositionValue_then_runResolvedObserve position computation
    context fuel table hvalid hcompletable hensured
  intro nextContext remaining value hnextValid hnextCompletable hnextEnsured
  exact ObserverPositionNeutral.eq_resolve (table := table) (observe := observe) position
    nextContext remaining value hnextValid hnextCompletable hnextEnsured

theorem evalDist_runResolvedObserve_eq_of_finalizationSynchronized
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (runResolvedObserve observe left fuel table computation) =
      evalDist (runResolvedObserve observe right fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value =>
      unfold runResolvedObserve
      simp only [runResolvedFromTable, pure_bind]
      exact ObserverSynchronized.eq_of_synchronized left right fuel value hcontext
        hvalues hrevealed
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_uniform_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | hashOutput =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_hashOutput_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | ensure coordinate =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_ensure_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.ensure coordinate, hleftValid.ensure coordinate,
              hrightValid.ensure coordinate, hleftCompletable.ensure coordinate⟩
          · exact hvalues
          · exact hrevealed
      | peek coordinate =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_peek_query_bind]
          rw [hvalues]
          exact ih (right.state.values coordinate) left right fuel hcontext hvalues hrevealed
      | publish coordinate =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_publish_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.publish coordinate, hleftValid.publish coordinate,
              hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩
          · exact hvalues
          · simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
      | probe coordinate candidate =>
          unfold runResolvedObserve
          simp only [runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => rfl
          | succ remaining =>
              by_cases hleftRevealed : coordinate ∈ left.state.revealed
              · have hrightRevealed : coordinate ∈ right.state.revealed := by
                  rw [← hrevealed]
                  exact hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () left right remaining hcontext hvalues hrevealed
              · have hrightRevealed : coordinate ∉ right.state.revealed := by
                  rwa [← hrevealed]
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                let left' : DeferredContext :=
                  { left with state := left.state.addPending coordinate candidate }
                let right' : DeferredContext :=
                  { right with state := right.state.addPending coordinate candidate }
                have hcompletableIff : DeferredCompletable table left' ↔
                    DeferredCompletable table right' := by
                  exact deferredCompletable_addPending_iff_of_finalizationViewEq
                    hcontext.1 coordinate candidate
                by_cases hleftCompletable : DeferredCompletable table left'
                · have hrightCompletable : DeferredCompletable table right' :=
                    hcompletableIff.mp hleftCompletable
                  apply ih () left' right' remaining
                  · exact ⟨hcontext.1.addPending_of_completable coordinate candidate
                        hleftCompletable hrightCompletable,
                      hcontext.2.1.addPending_of_completable coordinate candidate
                        hleftCompletable,
                      hcontext.2.2.1.addPending_of_completable coordinate candidate
                        hrightCompletable,
                      hleftCompletable⟩
                  · exact hvalues
                  · exact hrevealed
                · have hrightCompletable : ¬DeferredCompletable table right' := by
                    rwa [← hcompletableIff]
                  calc
                    _ = evalDist (pure true : ProbComp Bool) :=
                      evalDist_runResolvedObserve_eq_true_of_not_completable_auto (observe := observe)
                        left' remaining table (next ()) hcontext.2.1.1 hcontext.1.leftStarts
                        hleftCompletable
                    _ = evalDist (runResolvedObserve observe right' remaining table
                        (next ())) :=
                      (evalDist_runResolvedObserve_eq_true_of_not_completable_auto (observe := observe)
                        right' remaining table (next ()) hcontext.2.2.1.1 hcontext.1.rightStarts
                        hrightCompletable).symm
      | reveal coordinate =>
          unfold runResolvedObserve
          simp_rw [runResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              have hresolved := relTriple_resolveDeferredChainStart_of_finalizationViewEq
                table index left right hview hleftValid hrightValid hleftCompletable
              have hresolvedLeft :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
                  (fun result => result ∈ support
                    (pure (resolveDeferredChainStart table index left) :
                      ProbComp (Option DeferredResolution)))
                  (fun result hresult => hresult)
              have hresolvedBoth :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hresolvedLeft
              apply evalDist_eq_of_relTriple_eqRel
              apply relTriple_bind hresolvedBoth
              intro leftResolved rightResolved hrelation
              rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
              cases leftResolved with
              | none =>
                  cases rightResolved with
                  | none => simp [EqRel]
                  | some rightResolved => simp [FinalizationResolutionEq] at hrelation
              | some leftResolved =>
                  cases rightResolved with
                  | none => simp [FinalizationResolutionEq] at hrelation
                  | some rightResolved =>
                      have hleftResult :
                          resolveDeferredChainStart table index left = some leftResolved := by
                        simpa using hleftSupport.symm
                      have hrightResult :
                          resolveDeferredChainStart table index right = some rightResolved := by
                        simpa using hrightSupport.symm
                      have hleftMaterializedCompletable :=
                        hleftCompletable.materializeResolvedChainStart hview.leftStarts index
                          leftResolved hleftResult
                      have hrightCompletable : DeferredCompletable table right := by
                        rcases hleftCompletable with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (hview.deferredCompletion_iff completion).mp hcompletion⟩
                      have hrightMaterializedCompletable :=
                        hrightCompletable.materializeResolvedChainStart hview.rightStarts index
                          rightResolved hrightResult
                      have hleftMaterializedView :=
                        finalizationViewEq_materializeResolvedChainStart index leftResolved
                          hleftValid hview.leftStarts hleftResult
                            hleftMaterializedCompletable
                      have hrightMaterializedView :=
                        finalizationViewEq_materializeResolvedChainStart index rightResolved
                          hrightValid hview.rightStarts hrightResult
                            hrightMaterializedCompletable
                      have hleftMaterializedValid :
                          (materializeResolvedChainStart left index leftResolved).Valid := by
                        unfold materializeResolvedChainStart
                        rw [resolveDeferredChainStart_deferred_values_eq table index left
                          leftResolved hleftResult]
                        exact hleftValid.materialize_chainStart lay tree leafIdx chainIdx
                          leftResolved.output
                      have hrightMaterializedValid :
                          (materializeResolvedChainStart right index rightResolved).Valid := by
                        unfold materializeResolvedChainStart
                        rw [resolveDeferredChainStart_deferred_values_eq table index right
                          rightResolved hrightResult]
                        exact hrightValid.materialize_chainStart lay tree leafIdx chainIdx
                          rightResolved.output
                      have hnext := ih leftResolved.output
                        (materializeResolvedChainStart left index leftResolved)
                        (materializeResolvedChainStart right index rightResolved) fuel
                        ⟨hleftMaterializedView.trans
                            (hrelation.2.1.trans hrightMaterializedView.symm),
                          hleftMaterializedValid, hrightMaterializedValid,
                          hleftMaterializedCompletable⟩
                        (by
                          change Function.update left.state.values index.coordinate
                              (some leftResolved.output) =
                            Function.update right.state.values index.coordinate
                              (some rightResolved.output)
                          rw [hrelation.1, hvalues])
                        (by
                          simpa [materializeResolvedChainStart,
                            LazyRevealProbe.State.materialize] using hrevealed)
                      apply relTriple_eqRel_of_evalDist_eq
                      simpa only [runResolvedObserve, materializeResolvedChainStart,
                        index, OtsSecretIndex.coordinate, hrelation.1] using hnext
          | position position =>
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table
                position left right hview hleftValid hrightValid hleftCompletable
              have hresolvedLeft :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
                  (fun result => result ∈ support
                    (resolveDeferredReveal table position left))
                  (fun result hresult => hresult)
              have hresolvedBoth :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hresolvedLeft
              apply evalDist_eq_of_relTriple_eqRel
              apply relTriple_bind hresolvedBoth
              intro leftResolved rightResolved hrelation
              rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
              cases leftResolved with
              | none =>
                  cases rightResolved with
                  | none => simp [EqRel]
                  | some rightResolved => simp [FinalizationResolutionEq] at hrelation
              | some leftResolved =>
                  cases rightResolved with
                  | none => simp [FinalizationResolutionEq] at hrelation
                  | some rightResolved =>
                      have hleftMaterializedCompletable : DeferredCompletable table
                          (materializeResolvedPosition left position leftResolved) := by
                        rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (deferredCompletion_materializeResolvedReveal_iff position
                            leftResolved hleftValid hview.leftStarts hleftSupport).mpr
                              hcompletion⟩
                      have hrightRawCompletable :
                          DeferredCompletable table rightResolved.toDeferredContext := by
                        rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
                      have hrightMaterializedCompletable : DeferredCompletable table
                          (materializeResolvedPosition right position rightResolved) := by
                        rcases hrightRawCompletable with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (deferredCompletion_materializeResolvedReveal_iff position
                            rightResolved hrightValid hview.rightStarts hrightSupport).mpr
                              hcompletion⟩
                      have hleftMaterializedView :=
                        finalizationViewEq_materializeResolvedReveal position leftResolved
                          hleftValid hview.leftStarts hleftSupport
                            hleftMaterializedCompletable
                      have hrightMaterializedView :=
                        finalizationViewEq_materializeResolvedReveal position rightResolved
                          hrightValid hview.rightStarts hrightSupport
                            hrightMaterializedCompletable
                      have hleftResultValid := hleftValid.of_resolveDeferredReveal table
                        position leftResolved hleftSupport
                      have hrightResultValid := hrightValid.of_resolveDeferredReveal table
                        position rightResolved hrightSupport
                      have hleftStateValues :=
                        resolveDeferredReveal_preserves_state_values table position left
                          leftResolved hleftSupport
                      have hrightStateValues :=
                        resolveDeferredReveal_preserves_state_values table position right
                          rightResolved hrightSupport
                      have hleftResolvedValue := resolveDeferredReveal_resolves table position
                        left leftResolved hleftSupport
                      have hrightResolvedValue := resolveDeferredReveal_resolves table position
                        right rightResolved hrightSupport
                      have hleftMaterializedValid :
                          (materializeResolvedPosition left position leftResolved).Valid :=
                        hleftValid.materializeResolvedPosition_of position leftResolved
                          hleftResultValid hleftStateValues hleftResolvedValue
                      have hrightMaterializedValid :
                          (materializeResolvedPosition right position rightResolved).Valid :=
                        hrightValid.materializeResolvedPosition_of position rightResolved
                          hrightResultValid hrightStateValues hrightResolvedValue
                      have hnext := ih leftResolved.output
                        (materializeResolvedPosition left position leftResolved)
                        (materializeResolvedPosition right position rightResolved) fuel
                        ⟨hleftMaterializedView.trans
                            (hrelation.2.1.trans hrightMaterializedView.symm),
                          hleftMaterializedValid, hrightMaterializedValid,
                          hleftMaterializedCompletable⟩
                        (by
                          change Function.update left.state.values (.position position)
                              (some leftResolved.output) =
                            Function.update right.state.values (.position position)
                              (some rightResolved.output)
                          rw [hrelation.1, hvalues])
                        (by
                          simpa [materializeResolvedPosition,
                            LazyRevealProbe.State.materialize] using hrevealed)
                      apply relTriple_eqRel_of_evalDist_eq
                      simpa only [runResolvedObserve, materializeResolvedPosition,
                        hrelation.1] using hnext

theorem evalDist_resolveDeferredChainStart_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (match resolveDeferredChainStart table index context with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  let result : DeferredResolution :=
    ⟨{ state := context.state.clearPending index.coordinate, values := context.values },
      table index⟩
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hclean := hcompletable.not_hitAt_chainStart index
  have hresult : resolveDeferredChainStart table index context = some result := by
    cases hstate : context.state.values index.coordinate with
    | some output =>
        have houtput := hstarts index output hstate
        simp [resolveDeferredChainStart, hstate, houtput, hclean, result]
    | none => simp [resolveDeferredChainStart, hstate, hclean, result]
  rw [hresult]
  exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized computation
    result.toDeferredContext context fuel table
    (finalizationContextEq_resolveDeferredChainStart_original table index context result
      hvalid hcompletable hresult)
    (resolveDeferredChainStart_state_values_eq table index context result hresult)
    (by
      rw [resolveDeferredChainStart_state_eq_clearPending table index context result hresult]
      rfl)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChainPrefix_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      (∀ step : ChainStep, step.val < steps →
        Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
          context.state.ensured) →
      evalDist (do
        let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          steps hsteps context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | 0, hsteps, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable, _hensured => by
      simp only [resolveDeferredChainPrefix, pure_bind]
      exact evalDist_resolveDeferredChainStart_then_runResolvedObserve table
        ⟨lay, tree, leafIdx, chainIdx⟩ context fuel computation hvalid hcompletable
  | steps + 1, hsteps, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable, hensured => by
      rw [resolveDeferredChainPrefix]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps
              (by omega) context >>= fun previous =>
            match previous with
            | none => pure true
            | some previous =>
                runResolvedObserve observe previous.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro previous hprevious
          cases previous with
          | none => rfl
          | some previous =>
              let position : Position :=
                .chain lay tree leafIdx chainIdx ⟨steps, by omega⟩
              have hpreviousValid := hvalid.of_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx steps (by omega) previous hprevious
              have hpreviousCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hprevious
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx steps (by omega) context previous hprevious
              have hpositionEnsured : Coordinate.position position ∈
                  previous.state.ensured := by
                rw [hprivate.2.2]
                exact hensured ⟨steps, by omega⟩ (by simp)
              exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto
                (observe := observe)
                position computation previous.toDeferredContext fuel table hpreviousValid
                  hpreviousCompletable hpositionEnsured
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedObserve table lay tree
            leafIdx chainIdx steps (by omega) context fuel computation hvalid hcompletable
              (fun step hstep => hensured step (by omega))
set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChains_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ (chains : List ChainIndex) (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      (∀ chainIdx ∈ chains, FullChainEnsured lay tree leafIdx chainIdx context) →
      evalDist (do
        let resolved ← resolveDeferredChains table lay tree leafIdx chains context
        match resolved with
        | none => pure true
        | some resolved => runResolvedObserve observe resolved fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | [], context, fuel, computation, observe, _hdooms, _hsynchronized, _hposition,
      _hvalid, _hcompletable, _hensured => by
      simp [resolveDeferredChains]
  | chainIdx :: remaining, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable, hensured => by
      rw [resolveDeferredChains]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>= fun resolved =>
            match resolved with
            | none => pure true
            | some resolved =>
                runResolvedObserve observe resolved.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedValid := hvalid.of_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx (chainLength - 1) (by omega) resolved hresolved
              have hresolvedCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hresolved
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx (chainLength - 1) (by omega) context resolved hresolved
              apply evalDist_resolveDeferredChains_then_runResolvedObserve table lay tree
                leafIdx remaining resolved.toDeferredContext fuel computation hresolvedValid
                  hresolvedCompletable
              intro other hother step
              rw [hprivate.2.2]
              exact hensured other (by simp [hother]) step
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedObserve table lay tree
            leafIdx chainIdx (chainLength - 1) (by omega) context fuel computation hvalid
              hcompletable (fun step _ => hensured chainIdx (by simp) step)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : OtsLeafEnsured lay tree leafIdx context) :
    evalDist (do
      let resolved ← resolveDeferredOtsLeaf table lay tree leafIdx context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  rw [resolveDeferredOtsLeaf]
  simp only [bind_assoc]
  calc
    _ = evalDist (resolveDeferredChains table lay tree leafIdx
          (List.ofFn fun chainIdx : ChainIndex => chainIdx) context >>= fun chains =>
        match chains with
        | none => pure true
        | some chains => runResolvedObserve observe chains fuel table computation) := by
      apply evalDist_bind_congr
      intro chains hchains
      cases chains with
      | none => rfl
      | some chains =>
          have hchainsValid := hvalid.of_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
          have hchainsCompletable := hcompletable.of_resolveDeferredChains hvalid hchains
          have hprivate := privateStateAgrees_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains
          have hleafEnsured : Coordinate.position (.leaf lay tree leafIdx) ∈
              chains.state.ensured := by
            rw [hprivate.2.2]
            exact hensured.2
          exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto
            (observe := observe)
            (.leaf lay tree leafIdx) computation chains fuel table hchainsValid
              hchainsCompletable hleafEnsured
    _ = _ := evalDist_resolveDeferredChains_then_runResolvedObserve table lay tree
      leafIdx (List.ofFn fun chainIdx : ChainIndex => chainIdx) context fuel computation
        hvalid hcompletable (by
          intro chainIdx _hmem
          exact hensured.1 chainIdx)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredTreeNode_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      TreeNodeEnsured lay tree level nodeIdx context →
      evalDist (do
        let resolved ← resolveDeferredTreeNode table lay tree level nodeIdx hlevel context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | 0, nodeIdx, hlevel, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable, hensured =>
      evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve table lay tree
        (leafOfNat nodeIdx) context fuel computation hvalid hcompletable hensured
  | level + 1, nodeIdx, hlevel, context, fuel, computation, observe, _hdooms,
      _hsynchronized, _hposition, hvalid, hcompletable, hensured => by
      rw [resolveDeferredTreeNode]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredTreeNode table lay tree level (2 * nodeIdx)
              (by omega) context >>= fun leftResult =>
            match leftResult with
            | none => pure true
            | some leftResult =>
                runResolvedObserve observe leftResult.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro leftResult hleft
          cases leftResult with
          | none => rfl
          | some leftResult =>
              have hleftValid := hvalid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) leftResult hleft
              have hleftCompletable :=
                hcompletable.of_resolveDeferredTreeNode hvalid hleft
              have hleftPrivate := privateStateAgrees_resolveDeferredTreeNode table lay tree
                level (2 * nodeIdx) (by omega) context leftResult hleft
              have hrightEnsured : TreeNodeEnsured lay tree level (2 * nodeIdx + 1)
                  leftResult.toDeferredContext := by
                exact (treeNodeEnsured_congr_ensured lay tree level (2 * nodeIdx + 1)
                  context leftResult.toDeferredContext hleftPrivate.2.2.symm).mp
                    hensured.2.1
              simp only [bind_assoc]
              calc
                _ = evalDist (resolveDeferredTreeNode table lay tree level
                      (2 * nodeIdx + 1) (by omega) leftResult.toDeferredContext >>=
                    fun rightResult =>
                      match rightResult with
                      | none => pure true
                      | some rightResult =>
                          runResolvedObserve observe rightResult.toDeferredContext fuel table
                            computation) := by
                  apply evalDist_bind_congr
                  intro rightResult hright
                  cases rightResult with
                  | none => rfl
                  | some rightResult =>
                      have hrightValid := hleftValid.of_resolveDeferredTreeNode table lay tree
                        level (2 * nodeIdx + 1) (by omega) rightResult hright
                      have hrightCompletable :=
                        hleftCompletable.of_resolveDeferredTreeNode hleftValid hright
                      have hrightPrivate := privateStateAgrees_resolveDeferredTreeNode table lay
                        tree level (2 * nodeIdx + 1) (by omega)
                          leftResult.toDeferredContext rightResult hright
                      obtain ⟨hnodeLevel, hnodeBase⟩ := hensured.2.2
                      have hnodeEnsured : Coordinate.position
                          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) ∈
                            rightResult.state.ensured := by
                        rw [hrightPrivate.2.2, hleftPrivate.2.2]
                        simpa using hnodeBase
                      exact
                        evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto
                          (observe := observe)
                          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) computation
                            rightResult.toDeferredContext fuel table hrightValid
                              hrightCompletable hnodeEnsured
                _ = _ :=
                  evalDist_resolveDeferredTreeNode_then_runResolvedObserve table lay tree
                    level (2 * nodeIdx + 1) (by omega) leftResult.toDeferredContext fuel
                      computation hleftValid hleftCompletable hrightEnsured
        _ = _ :=
          evalDist_resolveDeferredTreeNode_then_runResolvedObserve table lay tree level
            (2 * nodeIdx) (by omega) context fuel computation hvalid hcompletable hensured.1

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredSelectedChainFamily_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ {n : Nat} (family : Fin n → ChainIndex) (digits : Fin n → Digit)
      (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      (∀ index (step : ChainStep), step.val < (digits index).val →
        Coordinate.position (.chain lay tree leafIdx (family index) step) ∈
          context.state.ensured) →
      evalDist (do
        let resolved ← resolveDeferredSelectedChainFamily table lay tree leafIdx
          family digits context
        match resolved with
        | none => pure true
        | some (finalContext, _) =>
            runResolvedObserve observe finalContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation)
  | 0, family, digits, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, _hvalid, _hcompletable, _hensured => by
      simp [resolveDeferredSelectedChainFamily]
  | n + 1, family, digits, context, fuel, computation, observe, _hdooms,
      _hsynchronized, _hposition, hvalid, hcompletable, hensured => by
      rw [resolveDeferredSelectedChainFamily]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx (family 0)
              (digits 0).val (by have := (digits 0).isLt; omega) context >>=
            fun headOption =>
              match headOption with
              | none => pure true
              | some head =>
                  runResolvedObserve observe head.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro headOption hhead
          cases headOption with
          | none => rfl
          | some head =>
              have hheadValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                (family 0) (digits 0).val (by have := (digits 0).isLt; omega) head hhead
              have hheadCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hhead
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx (family 0) (digits 0).val
                  (by have := (digits 0).isLt; omega) context head hhead
              have htail :=
                evalDist_resolveDeferredSelectedChainFamily_then_runResolvedObserve
                  (observe := observe)
                  table lay tree leafIdx (fun index : Fin n => family index.succ)
                    (fun index : Fin n => digits index.succ) head.toDeferredContext fuel
                      computation hheadValid hheadCompletable (by
                        intro index step hstep
                        rw [hprivate.2.2]
                        exact hensured index.succ step hstep)
              calc
                _ = evalDist (do
                    let tail ← resolveDeferredSelectedChainFamily table lay tree leafIdx
                      (fun index : Fin n => family index.succ)
                      (fun index : Fin n => digits index.succ) head.toDeferredContext
                    match tail with
                    | none => pure true
                    | some (finalContext, _) =>
                        runResolvedObserve observe finalContext fuel table computation) := by
                      apply congrArg evalDist
                      simp only [bind_assoc]
                      apply bind_congr
                      intro tailOption
                      cases tailOption <;> simp
                _ = _ := htail
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedObserve table lay tree
            leafIdx (family 0) (digits 0).val
              (by have := (digits 0).isLt; omega) context fuel computation hvalid
                hcompletable (fun step hstep => hensured 0 step hstep)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerPathFamily_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ {n : Nat} (family : Fin n → Fin maxLayerHeight)
      (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      (∀ index, (family index).val < layerHeight lay →
        TreeNodeEnsured lay tree (family index).val
          (Nat.xor (leafIdx.val / 2 ^ (family index).val) 1) context) →
      evalDist (do
        let resolved ← resolveDeferredLayerPathFamily table lay tree leafIdx family context
        match resolved with
        | none => pure true
        | some (finalContext, _) =>
            runResolvedObserve observe finalContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation)
  | 0, family, context, fuel, computation, observe, _hdooms, _hsynchronized, _hposition,
      _hvalid, _hcompletable, _hensured => by
      simp [resolveDeferredLayerPathFamily]
  | n + 1, family, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable, hensured => by
      rw [resolveDeferredLayerPathFamily]
      by_cases hinLayer : (family 0).val < layerHeight lay
      · simp only [hinLayer, ↓reduceDIte, bind_assoc]
        calc
          _ = evalDist (resolveDeferredTreeNode table lay tree (family 0).val
                (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                  (by have := (family 0).isLt; omega) context >>= fun headOption =>
              match headOption with
              | none => pure true
              | some head =>
                  runResolvedObserve observe head.toDeferredContext fuel table computation) := by
            apply evalDist_bind_congr
            intro headOption hhead
            cases headOption with
            | none => rfl
            | some head =>
                have hheadValid := hvalid.of_resolveDeferredTreeNode table lay tree
                  (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                    (by have := (family 0).isLt; omega) head hhead
                have hheadCompletable := hcompletable.of_resolveDeferredTreeNode hvalid hhead
                have hprivate := privateStateAgrees_resolveDeferredTreeNode table lay tree
                  (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                    (by have := (family 0).isLt; omega) context head hhead
                have htail :=
                  evalDist_resolveDeferredLayerPathFamily_then_runResolvedObserve
                    (observe := observe)
                    table lay tree leafIdx (fun index : Fin n => family index.succ)
                      head.toDeferredContext fuel computation hheadValid hheadCompletable (by
                        intro index hindex
                        apply (treeNodeEnsured_congr_ensured lay tree
                          (family index.succ).val
                          (Nat.xor (leafIdx.val / 2 ^ (family index.succ).val) 1)
                            context head.toDeferredContext hprivate.2.2.symm).mp
                        exact hensured index.succ hindex)
                calc
                  _ = evalDist (do
                      let tail ← resolveDeferredLayerPathFamily table lay tree leafIdx
                        (fun index : Fin n => family index.succ) head.toDeferredContext
                      match tail with
                      | none => pure true
                      | some (finalContext, _) =>
                          runResolvedObserve observe finalContext fuel table computation) := by
                        apply congrArg evalDist
                        simp only [bind_assoc]
                        apply bind_congr
                        intro tailOption
                        cases tailOption <;> simp
                  _ = _ := htail
          _ = _ := evalDist_resolveDeferredTreeNode_then_runResolvedObserve table lay tree
            (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
              (by have := (family 0).isLt; omega) context fuel computation hvalid
                hcompletable (hensured 0 hinLayer)
      · simp only [hinLayer, ↓reduceDIte, bind_assoc]
        calc
          _ = evalDist (do
              let tail ← resolveDeferredLayerPathFamily table lay tree leafIdx
                (fun index : Fin n => family index.succ) context
              match tail with
              | none => pure true
              | some (finalContext, _) =>
                  runResolvedObserve observe finalContext fuel table computation) := by
                apply congrArg evalDist
                apply bind_congr
                intro tailOption
                cases tailOption <;> simp
          _ = _ :=
            evalDist_resolveDeferredLayerPathFamily_then_runResolvedObserve table lay tree
              leafIdx (fun index : Fin n => family index.succ) context fuel computation hvalid
                hcompletable (fun index hindex => hensured index.succ hindex)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerValues_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : LayerValuesEnsured index lay encoding context) :
    evalDist (do
      let resolved ← resolveDeferredLayerValues table index lay encoding context
      match resolved with
      | none => pure true
      | some (finalContext, _) =>
          runResolvedObserve observe finalContext fuel table computation) =
    evalDist (runResolvedObserve observe context fuel table computation) := by
  let chainFamily : ChainIndex → ChainIndex := fun chainIdx => chainIdx
  let pathFamily : Fin maxLayerHeight → Fin maxLayerHeight := fun level => level
  change evalDist (do
      let resolved ← resolveDeferredLayerValues table index lay encoding context
      match resolved with
      | none => pure true
      | some (finalContext, _) =>
          runResolvedObserve observe finalContext fuel table computation) = _
  rw [resolveDeferredLayerValues]
  simp only [bind_assoc]
  calc
    _ = evalDist (resolveDeferredSelectedChainFamily table lay (treeIndexAt index lay)
          (leafIndexAt index lay) chainFamily encoding context >>=
        fun chainsOption =>
          match chainsOption with
          | none => pure true
          | some (afterChains, _) =>
              runResolvedObserve observe afterChains fuel table computation) := by
      apply evalDist_bind_congr
      intro chainsOption hchains
      cases chainsOption with
      | none => rfl
      | some chains =>
          rcases chains with ⟨afterChains, chainValues⟩
          have hchainsValid := hvalid.of_resolveDeferredSelectedChainFamily table lay
            (treeIndexAt index lay) (leafIndexAt index lay)
              chainFamily encoding afterChains chainValues hchains
          have hchainsCompletable :=
            hcompletable.of_resolveDeferredSelectedChainFamily hvalid
              chainFamily encoding afterChains chainValues hchains
          have hprivate := privateStateAgrees_resolveDeferredSelectedChainFamily table lay
            (treeIndexAt index lay) (leafIndexAt index lay)
              chainFamily encoding context afterChains chainValues
                hchains
          have hpath := evalDist_resolveDeferredLayerPathFamily_then_runResolvedObserve
            (observe := observe)
            table lay (treeIndexAt index lay) (leafIndexAt index lay)
              pathFamily afterChains fuel computation
                hchainsValid hchainsCompletable (by
                  intro level hlevel
                  apply (treeNodeEnsured_congr_ensured lay (treeIndexAt index lay) level.val
                    (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1)
                      context afterChains hprivate.2.2.symm).mp
                  exact hensured.2 level hlevel)
          calc
            _ = evalDist (do
                let path ← resolveDeferredLayerPathFamily table lay (treeIndexAt index lay)
                  (leafIndexAt index lay) (fun level : Fin maxLayerHeight => level) afterChains
                match path with
                | none => pure true
                | some (finalContext, _) =>
                    runResolvedObserve observe finalContext fuel table computation) := by
                  apply congrArg evalDist
                  simp only [bind_assoc]
                  apply bind_congr
                  intro pathOption
                  cases pathOption <;> simp
            _ = evalDist (runResolvedObserve observe afterChains fuel table computation) := by
              apply Eq.trans _ hpath
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  rcases resolved with ⟨finalContext, values⟩
                  rfl
            _ = _ := rfl
    _ = evalDist (runResolvedObserve observe context fuel table computation) := by
      let hbase :=
        evalDist_resolveDeferredSelectedChainFamily_then_runResolvedObserve
          (observe := observe) table lay
          (treeIndexAt index lay) (leafIndexAt index lay) chainFamily encoding context fuel
            computation hvalid hcompletable hensured.1
      apply Eq.trans _ hbase
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro resolved
      cases resolved with
      | none => rfl
      | some resolved =>
          rcases resolved with ⟨finalContext, values⟩
          rfl

theorem evalDist_resolveSelectedLayerValuesList_then_runResolvedObserve
    (table : OtsSecretIndex → HashOutput) (index : Index)
    (selected : Layer → Option DeferredLayerEncoding)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe] :
    ∀ (layers : List Layer) (context : DeferredContext),
      context.Valid → DeferredCompletable table context →
      (∀ lay, lay ∈ layers → ∀ counter encoding,
        selected lay = some (counter, encoding) →
          LayerValuesEnsured index lay encoding context) →
      evalDist (do
        let resolved ← resolveSelectedLayerValuesList table index selected layers context
        match resolved with
        | none => pure true
        | some finalContext =>
            runResolvedObserve observe finalContext fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | [], context, hvalid, hcompletable, hensured => by
      simp [resolveSelectedLayerValuesList]
  | lay :: layers, context, hvalid, hcompletable, hensured => by
      rw [resolveSelectedLayerValuesList]
      cases hselection : selected lay with
      | none =>
          exact evalDist_resolveSelectedLayerValuesList_then_runResolvedObserve table index
            selected fuel computation layers context hvalid hcompletable
              (fun other hother counter encoding hselected =>
                hensured other (List.mem_cons_of_mem lay hother) counter encoding hselected)
      | some selection =>
          rcases selection with ⟨counter, encoding⟩
          simp only [bind_assoc]
          calc
            _ = evalDist (resolveDeferredLayerValues table index lay encoding context >>= fun
                resolved =>
                  match resolved with
                  | none => pure true
                  | some (afterLayer, _) =>
                      runResolvedObserve observe afterLayer fuel table computation) := by
                apply evalDist_bind_congr
                intro resolved hresolved
                cases resolved with
                | none => rfl
                | some resolved =>
                    rcases resolved with ⟨afterLayer, values⟩
                    have hafterValid := hvalid.of_resolveDeferredLayerValues table index lay
                      encoding afterLayer values hresolved
                    have hafterCompletable := hcompletable.of_resolveDeferredLayerValues hvalid
                      hresolved
                    have hagrees := privateStateAgrees_resolveDeferredLayerValues table index lay
                      encoding context afterLayer values hresolved
                    exact evalDist_resolveSelectedLayerValuesList_then_runResolvedObserve
                      table index selected fuel computation layers afterLayer hafterValid
                        hafterCompletable
                        (fun other hother otherCounter otherEncoding hselected =>
                          (hensured other (List.mem_cons_of_mem lay hother) otherCounter
                            otherEncoding hselected).of_privateStateAgrees hagrees)
            _ = _ :=
              evalDist_resolveDeferredLayerValues_then_runResolvedObserve table index lay
                encoding context fuel computation hvalid hcompletable
                  (hensured lay (by simp) counter encoding hselection)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerSchedule_publish_observe_eq_selectedList
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (index : Index)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    {observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe] :
    ∀ (layers : List Layer) (result : ResolvedRunResult DeferredLayerStore),
      result.table = table →
      (∀ lay, lay ∉ layers →
        (result.value.resolved lay).isSome =
          (result.value.selected lay).isSome) →
      evalDist (runDeferredLayerSchedule parameter table ftsSecret index
          (layers.map DeferredLayerOperation.resolve) (some result) >>=
        publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath >>=
        finishObserve observe) =
      evalDist (do
        let resolved ← resolveSelectedLayerValuesList table index
          result.value.selected layers result.context
        match resolved with
        | none => pure true
        | some finalContext =>
            runResolvedObserve observe finalContext result.remaining table
              ((publishSelectedChronologicalSignature ftsSecret randomness index leaves
                ftsPath result.value.selected).run result.value.cache))
  | [], result, htable, hagrees => by
      have hpresence : ResolutionPresenceAgrees result.value := by
        intro lay
        exact hagrees lay (by simp)
      simp only [List.map_nil, runDeferredLayerSchedule, pure_bind,
        resolveSelectedLayerValuesList]
      rw [publishDeferredChronologicalSignature_eq_selected ftsSecret randomness index leaves
        ftsPath result hpresence]
      simp only [publishSelectedDeferredSignature]
      unfold runResolvedObserve
      rw [htable]
  | lay :: layers, result, htable, hagrees => by
      simp only [List.map_cons, runDeferredLayerSchedule, runDeferredLayerOperation]
      rw [resolveDeferredLayer]
      cases hselection : result.value.selected lay with
      | none =>
          simp only [pure_bind, resolveSelectedLayerValuesList, hselection]
          have hrecursive :=
            evalDist_resolveDeferredLayerSchedule_publish_observe_eq_selectedList
              (observe := observe) parameter
              table index ftsSecret randomness leaves ftsPath layers
              { context := result.context
                remaining := result.remaining
                value :=
                  { result.value with
                    resolved := Function.update result.value.resolved lay none }
                table := table }
                rfl (by
                  intro observed hnotMem
                  by_cases heq : observed = lay
                  · subst observed
                    simp [Function.update, hselection]
                  · simpa [Function.update, heq] using
                      hagrees observed (by simp [heq, hnotMem]))
          simpa only [bind_assoc] using hrecursive
      | some selection =>
          rcases selection with ⟨counter, encoding⟩
          simp only [bind_assoc, resolveSelectedLayerValuesList, hselection]
          apply evalDist_bind_congr
          intro resolvedOption hresolved
          cases resolvedOption with
          | none =>
              simp [publishDeferredChronologicalSignature, finishObserve]
          | some resolved =>
              rcases resolved with ⟨afterLayer, values⟩
              simpa only [pure_bind, bind_assoc] using
                (evalDist_resolveDeferredLayerSchedule_publish_observe_eq_selectedList
                  (observe := observe) parameter
                  table index ftsSecret randomness leaves ftsPath layers
                    { context := afterLayer
                      remaining := result.remaining
                      value :=
                        { result.value with
                          resolved := Function.update result.value.resolved lay
                            (some (counter, values.1, values.2)) }
                      table := table }
                    rfl (by
                      intro observed hnotMem
                      by_cases heq : observed = lay
                      · subst observed
                        simp [Function.update, hselection]
                      · simpa [Function.update, heq] using
                          hagrees observed (by simp [heq, hnotMem])))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem evalDist_runDeferredLayersAndPublish_observe_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    {observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache >>= finishObserve observe) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>= finishObserve observe) := by
  unfold runDeferredLayersAndPublish runSelectionOnlyLayersAndPublish
  rw [deferredLayerSchedule_eq_append, runDeferredLayerSchedule_append]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none =>
      simp [publishDeferredChronologicalSignature, publishSelectedDeferredSignature,
        finishObserve]
  | some selected =>
      have hinvariants :
          selected.table = table ∧ selected.context.Valid ∧
            DeferredCompletable table selected.context ∧
              ∀ lay counter encoding,
                selected.value.selected lay = some (counter, encoding) →
                  LayerValuesEnsured index lay encoding selected.context :=
        selectedLayersEnsured_of_mem_deferredLayerSelections parameter table ftsSecret index
          context fuel cache selected hvalid hcompletable hselected
      have hschedule :=
        evalDist_resolveDeferredLayerSchedule_publish_observe_eq_selectedList
          (observe := observe) parameter table
          index ftsSecret randomness leaves ftsPath [topLayer, middleLayer, bottomLayer]
            selected hinvariants.1 (by
              intro lay hnotMem
              fin_cases lay <;>
                simp [topLayer, middleLayer, bottomLayer, numLayers] at hnotMem)
      simp only [deferredLayerResolutions, publishSelectedDeferredSignature]
      rw [← bind_assoc]
      rw [hschedule]
      rw [hinvariants.1]
      exact evalDist_resolveSelectedLayerValuesList_then_runResolvedObserve
        (observe := observe) table index
        selected.value.selected selected.remaining
          ((publishSelectedChronologicalSignature ftsSecret randomness index leaves ftsPath
            selected.value.selected).run selected.value.cache)
          [topLayer, middleLayer, bottomLayer] selected.context hinvariants.2.1
            hinvariants.2.2.1 (by
              intro lay hlay counter encoding hselection
              exact hinvariants.2.2.2 lay counter encoding hselection)

theorem evalDist_runDeferredChronologicalLayersAndPublish_observe_eq_deferred
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache >>= finishObserve observe) =
      evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath deferredLayerSchedule context fuel cache >>= finishObserve observe) := by
  rw [evalDist_bind, evalDist_bind,
    evalDist_runDeferredChronologicalLayersAndPublish_eq_deferred parameter table ftsSecret
      randomness index leaves ftsPath context fuel cache]

theorem publishedValues_resolveDeferredPositionValue_iff
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredPositionValue position context)) :
    PublishedValues result.state ↔ PublishedValues context.state := by
  rw [resolveDeferredPositionValue_state_eq_clearPending position context result hresult]
  rfl

noncomputable def canonicalContinuationObserve
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (context : DeferredContext) (fuel : Nat) (value : α × SplitHashCache) : ProbComp Bool := by
  classical
  exact if PublishedValues context.state then
      runResolvedFinishIsNone (canonicalizeMaterializedValues table context) fuel table
        ((next value.1).run value.2)
    else
      pure true

instance canonicalContinuationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β) :
    ObserverDooms table (canonicalContinuationObserve table next) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    unfold canonicalContinuationObserve
    split
    next _ =>
      have hcanonicalDoomed :=
        doomedResolvedContext_canonicalizeMaterializedValues
          (table := table) (context := context) ⟨hconsistent, hstarts, hdoomed⟩
      simpa [runResolvedFinishIsNone] using
        evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
          (canonicalizeMaterializedValues table context) fuel table
          ((next value.1).run value.2) hcanonicalDoomed.1 hcanonicalDoomed.2.1
            hcanonicalDoomed.2.2
    next _ => rfl

instance canonicalContinuationObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β) :
    ObserverSynchronized table (canonicalContinuationObserve table next) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    have hpublishedIff : PublishedValues left.state ↔ PublishedValues right.state := by
      simp only [PublishedValues]
      constructor
      · intro hpublished coordinate hrightRevealed
        have hleftRevealed : coordinate ∈ left.state.revealed := by
          rwa [hrevealed]
        rw [← hvalues]
        exact hpublished coordinate hleftRevealed
      · intro hpublished coordinate hleftRevealed
        have hrightRevealed : coordinate ∈ right.state.revealed := by
          rwa [← hrevealed]
        rw [hvalues]
        exact hpublished coordinate hrightRevealed
    unfold canonicalContinuationObserve
    split
    next hleftPublished =>
      have hrightPublished := hpublishedIff.mp hleftPublished
      simp only [hrightPublished, ↓reduceIte]
      have hcanonical := canonicalizedFinalizationContextEq hcontext hrevealed
      apply evalDist_runResolvedFinishIsNone_eq_of_finalizationSynchronized
      · exact hcanonical.1
      · exact hcanonical.2
      · exact hrevealed
    next hleftNotPublished =>
      have hrightNotPublished : ¬PublishedValues right.state := by
        rwa [← hpublishedIff]
      simp [hrightNotPublished]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_canonicalContinuationObserve
    (position : Position)
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (context : DeferredContext) (fuel : Nat) (value : α × SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          canonicalContinuationObserve table next resolved.toDeferredContext fuel value) =
      evalDist (canonicalContinuationObserve table next context fuel value) := by
  by_cases hpublished : PublishedValues context.state
  · let finish : Option DeferredResolution → ProbComp Bool
      | none => pure true
      | some resolved =>
          runResolvedFinishIsNone resolved.toDeferredContext fuel table
            ((next value.1).run value.2)
    have hclean : ∀ coordinate output,
        resolvedCompletionValue table context coordinate = some output →
          ¬context.state.hitAt coordinate output := by
      obtain ⟨completion, hcompletion⟩ := hcompletable
      intro coordinate output hvalue hhit
      have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
      unfold LazyRevealProbe.State.hitAt at hhit
      rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
      exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])
    have hcanonicalValid :
        (canonicalizeMaterializedValues table context).Valid :=
      canonicalizeMaterializedValues_valid table context hvalid hclean
    have hcanonicalCompletable :
        DeferredCompletable table (canonicalizeMaterializedValues table context) := by
      obtain ⟨completion, hcompletion⟩ := hcompletable
      exact ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩
    have hcanonicalEnsured : Coordinate.position position ∈
        (canonicalizeMaterializedValues table context).state.ensured := by
      exact hensured
    calc
      _ = evalDist (((Option.map (canonicalizeDeferredResolution table)) <$>
            resolveDeferredPositionValue position context) >>= finish) := by
          simp only [map_eq_bind_pure_comp, bind_assoc]
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedPublished : PublishedValues resolved.state :=
                (publishedValues_resolveDeferredPositionValue_iff position context resolved
                  hresolved).2 hpublished
              simp [canonicalContinuationObserve, hresolvedPublished, finish,
                canonicalizeDeferredResolution]
      _ = evalDist (resolveDeferredPositionValue position
            (canonicalizeMaterializedValues table context) >>= finish) :=
          evalDist_bind_eq_of_evalDist_eq
            (evalDist_resolveDeferredPositionValue_canonicalize table position context
              hvalid.valuesConsistent hpublished)
            finish
      _ = evalDist (runResolvedFinishIsNone
            (canonicalizeMaterializedValues table context) fuel table
              ((next value.1).run value.2)) := by
          exact evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone position
            ((next value.1).run value.2) (canonicalizeMaterializedValues table context)
              fuel table hcanonicalValid hcanonicalCompletable hcanonicalEnsured
      _ = _ := by
          simp [canonicalContinuationObserve, hpublished]
  · calc
      _ = evalDist (resolveDeferredPositionValue position context >>= fun _ =>
            pure true) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedNotPublished : ¬PublishedValues resolved.state := by
                intro hresolvedPublished
                exact hpublished
                  ((publishedValues_resolveDeferredPositionValue_iff position context resolved
                    hresolved).1 hresolvedPublished)
              simp [canonicalContinuationObserve, hresolvedNotPublished]
      _ = evalDist (pure true : ProbComp Bool) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            (resolveDeferredPositionValue position context)
            (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
            (pure true)
      _ = _ := by
          simp [canonicalContinuationObserve, hpublished]

instance canonicalContinuationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β) :
    ObserverPositionNeutral table (canonicalContinuationObserve table next) where
  eq_resolve position context fuel value hvalid hcompletable hensured :=
    evalDist_resolveDeferredPositionValue_then_canonicalContinuationObserve position table
      next context fuel value hvalid hcompletable hensured

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runCanonicalContinuationObserve
    (position : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (context : DeferredContext) (fuel : Nat)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve (canonicalContinuationObserve table next)
            resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve (canonicalContinuationObserve table next)
        context fuel table computation) := by
  apply evalDist_resolveDeferredPositionValue_then_runResolvedObserve position computation
    (observe := canonicalContinuationObserve table next) context fuel table hvalid hcompletable
      hensured
  intro nextContext remaining value hnextValid hnextCompletable hnextEnsured
  exact evalDist_resolveDeferredPositionValue_then_canonicalContinuationObserve position table
    next nextContext remaining value hnextValid hnextCompletable hnextEnsured

end SphincsSecurity.Concrete.OtsProbeSimulation
