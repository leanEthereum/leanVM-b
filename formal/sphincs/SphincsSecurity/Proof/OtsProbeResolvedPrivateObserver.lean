import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveFinalization
import SphincsSecurity.Proof.OtsProbeResolvedPrivateInterpreter
import SphincsSecurity.Proof.OtsProbeResolvedPrivateRecursive
import SphincsSecurity.Proof.OtsProbeResolvedSelectionFinalization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedSignLayer

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

def ObserverPositionNeutralAt (table : OtsSecretIndex → HashOutput)
    (position : Position) (observe : DeferredContext → Nat → α → ProbComp Bool) : Prop :=
  ∀ context fuel value,
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
theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto_at
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured)
    [ObserverDooms table observe]
    (hneutral : ObserverPositionNeutralAt table position observe) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  apply evalDist_resolveDeferredPositionValue_then_runResolvedObserve position computation
    context fuel table hvalid hcompletable hensured
  exact hneutral

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

end SphincsSecurity.Concrete.OtsProbeSimulation
