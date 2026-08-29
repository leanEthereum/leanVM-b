import SphincsSecurity.Proof.OtsProbeResolvedDirect
import SphincsSecurity.Proof.OtsProbeResolvedPrivateObserver

/-! Erasure of the recursive work performed by one structural reveal. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DeferredAbsentOn (coordinates : List Coordinate) (context : DeferredContext) : Prop :=
  ∀ position : Position, Coordinate.position position ∈ coordinates →
    context.state.values (.position position) = none → context.values position = none

set_option maxRecDepth 100000 in
theorem finalizeResolvedCoordinates_projects_to_clean_of_absent
    (coordinates : List Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput)
    (hnodup : coordinates.Nodup) (habsent : DeferredAbsentOn coordinates context) :
    (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
        finalizeResolvedCoordinates coordinates context table =
      finalizeCleanFromTable coordinates context.state table := by
  induction coordinates generalizing context with
  | nil => simp [finalizeResolvedCoordinates, finalizeCleanFromTable]
  | cons coordinate remaining ih =>
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      cases hstate : context.state.values coordinate with
      | some output =>
          rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
          simp only [hstate]
          apply ih { context with state := context.state.clearPending coordinate }
            htailNodup
          intro position hmem hmissing
          apply habsent position (List.mem_cons_of_mem coordinate hmem)
          exact hmissing
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstate' : context.state.values index.coordinate = none := by
                simpa [index, OtsSecretIndex.coordinate] using hstate
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredChainStart_of_missing table index context hstate']
              by_cases hhit : context.state.hitAt
                  (.chainStart lay tree leafIdx chainIdx) (table index)
              · simp [index, OtsSecretIndex.coordinate, hhit]
              · simp only [index, OtsSecretIndex.coordinate, hhit, ↓reduceIte,
                    map_eq_bind_pure_comp, pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.chainStart lay tree leafIdx chainIdx)
                      (table index)
                    values := context.values }
                  htailNodup (by
                    intro position hmem hmissing
                    apply habsent position (List.mem_cons_of_mem _ hmem)
                    exact hmissing)
          | position position =>
              have hvalue : context.values position = none :=
                habsent position (by simp) hstate
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit]
              · simp only [hhit, ↓reduceIte, pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.position position) output
                    values := context.values.install position output }
                  htailNodup (by
                    intro other hmem hmissing
                    have hne : other ≠ position := by
                      intro heq
                      subst other
                      exact hnotMem hmem
                    have hmissingOriginal :
                        context.state.values (.position other) = none := by
                      simpa [LazyRevealProbe.State.complete, Function.update_of_ne,
                        show Coordinate.position other ≠ Coordinate.position position by
                          simpa using hne] using hmissing
                    simp [DeferredStructuralValues.install, hne,
                      habsent other (List.mem_cons_of_mem _ hmem) hmissingOriginal])

theorem directDeferredContext_absentOn
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate) :
    DeferredAbsentOn coordinates (directDeferredContext state) := by
  intro position _hmem hvalue
  simpa [directDeferredContext, directDeferredValues] using hvalue

theorem finishResolvedRun_direct_projects_to_clean
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (table : OtsSecretIndex → HashOutput)
    (hcompletable : DeferredCompletable table (directDeferredContext state)) :
    projectResolvedRunResult <$>
        finishResolvedRun
          (some ⟨directDeferredContext state, fuel, value, table⟩) =
      finishCleanRunFromTable (some ⟨state, fuel, value, table⟩) := by
  simp only [finishResolvedRun, hcompletable, ↓reduceIte, finishCleanRunFromTable]
  simp only [show (directDeferredContext state).state = state from rfl]
  have hfinal := finalizeResolvedCoordinates_projects_to_clean_of_absent
    state.coordinates.toList (directDeferredContext state) table state.coordinates.nodup_toList
      (directDeferredContext_absentOn state.coordinates.toList state)
  have hfinal' :
      (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
          finalizeResolvedCoordinates state.coordinates.toList
            (directDeferredContext state) table =
        finalizeCleanFromTable state.coordinates.toList state table := by
    rw [show (directDeferredContext state).state = state from rfl] at hfinal
    exact hfinal
  rw [← hfinal']
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro finalized
  cases finalized <;> simp [projectResolvedRunResult]

theorem evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (table : OtsSecretIndex → HashOutput)
    (hcompletable : DeferredCompletable table (directDeferredContext state)) :
    evalDist (finishResolvedRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) =
      evalDist (finishDirectRunIsNone
        (some ⟨directDeferredContext state, fuel, value, table⟩)) := by
  have hprojection := finishResolvedRun_direct_projects_to_clean state fuel value table
    hcompletable
  unfold finishResolvedRunIsNone finishDirectRunIsNone finishCleanRunIsNone
  simp only [projectResolvedRunResult]
  rw [show (directDeferredContext state).state = state from rfl]
  rw [← hprojection]
  rw [Functor.map_map]
  apply congrArg evalDist
  apply congrArg (fun f : Option (ResolvedRunResult α) → Bool =>
    f <$> finishResolvedRun
      (some ⟨directDeferredContext state, fuel, value, table⟩))
  funext result
  cases result <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_of_synchronized
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (left right : DeferredContext) (fuel : Nat)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position left
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (do
        let resolved ← resolveDeferredPositionValue position right
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hresolved := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table position
    left right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredPositionValue position left))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => exact relTriple_pure_pure rfl
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          apply relTriple_eqRel_of_evalDist_eq
          apply evalDist_runResolvedObserve_eq_of_finalizationSynchronized computation
          · exact ⟨hrelation.2.1, hrelation.2.2.1, hrelation.2.2.2.1,
              hrelation.2.2.2.2⟩
          · rw [resolveDeferredPositionValue_preserves_state_values position left leftResolved
                hleftSupport,
              resolveDeferredPositionValue_preserves_state_values position right rightResolved
                hrightSupport]
            exact hvalues
          · rw [resolveDeferredPositionValue_state_eq_clearPending position left leftResolved
                hleftSupport,
              resolveDeferredPositionValue_state_eq_clearPending position right rightResolved
                hrightSupport]
            simpa [LazyRevealProbe.State.clearPending] using hrevealed

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe] :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  let ensured : DeferredContext :=
    { context with state := context.state.ensure (.position position) }
  have hensuredValid : ensured.Valid := hvalid.ensure (.position position)
  have hensuredCompletable : DeferredCompletable table ensured :=
    hcompletable.ensure (.position position)
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hensuredStarts : StartTableAgrees ensured.state table :=
    hstarts.ensure (.position position)
  have hview : FinalizationViewEq table context ensured :=
    finalizationViewEq_of_deferredCompletion_iff hvalid hensuredValid hstarts hensuredStarts rfl
      hcompletable (fun _ => Iff.rfl)
  have hcontext : FinalizationContextEq table (some context) (some ensured) :=
    ⟨hview, hvalid, hensuredValid, hcompletable⟩
  have hcontextSymm : FinalizationContextEq table (some ensured) (some context) :=
    ⟨hview.symm, hensuredValid, hvalid, hensuredCompletable⟩
  calc
    _ = evalDist (do
        let resolved ← resolveDeferredPositionValue position ensured
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) :=
      evalDist_resolveDeferredPositionValue_then_runResolvedObserve_eq_of_synchronized
        table position computation context ensured fuel hcontext rfl rfl
    _ = evalDist (runResolvedObserve observe ensured fuel table computation) :=
      evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto
        (observe := observe) position computation ensured fuel table hensuredValid
          hensuredCompletable (by simp [ensured, LazyRevealProbe.State.ensure])
    _ = _ :=
      evalDist_runResolvedObserve_eq_of_finalizationSynchronized computation ensured context
        fuel table hcontextSymm rfl rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChainPrefix_then_runResolvedObserve_any
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      evalDist (do
        let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          steps hsteps context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | 0, hsteps, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable => by
      simp only [resolveDeferredChainPrefix, pure_bind]
      exact evalDist_resolveDeferredChainStart_then_runResolvedObserve table
        ⟨lay, tree, leafIdx, chainIdx⟩ context fuel computation hvalid hcompletable
  | steps + 1, hsteps, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable => by
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
              exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
                (observe := observe) position computation previous.toDeferredContext fuel table
                  hpreviousValid hpreviousCompletable
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedObserve_any table lay tree
            leafIdx chainIdx steps (by omega) context fuel computation hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChains_then_runResolvedObserve_any
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ (chains : List ChainIndex) (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      evalDist (do
        let resolved ← resolveDeferredChains table lay tree leafIdx chains context
        match resolved with
        | none => pure true
        | some resolved => runResolvedObserve observe resolved fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | [], context, fuel, computation, observe, _hdooms, _hsynchronized, _hposition,
      _hvalid, _hcompletable => by
      simp [resolveDeferredChains]
  | chainIdx :: remaining, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable => by
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
              exact evalDist_resolveDeferredChains_then_runResolvedObserve_any table lay tree
                leafIdx remaining resolved.toDeferredContext fuel computation hresolvedValid
                  hresolvedCompletable
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedObserve_any table lay tree
            leafIdx chainIdx (chainLength - 1) (by omega) context fuel computation hvalid
              hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve_any
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
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
          exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
            (observe := observe) (.leaf lay tree leafIdx) computation chains fuel table
              hchainsValid hchainsCompletable
    _ = _ := evalDist_resolveDeferredChains_then_runResolvedObserve_any table lay tree
      leafIdx (List.ofFn fun chainIdx : ChainIndex => chainIdx) context fuel computation
        hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredTreeNode_then_runResolvedObserve_any
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      {observe : DeferredContext → Nat → α → ProbComp Bool}
      [ObserverDooms table observe] [ObserverSynchronized table observe]
      [ObserverPositionNeutral table observe],
      context.Valid → DeferredCompletable table context →
      evalDist (do
        let resolved ← resolveDeferredTreeNode table lay tree level nodeIdx hlevel context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedObserve observe context fuel table computation)
  | 0, nodeIdx, hlevel, context, fuel, computation, observe, _hdooms, _hsynchronized,
      _hposition, hvalid, hcompletable =>
      evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve_any table lay tree
        (leafOfNat nodeIdx) context fuel computation hvalid hcompletable
  | level + 1, nodeIdx, hlevel, context, fuel, computation, observe, _hdooms,
      _hsynchronized, _hposition, hvalid, hcompletable => by
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
                      exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
                        (observe := observe)
                        (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) computation
                          rightResult.toDeferredContext fuel table hrightValid
                            hrightCompletable
                _ = _ :=
                  evalDist_resolveDeferredTreeNode_then_runResolvedObserve_any table lay tree
                    level (2 * nodeIdx + 1) (by omega) leftResult.toDeferredContext fuel
                      computation hleftValid hleftCompletable
        _ = _ :=
          evalDist_resolveDeferredTreeNode_then_runResolvedObserve_any table lay tree level
            (2 * nodeIdx) (by omega) context fuel computation hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredReveal_then_runResolvedObserve_any
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hsteps : step.val + 1 ≤ chainLength - 1 := by
        have := step.isLt
        omega
      rw [resolveDeferredReveal, if_pos (by simp [ResolvableOtsPosition])]
      exact evalDist_resolveDeferredChainPrefix_then_runResolvedObserve_any table lay tree
        leafIdx chainIdx (step.val + 1) hsteps context fuel computation hvalid hcompletable
  | leaf lay tree leafIdx =>
      rw [resolveDeferredReveal, if_pos (by simp [ResolvableOtsPosition])]
      exact evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve_any table lay tree
        leafIdx context fuel computation hvalid hcompletable
  | node lay tree level nodeIdx =>
      by_cases hresolvable : ResolvableOtsPosition (.node lay tree level nodeIdx)
      · have hlevel : level.val + 1 ≤ maxLayerHeight := by
          have := level.isLt
          omega
        rw [resolveDeferredReveal, if_pos hresolvable]
        exact evalDist_resolveDeferredTreeNode_then_runResolvedObserve_any table lay tree
          (level.val + 1) nodeIdx hlevel context fuel computation hvalid hcompletable
      · rw [resolveDeferredReveal, if_neg hresolvable]
        exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
          (observe := observe) (.node lay tree level nodeIdx) computation context fuel table
            hvalid hcompletable
  | ftsLeaf index tree leafIdx =>
      rw [resolveDeferredReveal, if_neg (by simp [ResolvableOtsPosition])]
      exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
        (observe := observe) (.ftsLeaf index tree leafIdx) computation context fuel table
          hvalid hcompletable
  | ftsNode index tree level nodeIdx =>
      rw [resolveDeferredReveal, if_neg (by simp [ResolvableOtsPosition])]
      exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
        (observe := observe) (.ftsNode index tree level nodeIdx) computation context fuel table
          hvalid hcompletable
  | ftsRoots index =>
      rw [resolveDeferredReveal, if_neg (by simp [ResolvableOtsPosition])]
      exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
        (observe := observe) (.ftsRoots index) computation context fuel table hvalid
          hcompletable

def RecursiveRevealEnsured (position : Position) (context : DeferredContext) : Prop :=
  match position with
  | .chain lay tree leafIdx chainIdx step =>
      ∀ current : ChainStep, current.val < step.val + 1 →
        Coordinate.position (.chain lay tree leafIdx chainIdx current) ∈
          context.state.ensured
  | .leaf lay tree leafIdx => OtsLeafEnsured lay tree leafIdx context
  | .node lay tree level nodeIdx =>
      TreeNodeEnsured lay tree (level.val + 1) nodeIdx context
  | _ => True

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredReveal_then_runResolvedObserve_of_resolvable
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresolvable : ResolvableOtsPosition position)
    (hensured : RecursiveRevealEnsured position context) :
    evalDist (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedObserve observe context fuel table computation) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hsteps : step.val + 1 ≤ chainLength - 1 := by
        have := step.isLt
        omega
      rw [resolveDeferredReveal, if_pos hresolvable]
      simp only [resolveDeferredPosition]
      change evalDist (do
        let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          (step.val + 1) hsteps context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) = _
      exact evalDist_resolveDeferredChainPrefix_then_runResolvedObserve
        (observe := observe) table lay tree leafIdx chainIdx (step.val + 1)
          hsteps context fuel computation hvalid hcompletable hensured
  | leaf lay tree leafIdx =>
      rw [resolveDeferredReveal, if_pos hresolvable]
      exact evalDist_resolveDeferredOtsLeaf_then_runResolvedObserve
        (observe := observe) table lay tree leafIdx context fuel computation hvalid
          hcompletable hensured
  | node lay tree level nodeIdx =>
      have hlevel : level.val + 1 ≤ maxLayerHeight := by
        have := level.isLt
        omega
      rw [resolveDeferredReveal, if_pos hresolvable]
      simp only [resolveDeferredPosition]
      change evalDist (do
        let resolved ← resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
          hlevel context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe resolved.toDeferredContext fuel table computation) = _
      exact evalDist_resolveDeferredTreeNode_then_runResolvedObserve
        (observe := observe) table lay tree (level.val + 1) nodeIdx
          hlevel context fuel computation hvalid hcompletable hensured
  | ftsLeaf index tree leafIdx =>
      simp [ResolvableOtsPosition] at hresolvable
  | ftsNode index tree level nodeIdx =>
      simp [ResolvableOtsPosition] at hresolvable
  | ftsRoots index =>
      simp [ResolvableOtsPosition] at hresolvable

end SphincsSecurity.Concrete.OtsProbeSimulation
