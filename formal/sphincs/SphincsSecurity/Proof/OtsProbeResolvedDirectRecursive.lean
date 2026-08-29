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

set_option maxRecDepth 100000 in
theorem finalizationViewEq_materializeResolvedPositionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hcompletable : DeferredCompletable table
      (materializeResolvedPosition context position result)) :
    FinalizationViewEq table
      (materializeResolvedPosition context position result)
      result.toDeferredContext := by
  have hresultValid := hvalid.of_resolveDeferredPositionValue position result hresult
  have hstateValues := resolveDeferredPositionValue_preserves_state_values position context
    result hresult
  have hpending := resolveDeferredPositionValue_pending position context result hresult
  have hresolved := resolveDeferredPositionValue_resolves position context result hresult
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
    exact deferredCompletion_materializeResolvedPosition_iff position result hstateValues
      hpending hresolved

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_after_materialized_positionValue_observe
    (observe : DeferredContext → ProbComp Bool)
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredPositionValue revealed context)) :
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
  have hrevealedValid := hvalid.of_resolveDeferredPositionValue revealed revealedResult
    hrevealed
  have hstateValues := resolveDeferredPositionValue_preserves_state_values revealed context
    revealedResult hrevealed
  have hpending := resolveDeferredPositionValue_pending revealed context revealedResult
    hrevealed
  have hresolved := resolveDeferredPositionValue_resolves revealed context revealedResult
    hrevealed
  have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed revealedResult
    hrevealedValid hstateValues hresolved
  have hrevealedCompletable :=
    hcompletable.of_resolveDeferredPositionValue hvalid revealed revealedResult hrevealed
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    exact ⟨completion,
      (deferredCompletion_materializeResolvedPosition_iff revealed revealedResult hstateValues
        hpending hresolved).2 hcompletion⟩
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedPositionValue revealed revealedResult hvalid hstarts
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
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hboth
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure rfl
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
          apply relTriple_eqRel_of_evalDist_eq
          rw [hstate, hvalues]

theorem evalDist_resolveDeferredPositionValue_after_materialized_positionValue_runResolvedObserve
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredPositionValue revealed context)) :
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
  evalDist_resolveDeferredPositionValue_after_materialized_positionValue_observe
    (fun nextContext => runResolvedObserve observe nextContext fuel table computation)
    target revealed context revealedResult table hvalid hcompletable hrevealed

noncomputable def directPositionContinuationObserve
    (table : OtsSecretIndex → HashOutput) (revealed : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (_value : Unit) : ProbComp Bool := by
  classical
  exact if context.Valid ∧ DeferredCompletable table context then do
      let resolved ← resolveDeferredPositionValue revealed context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe
            (materializeResolvedPosition context revealed resolved) fuel table
              (next resolved.output)
    else pure true

instance directPositionContinuationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) (revealed : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool) :
    ObserverDooms table (directPositionContinuationObserve table revealed next observe) where
  eq_true context fuel value _hconsistent _hstarts hdoomed := by
    simp [directPositionContinuationObserve, hdoomed]

set_option maxRecDepth 100000 in
instance directPositionContinuationObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput) (revealed : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe] :
    ObserverSynchronized table
      (directPositionContinuationObserve table revealed next observe) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
    have hrightCompletable : DeferredCompletable table right := by
      rcases hleftCompletable with ⟨completion, hcompletion⟩
      exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
    have hleftGuard : left.Valid ∧ DeferredCompletable table left :=
      ⟨hleftValid, hleftCompletable⟩
    have hrightGuard : right.Valid ∧ DeferredCompletable table right :=
      ⟨hrightValid, hrightCompletable⟩
    simp only [directPositionContinuationObserve, if_pos hleftGuard,
      if_pos hrightGuard]
    have hresolved := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table
      revealed left right hview hleftValid hrightValid hleftCompletable
    have hresolvedLeft :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
        (fun result => result ∈ support (resolveDeferredPositionValue revealed left))
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
            have hleftRawCompletable := hrelation.2.2.2.2
            have hrightRawCompletable :
                DeferredCompletable table rightResolved.toDeferredContext := by
              rcases hleftRawCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion,
                (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
            have hleftStateValues := resolveDeferredPositionValue_preserves_state_values
              revealed left leftResolved hleftSupport
            have hrightStateValues := resolveDeferredPositionValue_preserves_state_values
              revealed right rightResolved hrightSupport
            have hleftPending := resolveDeferredPositionValue_pending revealed left leftResolved
              hleftSupport
            have hrightPending := resolveDeferredPositionValue_pending revealed right rightResolved
              hrightSupport
            have hleftValue := resolveDeferredPositionValue_resolves revealed left leftResolved
              hleftSupport
            have hrightValue := resolveDeferredPositionValue_resolves revealed right rightResolved
              hrightSupport
            have hleftMaterializedCompletable : DeferredCompletable table
                (materializeResolvedPosition left revealed leftResolved) := by
              rcases hleftRawCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion,
                (deferredCompletion_materializeResolvedPosition_iff revealed leftResolved
                  hleftStateValues hleftPending hleftValue).2 hcompletion⟩
            have hrightMaterializedCompletable : DeferredCompletable table
                (materializeResolvedPosition right revealed rightResolved) := by
              rcases hrightRawCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion,
                (deferredCompletion_materializeResolvedPosition_iff revealed rightResolved
                  hrightStateValues hrightPending hrightValue).2 hcompletion⟩
            have hleftMaterializedView :=
              finalizationViewEq_materializeResolvedPositionValue revealed leftResolved
                hleftValid hview.leftStarts hleftSupport hleftMaterializedCompletable
            have hrightMaterializedView :=
              finalizationViewEq_materializeResolvedPositionValue revealed rightResolved
                hrightValid hview.rightStarts hrightSupport hrightMaterializedCompletable
            have hleftResultValid := hleftValid.of_resolveDeferredPositionValue revealed
              leftResolved hleftSupport
            have hrightResultValid := hrightValid.of_resolveDeferredPositionValue revealed
              rightResolved hrightSupport
            have hleftMaterializedValid := hleftValid.materializeResolvedPosition_of revealed
              leftResolved hleftResultValid hleftStateValues hleftValue
            have hrightMaterializedValid := hrightValid.materializeResolvedPosition_of revealed
              rightResolved hrightResultValid hrightStateValues hrightValue
            apply relTriple_eqRel_of_evalDist_eq
            simpa only [hrelation.1] using
              (evalDist_runResolvedObserve_eq_of_finalizationSynchronized
                (next leftResolved.output)
                (materializeResolvedPosition left revealed leftResolved)
                (materializeResolvedPosition right revealed rightResolved) fuel table
                ⟨hleftMaterializedView.trans
                    (hrelation.2.1.trans hrightMaterializedView.symm),
                  hleftMaterializedValid, hrightMaterializedValid,
                  hleftMaterializedCompletable⟩
                (by
                  change Function.update left.state.values (.position revealed)
                      (some leftResolved.output) =
                    Function.update right.state.values (.position revealed)
                      (some rightResolved.output)
                  rw [hrelation.1, hvalues])
                (by
                  simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using
                    hrevealed))

set_option maxRecDepth 100000 in
instance directPositionContinuationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput) (revealed : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe] :
    ObserverPositionNeutral table
      (directPositionContinuationObserve table revealed next observe) where
  eq_resolve target context fuel value hvalid hcompletable _hensured := by
    let resolver : PrivateResolver := fun nextContext =>
      resolveDeferredPositionValue revealed nextContext
    let continuation : Option RevealedResolution → ProbComp Bool
      | none => pure true
      | some resolved =>
          runResolvedObserve observe
            { state := (context.state.clearPending (.position target)).materialize
                (.position revealed) resolved.output
              values := resolved.context.values }
            fuel table (next resolved.output)
    rw [directPositionContinuationObserve, if_pos ⟨hvalid, hcompletable⟩]
    calc
      _ = evalDist (resolvePositionThenResolver target resolver context >>= continuation) := by
        unfold resolvePositionThenResolver resolver continuation
        simp only [bind_assoc]
        apply evalDist_bind_congr
        intro targetResult htargetResult
        cases targetResult with
        | none => rfl
        | some targetResult =>
            have htargetValid := hvalid.of_resolveDeferredPositionValue target targetResult
              htargetResult
            have htargetCompletable := hcompletable.of_resolveDeferredPositionValue hvalid
              target targetResult htargetResult
            have htargetGuard : targetResult.toDeferredContext.Valid ∧
                DeferredCompletable table targetResult.toDeferredContext :=
              ⟨htargetValid, htargetCompletable⟩
            simp only [directPositionContinuationObserve, if_pos htargetGuard]
            simp only [bind_assoc]
            apply evalDist_bind_congr
            intro revealedResult _hrevealedResult
            cases revealedResult with
            | none => rfl
            | some revealedResult =>
                have hstate := resolveDeferredPositionValue_state_eq_clearPending target context
                  targetResult htargetResult
                simp only [materializeResolvedPosition, pure_bind]
                rw [hstate]
      _ = evalDist (resolveResolverThenPosition target resolver context >>= continuation) :=
        evalDist_bind_eq_of_evalDist_eq
          (positionResolutionCommutes_value target revealed context) continuation
      _ = evalDist (resolveDeferredPositionValue revealed context >>= fun revealedResult =>
            match revealedResult with
            | none => pure true
            | some revealedResult =>
                resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
                  fun targetResult =>
                    match targetResult with
                    | none => pure true
                    | some targetResult =>
                        runResolvedObserve observe
                          { state := (context.state.clearPending
                                (.position target)).materialize
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
      _ = evalDist (resolveDeferredPositionValue revealed context >>= fun revealedResult =>
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
              evalDist_resolveDeferredPositionValue_after_materialized_positionValue_runResolvedObserve
                target revealed context revealedResult table fuel
                  (next revealedResult.output) observe hvalid hcompletable hrevealedResult
            have hstateValues := resolveDeferredPositionValue_preserves_state_values revealed
              context revealedResult hrevealedResult
            have hpending := resolveDeferredPositionValue_pending revealed context
              revealedResult hrevealedResult
            have hresolved := resolveDeferredPositionValue_resolves revealed context
              revealedResult hrevealedResult
            have hrevealedValid := hvalid.of_resolveDeferredPositionValue revealed
              revealedResult hrevealedResult
            have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed
              revealedResult hrevealedValid hstateValues hresolved
            have hrawCompletable := hcompletable.of_resolveDeferredPositionValue hvalid
              revealed revealedResult hrevealedResult
            have hmaterializedCompletable : DeferredCompletable table
                (materializeResolvedPosition context revealed revealedResult) := by
              rcases hrawCompletable with ⟨completion, hcompletion⟩
              exact ⟨completion,
                (deferredCompletion_materializeResolvedPosition_iff revealed revealedResult
                  hstateValues hpending hresolved).2 hcompletion⟩
            exact htransport.trans
              (evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
                (observe := observe) target (next revealedResult.output)
                  (materializeResolvedPosition context revealed revealedResult) fuel table
                    hmaterializedValid hmaterializedCompletable)
      _ = _ := by
        rfl

theorem evalDist_resolveDeferredReveal_then_directPositionContinuationObserve
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure true
      | some resolved =>
          directPositionContinuationObserve table position next observe
            resolved.toDeferredContext fuel ()) =
      evalDist (directPositionContinuationObserve table position next observe
        context fuel ()) := by
  exact evalDist_resolveDeferredReveal_then_runResolvedObserve_any
    (observe := directPositionContinuationObserve table position next observe)
    table position context fuel (pure ()) hvalid hcompletable

theorem privateStateAgrees_resolveDeferredReveal
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    PrivateStateAgrees result.toDeferredContext context := by
  classical
  unfold resolveDeferredReveal at hresult
  by_cases hresolvable : ResolvableOtsPosition position
  · simp only [hresolvable, if_pos] at hresult
    cases position with
    | chain lay tree leafIdx chainIdx step =>
        exact privateStateAgrees_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          (step.val + 1) (by have := step.isLt; omega) context result hresult
    | leaf lay tree leafIdx =>
        exact privateStateAgrees_resolveDeferredOtsLeaf table lay tree leafIdx context result
          hresult
    | node lay tree level nodeIdx =>
        exact privateStateAgrees_resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
          (by have := level.isLt; omega) context result hresult
    | ftsLeaf index tree leafIdx => simp [ResolvableOtsPosition] at hresolvable
    | ftsNode index tree level nodeIdx => simp [ResolvableOtsPosition] at hresolvable
    | ftsRoots index => simp [ResolvableOtsPosition] at hresolvable
  · simp only [hresolvable] at hresult
    exact privateStateAgrees_resolveDeferredPositionValue position context result hresult

set_option maxRecDepth 100000 in
theorem evalDist_materializedDeferredReveal_eq_directPositionContinuationObserve
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (resolved : DeferredResolution) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hmissing : context.state.values (.position position) = none)
    (hresolved : some resolved ∈ support
      (resolveDeferredReveal table position context)) :
    evalDist (runResolvedObserve observe
      (materializeResolvedPosition context position resolved) fuel table
        (next resolved.output)) =
      evalDist (directPositionContinuationObserve table position next observe
        resolved.toDeferredContext fuel ()) := by
  have hrawValid := hvalid.of_resolveDeferredReveal table position resolved hresolved
  have hrawCompletable :=
    hcompletable.of_resolveDeferredReveal hvalid position resolved hresolved
  have hrawGuard : resolved.toDeferredContext.Valid ∧
      DeferredCompletable table resolved.toDeferredContext :=
    ⟨hrawValid, hrawCompletable⟩
  rw [directPositionContinuationObserve, if_pos hrawGuard]
  have hprivate := privateStateAgrees_resolveDeferredReveal table position context resolved
    hresolved
  have hrawMissing : resolved.state.values (.position position) = none := by
    rw [hprivate.1]
    exact hmissing
  have hrawValue : resolved.values position = some resolved.output := by
    have hvalue := resolveDeferredReveal_resolves table position context resolved hresolved
    simpa [DeferredContext.positionValue, hrawMissing] using hvalue
  have hpendingSubset := resolveDeferredReveal_pendingAway_subset table position context
    resolved hresolved
  have hclear : resolved.state.clearPending (.position position) = resolved.state := by
    cases hstate : resolved.state with
    | mk pending values revealed ensured =>
        simp only [hstate] at hpendingSubset
        simp only [LazyRevealProbe.State.clearPending]
        congr 1
        apply Finset.filter_eq_self.2
        intro entry hentry
        have horiginal := hpendingSubset hentry
        exact (Finset.mem_filter.1 horiginal).2
  have hrawNotHit : ¬resolved.state.hitAt (.position position) resolved.output := by
    rw [← hclear]
    exact not_hitAt_clearPending_self resolved.state (.position position) resolved.output
  rw [resolveDeferredPositionValue_of_deferred_value position resolved.toDeferredContext
    resolved.output hrawMissing hrawValue, if_neg hrawNotHit]
  simp only [pure_bind]
  let repeated : DeferredResolution :=
    ⟨resolved.toDeferredContext, resolved.output⟩
  have hrepeated : some repeated ∈ support
      (resolveDeferredPositionValue position resolved.toDeferredContext) := by
    rw [resolveDeferredPositionValue_of_deferred_value position resolved.toDeferredContext
      resolved.output hrawMissing hrawValue, if_neg hrawNotHit]
    simp [repeated, hclear]
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context
    resolved hresolved
  have hrawPending := resolveDeferredPositionValue_pending position resolved.toDeferredContext
    repeated hrepeated
  have hrawPosition := resolveDeferredPositionValue_resolves position
    resolved.toDeferredContext repeated hrepeated
  have hmaterializedCompletable : DeferredCompletable table
      (materializeResolvedPosition context position resolved) := by
    rcases hrawCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion,
      (deferredCompletion_materializeResolvedReveal_iff position resolved hvalid
        (startTableAgrees_of_deferredCompletable hcompletable) hresolved).2 hcompletion⟩
  have hrepeatedCompletable : DeferredCompletable table repeated.toDeferredContext := by
    exact hrawCompletable.of_resolveDeferredPositionValue hrawValid position repeated hrepeated
  have hrepeatedMaterializedCompletable : DeferredCompletable table
      (materializeResolvedPosition resolved.toDeferredContext position repeated) := by
    rcases hrepeatedCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion,
      (deferredCompletion_materializeResolvedPosition_iff
        (context := resolved.toDeferredContext) position repeated rfl hrawPending
          hrawPosition).2 hcompletion⟩
  have hleftView := finalizationViewEq_materializeResolvedReveal position resolved hvalid
    (startTableAgrees_of_deferredCompletable hcompletable) hresolved hmaterializedCompletable
  have hrightView := finalizationViewEq_materializeResolvedPositionValue position repeated
    hrawValid (startTableAgrees_of_deferredCompletable hrawCompletable) hrepeated
      hrepeatedMaterializedCompletable
  have hleftMaterializedValid := hvalid.materializeResolvedPosition_of position resolved
    hrawValid hstateValues (resolveDeferredReveal_resolves table position context resolved
      hresolved)
  have hrightMaterializedValid := hrawValid.materializeResolvedPosition_of position repeated
    (hrawValid.of_resolveDeferredPositionValue position repeated hrepeated) rfl hrawPosition
  apply evalDist_runResolvedObserve_eq_of_finalizationSynchronized
  · exact ⟨hleftView.trans hrightView.symm, hleftMaterializedValid,
      hrightMaterializedValid, hmaterializedCompletable⟩
  · change Function.update context.state.values (.position position)
        (some resolved.output) =
      Function.update resolved.state.values (.position position) (some repeated.output)
    simp only [repeated]
    rw [hstateValues]
  · simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using
      hprivate.2.1.symm

set_option maxRecDepth 100000 in
theorem evalDist_recursiveReveal_eq_directPositionValue
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hmissing : context.state.values (.position position) = none) :
    evalDist (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedObserve observe
            (materializeResolvedPosition context position resolved) fuel table
              (next resolved.output)) =
      evalDist (do
        let resolved ← resolveDeferredPositionValue position context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedObserve observe
              (materializeResolvedPosition context position resolved) fuel table
                (next resolved.output)) := by
  calc
    _ = evalDist (do
        let resolved ← resolveDeferredReveal table position context
        match resolved with
        | none => pure true
        | some resolved =>
            directPositionContinuationObserve table position next observe
              resolved.toDeferredContext fuel ()) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          exact evalDist_materializedDeferredReveal_eq_directPositionContinuationObserve table
            position context resolved fuel next hvalid hcompletable hmissing hresolved
    _ = evalDist (directPositionContinuationObserve table position next observe
          context fuel ()) :=
      evalDist_resolveDeferredReveal_then_directPositionContinuationObserve table position
        context fuel next hvalid hcompletable
    _ = _ := by
      have hguard : context.Valid ∧ DeferredCompletable table context :=
        ⟨hvalid, hcompletable⟩
      simp only [directPositionContinuationObserve, if_pos hguard]

theorem DeferredContext.ValuesConsistent.materializeResolvedPositionValue_of
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    (materializeResolvedPosition context position result).ValuesConsistent := by
  have hresultConsistent := hconsistent.of_resolveDeferredPositionValue position result hresult
  have hstateValues := resolveDeferredPositionValue_preserves_state_values position context
    result hresult
  intro other output hvalue
  by_cases heq : other = position
  · subst other
    have hsame : output = result.output := by
      simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using hvalue.symm
    rw [hsame]
    exact resolveDeferredPositionValue_installs position context result hresult
  · apply hresultConsistent other output
    rw [hstateValues]
    simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize,
      Function.update_of_ne,
      show Coordinate.position other ≠ Coordinate.position position by simpa using heq]
      using hvalue

theorem DeferredCompletion.of_materializedResolvedPositionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hcompletion : DeferredCompletion table
      (_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition
        context position result) completion) :
    DeferredCompletion table context completion := by
  have hstateValues := resolveDeferredPositionValue_preserves_state_values position context
    result hresult
  have hpending := resolveDeferredPositionValue_pending position context result hresult
  have hresolved := resolveDeferredPositionValue_resolves position context result hresult
  have hraw := hcompletion.of_materializeResolvedPosition position result hstateValues
    (by rw [hpending]) hresolved
  exact hraw.of_resolveDeferredPositionValue_of_valuesConsistent hconsistent position result hresult

set_option maxRecDepth 100000 in
theorem resolvedCore_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedFromTable] at hresult
      subst result
      exact ⟨rfl, hconsistent, hstarts⟩
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (hconsistent.ensure coordinate) (hstarts.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hconsistent hstarts
                  (by simpa [hrevealed] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate candidate }
                  remaining (hconsistent.addPending coordinate candidate)
                  (hstarts.addPending coordinate candidate)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hconsistent hstarts hresult
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            (hconsistent.publish coordinate) (hstarts.publish coordinate) hresult
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind] at hresult
          cases hvalue : context.state.values coordinate with
          | some output =>
              exact ih output context fuel hconsistent hstarts (by simpa [hvalue] using hresult)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only [hvalue] at hresult
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : context.state.hitAt index.coordinate output
                  · have hhit' : context.state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [index, output, OtsSecretIndex.coordinate] using hhit
                    simp [hhit'] at hresult
                  · have hhit' : ¬context.state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [index, output, OtsSecretIndex.coordinate] using hhit
                    let nextContext : DeferredContext :=
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                    have hnextConsistent : nextContext.ValuesConsistent := by
                      intro position value hknown
                      apply hconsistent position value
                      simpa [nextContext, index, OtsSecretIndex.coordinate,
                        LazyRevealProbe.State.materialize] using hknown
                    have hnextStarts : StartTableAgrees
                        nextContext.state table := by
                      change StartTableAgrees
                        (context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output) table
                      simpa [index, OtsSecretIndex.coordinate] using hstarts.materialize_start index
                    exact ih output nextContext fuel hnextConsistent hnextStarts
                      (by simpa [nextContext, index, output, hvalue, hhit'] using hresult)
              | position position =>
                  simp only [hvalue] at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
                  cases resolvedOption with
                  | none => simp at hrest
                  | some resolved =>
                      have hmaterializedConsistent :=
                        hconsistent.materializeResolvedPositionValue_of position resolved hresolved
                      have hmaterializedStarts : StartTableAgrees
                          (context.state.materialize (.position position) resolved.output) table :=
                        hstarts.materialize_position position resolved.output
                      exact ih resolved.output
                        (materializeResolvedPosition context position resolved) fuel
                        hmaterializedConsistent (by
                          simpa [materializeResolvedPosition] using hmaterializedStarts)
                        (by simpa [hvalue, materializeResolvedPosition] using hrest)

set_option maxRecDepth 100000 in
theorem DeferredCompletion.of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation))
    (hcompletion : DeferredCompletion table result.context completion) :
    DeferredCompletion table context completion := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedFromTable] at hresult
      subst result
      exact hcompletion
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind] at hresult
          have hcurrent := ih () { context with state := context.state.ensure coordinate } fuel
            (hconsistent.ensure coordinate) (hstarts.ensure coordinate) hresult
          exact hcurrent.of_coreEq ⟨rfl, rfl, rfl⟩
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hconsistent hstarts
                  (by simpa [hrevealed] using hresult)
              · have hcurrent := ih ()
                    { context with state := context.state.addPending coordinate candidate }
                    remaining (hconsistent.addPending coordinate candidate)
                    (hstarts.addPending coordinate candidate)
                    (by simpa [hrevealed] using hresult)
                exact hcurrent.of_addPending coordinate candidate
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hconsistent hstarts hresult
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind] at hresult
          have hcurrent := ih () { context with state := context.state.publish coordinate } fuel
            (hconsistent.publish coordinate) (hstarts.publish coordinate) hresult
          exact hcurrent.of_coreEq ⟨rfl, rfl, rfl⟩
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind] at hresult
          cases hvalue : context.state.values coordinate with
          | some output =>
              exact ih output context fuel hconsistent hstarts (by simpa [hvalue] using hresult)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only [hvalue] at hresult
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : context.state.hitAt index.coordinate output
                  · have hhit' : context.state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [index, output, OtsSecretIndex.coordinate] using hhit
                    simp [hhit'] at hresult
                  · have hhit' : ¬context.state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [index, output, OtsSecretIndex.coordinate] using hhit
                    let nextContext : DeferredContext :=
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                    have hnextConsistent : nextContext.ValuesConsistent := by
                      intro position value hknown
                      apply hconsistent position value
                      simpa [nextContext, index, OtsSecretIndex.coordinate,
                        LazyRevealProbe.State.materialize] using hknown
                    have hnextStarts : StartTableAgrees nextContext.state table := by
                      change StartTableAgrees
                        (context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output) table
                      simpa [index, OtsSecretIndex.coordinate] using hstarts.materialize_start index
                    have hcurrent := ih output nextContext fuel hnextConsistent hnextStarts
                      (by simpa [nextContext, index, output, hhit'] using hresult)
                    let resolved : DeferredResolution :=
                      ⟨{ state := context.state.clearPending index.coordinate
                         values := context.values }, output⟩
                    have hresolvedEq : resolveDeferredChainStart table index context =
                        some resolved := by
                      simp [resolveDeferredChainStart, resolved, index, output, hvalue, hhit',
                        OtsSecretIndex.coordinate]
                    have hcurrent' : DeferredCompletion table
                        (materializeResolvedChainStart context index resolved) completion := by
                      simpa [nextContext, resolved, materializeResolvedChainStart, index, output,
                        OtsSecretIndex.coordinate] using hcurrent
                    exact hcurrent'.of_materializeResolvedChainStart' hstarts index resolved
                      hresolvedEq
              | position position =>
                  simp only [hvalue] at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
                  cases resolvedOption with
                  | none => simp at hrest
                  | some resolved =>
                      have hmaterializedConsistent :=
                        hconsistent.materializeResolvedPositionValue_of position resolved hresolved
                      have hmaterializedStarts : StartTableAgrees
                          (context.state.materialize (.position position) resolved.output) table :=
                        hstarts.materialize_position position resolved.output
                      have hcurrent := ih resolved.output
                        (_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition
                          context position resolved) fuel
                        hmaterializedConsistent (by
                          simpa only
                            [_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition]
                            using hmaterializedStarts)
                        (by
                          simpa only
                            [_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition]
                            using hrest)
                      exact hcurrent.of_materializedResolvedPositionValue hconsistent position
                        resolved hresolved

theorem deferredCompletable_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation))
    (hfinal : DeferredCompletable table result.context) :
    DeferredCompletable table context := by
  obtain ⟨completion, hcompletion⟩ := hfinal
  exact ⟨completion, hcompletion.of_mem_runDirectResolvedFromTable computation context fuel table
    result completion hconsistent hstarts hresult⟩

theorem not_deferredCompletable_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation))
    (hdoomed : ¬DeferredCompletable table context) :
    ¬DeferredCompletable table result.context := by
  intro hfinal
  exact hdoomed (deferredCompletable_of_mem_runDirectResolvedFromTable computation context fuel
    table result hconsistent hstarts hresult hfinal)

noncomputable def runDirectResolvedObserve
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool :=
  runDirectResolvedFromTable context fuel table computation >>= finishObserve observe

theorem evalDist_runDirectResolvedObserve_eq_true_of_not_completable
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
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
    evalDist (runDirectResolvedObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  unfold runDirectResolvedObserve
  calc
    _ = evalDist (runDirectResolvedFromTable context fuel table computation >>= fun _ =>
          pure true) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runDirectResolvedFromTable computation context fuel
            table result hconsistent hstarts hresult
          have hstillDoomed := not_deferredCompletable_of_mem_runDirectResolvedFromTable
            computation context fuel table result hconsistent hstarts hresult hdoomed
          exact hobserve result.context result.remaining result.value hcore.2.1 hcore.2.2
            hstillDoomed
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runDirectResolvedFromTable context fuel table computation)
      (by simp [runDirectResolvedFromTable]) (pure true)

theorem evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) [ObserverDooms table observe]
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runDirectResolvedObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) :=
  evalDist_runDirectResolvedObserve_eq_true_of_not_completable observe context fuel table
    computation hconsistent hstarts hdoomed ObserverDooms.eq_true

set_option maxRecDepth 100000 in
theorem evalDist_runResolvedObserve_eq_runDirectResolvedObserve
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runResolvedObserve observe context fuel table computation) =
      evalDist (runDirectResolvedObserve observe context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedObserve, runDirectResolvedObserve, runResolvedFromTable,
        runDirectResolvedFromTable]
  | query_bind input next ih =>
      unfold runResolvedObserve runDirectResolvedObserve
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind,
            runDirectResolvedFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel hvalid hcompletable
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind,
            runDirectResolvedFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel hvalid hcompletable
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind,
            runDirectResolvedFromTable_ensure_query_bind]
          apply ih ()
          · exact hvalid.ensure coordinate
          · exact (deferredCompletable_iff_of_coreEq
              (left := { context with state := context.state.ensure coordinate })
              (right := context) ⟨rfl, rfl, rfl⟩).2 hcompletable
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind,
            runDirectResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => rfl
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining hvalid hcompletable
              · simp only [hrevealed, ↓reduceIte]
                let nextContext : DeferredContext :=
                  { context with state := context.state.addPending coordinate candidate }
                by_cases hnextCompletable : DeferredCompletable table nextContext
                · apply ih () nextContext remaining
                  · exact hvalid.addPending_of_completable coordinate candidate hnextCompletable
                  · exact hnextCompletable
                · have hconsistent := hvalid.valuesConsistent.addPending coordinate candidate
                  have hstarts := (startTableAgrees_of_deferredCompletable hcompletable).addPending
                    coordinate candidate
                  exact (evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                    (observe := observe) nextContext remaining table (next ()) hconsistent hstarts
                      hnextCompletable).trans
                    (evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
                      (observe := observe) nextContext remaining table (next ()) hconsistent hstarts
                        hnextCompletable).symm
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind,
            runDirectResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel hvalid hcompletable
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind,
            runDirectResolvedFromTable_publish_query_bind]
          apply ih ()
          · exact hvalid.publish coordinate
          · exact (deferredCompletable_iff_of_coreEq
              (left := { context with state := context.state.publish coordinate })
              (right := context) ⟨rfl, rfl, rfl⟩).2 hcompletable
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind,
            runDirectResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstarts := startTableAgrees_of_deferredCompletable hcompletable
              have hclean := hcompletable.not_hitAt_chainStart index
              cases hstate : context.state.values index.coordinate with
              | some output =>
                  have houtput := hstarts index output hstate
                  subst output
                  let resolved : DeferredResolution :=
                    ⟨{ state := context.state.clearPending index.coordinate
                       values := context.values }, table index⟩
                  have hresolved : resolveDeferredChainStart table index context =
                      some resolved := by
                    simp [resolveDeferredChainStart, resolved, hstate, hclean]
                  simp only [pure_bind]
                  rw [show resolveDeferredChainStart table
                    ⟨lay, tree, leafIdx, chainIdx⟩ context = some resolved by
                      simpa [index] using hresolved]
                  have hnextValid :
                      (materializeResolvedChainStart context index resolved).Valid := by
                    rw [materializeResolvedChainStart]
                    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
                    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx resolved.output
                  have hnextCompletable := hcompletable.materializeResolvedChainStart hstarts
                    index resolved hresolved
                  have hrawEq := finalizationContextEq_resolveDeferredChainStart_original table
                    index context resolved hvalid hcompletable hresolved
                  have hmatView := finalizationViewEq_materializeResolvedChainStart index resolved
                    hvalid hstarts hresolved hnextCompletable
                  have hstate' : context.state.values
                      (.chainStart lay tree leafIdx chainIdx) =
                        some (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                    simpa [index, OtsSecretIndex.coordinate] using hstate
                  simp only [hstate']
                  calc
                    _ = evalDist (runResolvedObserve observe
                          (materializeResolvedChainStart context index resolved) fuel table
                            (next (table index))) := by
                      rfl
                    _ = evalDist (runResolvedObserve observe context fuel table
                          (next (table index))) := by
                      apply evalDist_runResolvedObserve_eq_of_finalizationSynchronized
                      · exact ⟨hmatView.trans hrawEq.1, hnextValid, hvalid, hnextCompletable⟩
                      · simp only [materializeResolvedChainStart, resolved,
                          LazyRevealProbe.State.materialize]
                        funext coordinate
                        by_cases heq : coordinate = index.coordinate
                        · subst coordinate
                          simpa using hstate.symm
                        · simp [Function.update_of_ne heq]
                      · rfl
                    _ = evalDist (runDirectResolvedObserve observe context fuel table
                          (next (table index))) := ih (table index) context fuel hvalid hcompletable
                    _ = _ := by
                      rfl
              | none =>
                  let resolved : DeferredResolution :=
                    ⟨{ state := context.state.clearPending index.coordinate
                       values := context.values }, table index⟩
                  have hresolved : resolveDeferredChainStart table index context =
                      some resolved := by
                    simp [resolveDeferredChainStart, resolved, hstate, hclean]
                  simp only [pure_bind]
                  rw [show resolveDeferredChainStart table
                    ⟨lay, tree, leafIdx, chainIdx⟩ context = some resolved by
                      simpa [index] using hresolved]
                  have hnextValid :
                      (materializeResolvedChainStart context index resolved).Valid := by
                    rw [materializeResolvedChainStart]
                    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
                    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx resolved.output
                  have hnextCompletable := hcompletable.materializeResolvedChainStart hstarts
                    index resolved hresolved
                  have hstate' : context.state.values
                      (.chainStart lay tree leafIdx chainIdx) = none := by
                    simpa [index, OtsSecretIndex.coordinate] using hstate
                  have hclean' : ¬context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                    simpa [index, OtsSecretIndex.coordinate] using hclean
                  simp only [hstate', hclean', ↓reduceIte]
                  simpa [runResolvedObserve, runDirectResolvedObserve,
                    materializeResolvedChainStart, resolved, index, OtsSecretIndex.coordinate]
                    using ih (table index) (materializeResolvedChainStart context index resolved)
                      fuel hnextValid hnextCompletable
          | position position =>
              cases hstate : context.state.values (.position position) with
              | some output =>
                  calc
                    _ = evalDist (resolveDeferredReveal table position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runResolvedObserve observe
                                (materializeResolvedPosition context position resolved) fuel table
                                  (next resolved.output)) := by
                      rw [bind_assoc]
                      apply evalDist_bind_congr
                      intro resolved _hresolved
                      cases resolved <;> rfl
                    _ = evalDist (resolveDeferredReveal table position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runResolvedObserve observe resolved.toDeferredContext fuel table
                                (next output)) := by
                      apply evalDist_bind_congr
                      intro resolved hresolved
                      cases resolved with
                      | none => rfl
                      | some resolved =>
                          have hstateValues := resolveDeferredReveal_preserves_state_values table
                            position context resolved hresolved
                          have hresolvedValue := resolveDeferredReveal_resolves table position
                            context resolved hresolved
                          have hsame : resolved.output = output := by
                            unfold DeferredContext.positionValue at hresolvedValue
                            rw [hstateValues, hstate] at hresolvedValue
                            exact Option.some.inj hresolvedValue.symm
                          have hrawValid := hvalid.of_resolveDeferredReveal table position resolved
                            hresolved
                          have hrawCompletable := hcompletable.of_resolveDeferredReveal hvalid
                            position resolved hresolved
                          have hnextValid := hvalid.materializeResolvedPosition_of position resolved
                            hrawValid hstateValues hresolvedValue
                          have hnextCompletable : DeferredCompletable table
                              (materializeResolvedPosition context position resolved) := by
                            obtain ⟨completion, hcompletion⟩ := hrawCompletable
                            exact ⟨completion,
                              (deferredCompletion_materializeResolvedReveal_iff position resolved
                                hvalid (startTableAgrees_of_deferredCompletable hcompletable)
                                  hresolved).2 hcompletion⟩
                          have hview := finalizationViewEq_materializeResolvedReveal position
                            resolved hvalid (startTableAgrees_of_deferredCompletable hcompletable)
                              hresolved hnextCompletable
                          simp only
                          rw [hsame]
                          apply evalDist_runResolvedObserve_eq_of_finalizationSynchronized
                          · exact ⟨hview, hnextValid, hrawValid, hnextCompletable⟩
                          · simp only
                              [_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition,
                                LazyRevealProbe.State.materialize]
                            rw [hstateValues]
                            funext coordinate
                            by_cases heq : coordinate = .position position
                            · subst coordinate
                              simpa [hstate] using hsame
                            · simp [Function.update_of_ne heq]
                          · simpa only
                              [_root_.SphincsSecurity.Concrete.OtsProbeSimulation.materializeResolvedPosition,
                                LazyRevealProbe.State.materialize] using
                              (privateStateAgrees_resolveDeferredReveal table position context
                                resolved hresolved).2.1.symm
                    _ = evalDist (runResolvedObserve observe context fuel table (next output)) :=
                      evalDist_resolveDeferredReveal_then_runResolvedObserve_any
                        (observe := observe) table position context fuel (next output) hvalid
                          hcompletable
                    _ = evalDist (runDirectResolvedObserve observe context fuel table
                          (next output)) := ih output context fuel hvalid hcompletable
                    _ = _ := by rfl
              | none =>
                  calc
                    _ = evalDist (resolveDeferredReveal table position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runResolvedObserve observe
                                (materializeResolvedPosition context position resolved) fuel table
                                  (next resolved.output)) := by
                      rw [bind_assoc]
                      apply evalDist_bind_congr
                      intro resolved _hresolved
                      cases resolved <;> rfl
                    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runResolvedObserve observe
                                (materializeResolvedPosition context position resolved) fuel table
                                  (next resolved.output)) :=
                      evalDist_recursiveReveal_eq_directPositionValue table position context fuel
                        next hvalid hcompletable hstate
                    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runDirectResolvedObserve observe
                                (materializeResolvedPosition context position resolved) fuel table
                                  (next resolved.output)) := by
                      apply evalDist_bind_congr
                      intro resolved hresolved
                      cases resolved with
                      | none => rfl
                      | some resolved =>
                          have hrawValid := hvalid.of_resolveDeferredPositionValue position
                            resolved hresolved
                          have hstateValues := resolveDeferredPositionValue_preserves_state_values
                            position context resolved hresolved
                          have hpending := resolveDeferredPositionValue_pending position context
                            resolved hresolved
                          have hresolvedValue := resolveDeferredPositionValue_resolves position
                            context resolved hresolved
                          have hnextValid := hvalid.materializeResolvedPosition_of position resolved
                            hrawValid hstateValues hresolvedValue
                          have hrawCompletable := hcompletable.of_resolveDeferredPositionValue
                            hvalid position resolved hresolved
                          have hnextCompletable : DeferredCompletable table
                              (materializeResolvedPosition context position resolved) := by
                            obtain ⟨completion, hcompletion⟩ := hrawCompletable
                            exact ⟨completion,
                              (deferredCompletion_materializeResolvedPosition_iff position resolved
                                hstateValues hpending hresolvedValue).2 hcompletion⟩
                          exact ih resolved.output
                            (materializeResolvedPosition context position resolved) fuel hnextValid
                              hnextCompletable
                    _ = _ := by
                      rw [bind_assoc]
                      apply evalDist_bind_congr
                      intro resolved _hresolved
                      cases resolved <;> rfl

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
