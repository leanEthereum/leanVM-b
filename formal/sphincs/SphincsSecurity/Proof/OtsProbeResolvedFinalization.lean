import SphincsSecurity.Proof.OtsProbeResolvedSchedule
import SphincsSecurity.Proof.OtsProbeChronologicalTerminal

/-!
# Finalization equivalence for one-time layer resolution

The materializing chronological signer and the private deferred scheduler expose the same values
and retain the same clean completion distribution. This file lifts that relation through the two
finite families that resolve a selected one-time layer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def FinalizationContextValueEq (table : OtsSecretIndex → HashOutput) :
    Option (DeferredContext × α) → Option (DeferredContext × α) → Prop
  | none, none => True
  | some left, some right =>
      left.2 = right.2 ∧
        FinalizationContextEq table (some left.1) (some right.1)
  | _, _ => False

def FinalizationRunContextValueEq (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (initialOrdinaryCache : QueryCache HashSpec) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (DeferredContext × α) → Prop
  | none, none => True
  | some left, some right =>
      left.value.1 = right.2 ∧
        FinalizationContextEq table (some left.context) (some right.1) ∧
        left.remaining = fuel ∧ left.table = table ∧
        ordinaryQueryCache left.value.2 = initialOrdinaryCache
  | _, _ => False

def FinalizationRunResolutionEq (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (initialOrdinaryCache : QueryCache HashSpec) :
    Option (ResolvedRunResult (Digest × SplitHashCache)) →
      Option DeferredResolution → Prop
  | none, none => True
  | some left, some right =>
      left.value.1 = truncateHash right.output ∧
        FinalizationContextEq table (some left.context) (some right.toDeferredContext) ∧
        left.remaining = fuel ∧ left.table = table ∧
        ordinaryQueryCache left.value.2 = initialOrdinaryCache
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealPosition_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table ((revealPosition position).run cache))
      (resolveDeferredReveal table position right)
      (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache)) := by
  rw [runResolvedFromTable_revealPosition]
  rw [← bind_pure (resolveDeferredReveal table position right)]
  have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table position left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredReveal table position left))
      (fun result hresult => hresult)
  apply relTriple_bind hresolvedSupport
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨hrelation, hleftSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => exact relTriple_pure_pure trivial
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hmaterializedCompletable : DeferredCompletable table
              (materializeResolvedPosition left position leftResolved) := by
            rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
            exact ⟨completion,
              (deferredCompletion_materializeResolvedReveal_iff position leftResolved
                hleftValid hview.leftStarts hleftSupport).mpr hcompletion⟩
          have hmaterializedView := finalizationViewEq_materializeResolvedReveal position
            leftResolved hleftValid hview.leftStarts hleftSupport hmaterializedCompletable
          have hresultValid := hleftValid.of_resolveDeferredReveal table position leftResolved
            hleftSupport
          have hstateValues := resolveDeferredReveal_preserves_state_values table position left
            leftResolved hleftSupport
          have hresolvedValue := resolveDeferredReveal_resolves table position left leftResolved
            hleftSupport
          have hmaterializedValid :
              (materializeResolvedPosition left position leftResolved).Valid :=
            hleftValid.materializeResolvedPosition_of position leftResolved hresultValid
              hstateValues hresolvedValue
          apply relTriple_pure_pure
          refine ⟨?_, ?_, rfl, rfl, ordinaryQueryCache_update_hidden cache
            (.position position) leftResolved.output⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hmaterializedView.trans hrelation.2.1, hmaterializedValid,
              hrelation.2.2.2.1, hmaterializedCompletable⟩

theorem relTriple_runResolvedFromTable_revealChainStart_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((revealChainStart index.lay index.tree index.leafIdx index.chainIdx).run cache))
      (pure (resolveDeferredChainStart table index right) :
        ProbComp (Option DeferredResolution))
      (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache)) := by
  rw [revealChainStart, runResolvedFromTable_revealCoordinate]
  have hresolved := relTriple_resolveDeferredChainStart_of_finalizationViewEq table index left
    right hview hleftValid hrightValid hleftCompletable
  have hresolvedSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (pure (resolveDeferredChainStart table index left)))
      (fun result hresult => hresult)
  change RelTriple
    ((pure (resolveDeferredChainStart table index left) :
        ProbComp (Option DeferredResolution)) >>= fun resolved =>
      match resolved with
      | none => pure none
      | some resolved => pure (some ⟨
          materializeResolvedChainStart left index resolved,
          fuel,
          (truncateHash resolved.output,
            Function.update cache (.hidden index.coordinate) (some resolved.output)),
          table⟩))
    ((pure (resolveDeferredChainStart table index right) :
        ProbComp (Option DeferredResolution)) >>= pure)
    (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache))
  apply relTriple_bind hresolvedSupport
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨hrelation, hleftSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => exact relTriple_pure_pure trivial
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          have hleftResult : resolveDeferredChainStart table index left = some leftResolved := by
            simpa using hleftSupport.symm
          have hmaterializedCompletable := hleftCompletable.materializeResolvedChainStart
            hview.leftStarts index leftResolved hleftResult
          have hmaterializedView := finalizationViewEq_materializeResolvedChainStart index
            leftResolved hleftValid hview.leftStarts hleftResult hmaterializedCompletable
          have hmaterializedValid :
              (materializeResolvedChainStart left index leftResolved).Valid := by
            unfold materializeResolvedChainStart
            rw [resolveDeferredChainStart_deferred_values_eq table index left leftResolved
              hleftResult]
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            exact hleftValid.materialize_chainStart lay tree leafIdx chainIdx leftResolved.output
          apply relTriple_pure_pure
          refine ⟨?_, ?_, rfl, rfl, ordinaryQueryCache_update_hidden cache index.coordinate
            leftResolved.output⟩
          · simpa using congrArg truncateHash hrelation.1
          · exact ⟨hmaterializedView.trans hrelation.2.1, hmaterializedValid,
              hrelation.2.2.2.1, hmaterializedCompletable⟩

theorem relTriple_runResolvedFromTable_revealPrivateChainValue_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((revealCoordinate (chainValueCoordinate lay tree leafIdx chainIdx digit)).run cache))
      (resolveDeferredChainPrefix table lay tree leafIdx chainIdx digit.val
        (by have := digit.isLt; omega) right)
      (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache)) := by
  by_cases hzero : digit.val = 0
  · simpa [chainValueCoordinate, hzero, revealChainStart, resolveDeferredChainPrefix] using
      (relTriple_runResolvedFromTable_revealChainStart_of_finalizationViewEq table
        ⟨lay, tree, leafIdx, chainIdx⟩ left right fuel cache hview hleftValid hrightValid
        hleftCompletable)
  · let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    have hstep : step.val + 1 = digit.val := by
      simp only [step]
      omega
    simpa [chainValueCoordinate, hzero, revealPosition, step, resolveDeferredReveal,
      ResolvableOtsPosition, resolveDeferredPosition, hstep] using
      (relTriple_runResolvedFromTable_revealPosition_of_finalizationViewEq table
        (.chain lay tree leafIdx chainIdx step) left right fuel cache hview hleftValid
        hrightValid hleftCompletable)

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealPrivateChainFamily_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ {n : Nat} (family : Fin n → ChainIndex)
      (digits : Fin n → Digit) (left right : DeferredContext) (fuel : Nat)
      (cache : SplitHashCache),
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (runResolvedFromTable left fuel table
          ((sequenceFin fun position => revealCoordinate
            (chainValueCoordinate lay tree leafIdx (family position)
              (digits position))).run cache))
        (resolveDeferredSelectedChainFamily table lay tree leafIdx family digits right)
        (FinalizationRunContextValueEq table fuel (ordinaryQueryCache cache))
  | 0, family, digits, left, right, fuel, cache, hview, hleftValid, hrightValid,
      hleftCompletable => by
      simp [sequenceFin, resolveDeferredSelectedChainFamily, runResolvedFromTable,
        FinalizationRunContextValueEq, FinalizationContextEq, hview, hleftValid,
        hrightValid, hleftCompletable]
  | n + 1, family, digits, left, right, fuel, cache, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind,
        resolveDeferredSelectedChainFamily]
      have hhead :=
        relTriple_runResolvedFromTable_revealPrivateChainValue_of_finalizationViewEq table lay
          tree leafIdx (family 0) (digits 0) left right fuel cache hview hleftValid hrightValid
          hleftCompletable
      apply relTriple_bind hhead
      intro leftHead rightHead hheadRelation
      cases leftHead with
      | none =>
          cases rightHead with
          | none => exact relTriple_pure_pure trivial
          | some rightHead => simp [FinalizationRunResolutionEq] at hheadRelation
      | some leftHead =>
          cases rightHead with
          | none => simp [FinalizationRunResolutionEq] at hheadRelation
          | some rightHead =>
              simp only
              rw [hheadRelation.2.2.1, hheadRelation.2.2.2.1]
              rw [StateT.run_bind, runResolvedFromTable_bind]
              have htail :=
                relTriple_runResolvedFromTable_revealPrivateChainFamily_of_finalizationViewEq
                  table lay tree leafIdx (fun position : Fin n => family position.succ)
                  (fun position : Fin n => digits position.succ) leftHead.context
                  rightHead.toDeferredContext
                  fuel leftHead.value.2 hheadRelation.2.1.1 hheadRelation.2.1.2.1
                  hheadRelation.2.1.2.2.1 hheadRelation.2.1.2.2.2
              apply relTriple_bind htail
              intro leftTail rightTail htailRelation
              cases leftTail with
              | none =>
                  cases rightTail with
                  | none => exact relTriple_pure_pure trivial
                  | some rightTail => simp [FinalizationRunContextValueEq] at htailRelation
              | some leftTail =>
                  cases rightTail with
                  | none => simp [FinalizationRunContextValueEq] at htailRelation
                  | some rightTail =>
                      apply relTriple_pure_pure
                      refine ⟨?_, htailRelation.2.1, htailRelation.2.2.1,
                        htailRelation.2.2.2.1, ?_⟩
                      · funext position
                        refine Fin.cases ?_ (fun tailPosition => ?_) position
                        · exact hheadRelation.1
                        · exact congrFun htailRelation.1 tailPosition
                      · exact htailRelation.2.2.2.2.trans hheadRelation.2.2.2.2

theorem relTriple_runResolvedFromTable_revealPrivateTreeNode_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((match level with
          | 0 => revealPosition (.leaf lay tree (leafOfNat nodeIdx))
          | current + 1 =>
              if hcurrent : current < maxLayerHeight then
                revealPosition (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx))
              else pure 0).run cache))
      (resolveDeferredTreeNode table lay tree level nodeIdx hlevel right)
      (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache)) := by
  cases level with
  | zero =>
      simpa [resolveDeferredReveal, ResolvableOtsPosition, resolveDeferredPosition,
        resolveDeferredTreeNode] using
        (relTriple_runResolvedFromTable_revealPosition_of_finalizationViewEq table
          (.leaf lay tree (leafOfNat nodeIdx)) left right fuel cache hview hleftValid
          hrightValid hleftCompletable)
  | succ current =>
      have hcurrent : current < maxLayerHeight := by omega
      have hnodeLt : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (current + 1) := pow_pos (by omega) _
        nlinarith
      have hnodeVal : (leafOfNat nodeIdx).val = nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hnodeLt]
      have hresolvable : ResolvableOtsPosition
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) := by
        simp [ResolvableOtsPosition, hnodeVal]
        exact hspan
      simpa [hcurrent, resolveDeferredReveal, hresolvable, resolveDeferredPosition,
        hnodeVal] using
        (relTriple_runResolvedFromTable_revealPosition_of_finalizationViewEq table
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) left right fuel cache
          hview hleftValid hrightValid hleftCompletable)

theorem relTriple_runResolvedFromTable_revealPrivateLayerPathNode_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (level : Fin maxLayerHeight)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((match level.val with
          | 0 => revealPosition (.leaf lay tree
              (leafOfNat (Nat.xor leafIdx.val 1)))
          | current + 1 =>
              if hcurrent : current < maxLayerHeight then
                revealPosition (.node lay tree ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1)))
              else pure 0).run cache))
      (resolveDeferredTreeNode table lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
        (by have := level.isLt; omega) right)
      (FinalizationRunResolutionEq table fuel (ordinaryQueryCache cache)) := by
  have hcomputation :
      (match level.val with
      | 0 => revealPosition (.leaf lay tree
          (leafOfNat (Nat.xor leafIdx.val 1)))
      | current + 1 =>
          if hcurrent : current < maxLayerHeight then
            revealPosition (.node lay tree ⟨current, hcurrent⟩
              (leafOfNat (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1)))
          else pure 0) =
        (match level.val with
        | 0 => revealPosition (.leaf lay tree
            (leafOfNat (Nat.xor (leafIdx.val / 2 ^ level.val) 1)))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPosition (.node lay tree ⟨current, hcurrent⟩
                (leafOfNat (Nat.xor (leafIdx.val / 2 ^ level.val) 1)))
            else pure 0) := by
    cases hvalue : level.val <;> simp
  rw [hcomputation]
  exact
    relTriple_runResolvedFromTable_revealPrivateTreeNode_of_finalizationViewEq table lay tree
      level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      (by have := level.isLt; omega)
      (FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val level.val
        (by have := level.isLt; omega) leafIdx.isLt)
      left right fuel cache hview hleftValid hrightValid hleftCompletable

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealPrivateLayerPathFamily_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ {n : Nat} (family : Fin n → Fin maxLayerHeight)
      (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache),
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (runResolvedFromTable left fuel table
          ((sequenceFin fun position =>
            if (family position).val < layerHeight lay then
              match (family position).val with
              | 0 => revealPosition (.leaf lay tree
                  (leafOfNat (Nat.xor leafIdx.val 1)))
              | current + 1 =>
                  if hcurrent : current < maxLayerHeight then
                    revealPosition (.node lay tree ⟨current, hcurrent⟩
                      (leafOfNat
                        (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1)))
                  else pure 0
            else pure 0).run cache))
        (resolveDeferredLayerPathFamily table lay tree leafIdx family right)
        (FinalizationRunContextValueEq table fuel (ordinaryQueryCache cache))
  | 0, family, left, right, fuel, cache, hview, hleftValid, hrightValid,
      hleftCompletable => by
      simp [sequenceFin, resolveDeferredLayerPathFamily, runResolvedFromTable,
        FinalizationRunContextValueEq, FinalizationContextEq, hview, hleftValid,
        hrightValid, hleftCompletable]
  | n + 1, family, left, right, fuel, cache, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind,
        resolveDeferredLayerPathFamily]
      by_cases hinLayer : (family 0).val < layerHeight lay
      · simp only [hinLayer, ↓reduceIte]
        have hhead :=
          relTriple_runResolvedFromTable_revealPrivateLayerPathNode_of_finalizationViewEq
            table lay tree leafIdx (family 0) left right fuel cache hview hleftValid
            hrightValid hleftCompletable
        apply relTriple_bind hhead
        intro leftHead rightHead hheadRelation
        cases leftHead with
        | none =>
            cases rightHead with
            | none => exact relTriple_pure_pure trivial
            | some rightHead => simp [FinalizationRunResolutionEq] at hheadRelation
        | some leftHead =>
            cases rightHead with
            | none => simp [FinalizationRunResolutionEq] at hheadRelation
            | some rightHead =>
                simp only
                rw [hheadRelation.2.2.1, hheadRelation.2.2.2.1]
                rw [StateT.run_bind, runResolvedFromTable_bind]
                have htail :=
                  relTriple_runResolvedFromTable_revealPrivateLayerPathFamily_of_finalizationViewEq
                    table lay tree leafIdx (fun position : Fin n => family position.succ)
                    leftHead.context rightHead.toDeferredContext fuel leftHead.value.2
                    hheadRelation.2.1.1 hheadRelation.2.1.2.1
                    hheadRelation.2.1.2.2.1 hheadRelation.2.1.2.2.2
                apply relTriple_bind htail
                intro leftTail rightTail htailRelation
                cases leftTail with
                | none =>
                    cases rightTail with
                    | none => exact relTriple_pure_pure trivial
                    | some rightTail =>
                        simp [FinalizationRunContextValueEq] at htailRelation
                | some leftTail =>
                    cases rightTail with
                    | none => simp [FinalizationRunContextValueEq] at htailRelation
                    | some rightTail =>
                        apply relTriple_pure_pure
                        refine ⟨?_, htailRelation.2.1, htailRelation.2.2.1,
                          htailRelation.2.2.2.1, ?_⟩
                        · funext position
                          refine Fin.cases ?_ (fun tailPosition => ?_) position
                          · exact hheadRelation.1
                          · exact congrFun htailRelation.1 tailPosition
                        · exact htailRelation.2.2.2.2.trans hheadRelation.2.2.2.2
      · rw [dif_neg hinLayer]
        simp only [hinLayer, ↓reduceIte]
        have hpure :
            runResolvedFromTable left fuel table
                ((pure 0 : StateT SplitHashCache
                  (OracleComp (LazyRevealProbe.World Coordinate)) Digest).run cache) =
              pure (some ⟨left, fuel, (0, cache), table⟩) := by
          simp [StateT.run_pure, runResolvedFromTable]
        rw [hpure]
        simp only [pure_bind]
        rw [StateT.run_bind, runResolvedFromTable_bind]
        have htail :=
          relTriple_runResolvedFromTable_revealPrivateLayerPathFamily_of_finalizationViewEq
            table lay tree leafIdx (fun position : Fin n => family position.succ)
            left right fuel cache hview hleftValid hrightValid hleftCompletable
        apply relTriple_bind htail
        intro leftTail rightTail htailRelation
        cases leftTail with
        | none =>
            cases rightTail with
            | none => exact relTriple_pure_pure trivial
            | some rightTail => simp [FinalizationRunContextValueEq] at htailRelation
        | some leftTail =>
            cases rightTail with
            | none => simp [FinalizationRunContextValueEq] at htailRelation
            | some rightTail =>
                apply relTriple_pure_pure
                refine ⟨?_, htailRelation.2.1, htailRelation.2.2.1,
                  htailRelation.2.2.2.1, htailRelation.2.2.2.2⟩
                funext position
                refine Fin.cases rfl (fun tailPosition => ?_) position
                exact congrFun htailRelation.1 tailPosition

theorem relTriple_runResolvedFromTable_revealPrivateLayerValues_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (left right : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (runResolvedFromTable left fuel table
        ((revealPrivateLayerValues index lay encoding).run cache))
      (resolveDeferredLayerValues table index lay encoding right)
      (FinalizationRunContextValueEq table fuel (ordinaryQueryCache cache)) := by
  rw [revealPrivateLayerValues, resolveDeferredLayerValues,
    StateT.run_bind, runResolvedFromTable_bind]
  have hchains :=
    relTriple_runResolvedFromTable_revealPrivateChainFamily_of_finalizationViewEq table lay
      (treeIndexAt index lay) (leafIndexAt index lay)
      (fun chainIdx : ChainIndex => chainIdx) encoding left right fuel cache hview
      hleftValid hrightValid hleftCompletable
  apply relTriple_bind hchains
  intro leftChains rightChains hchainsRelation
  cases leftChains with
  | none =>
      cases rightChains with
      | none => exact relTriple_pure_pure trivial
      | some rightChains => simp [FinalizationRunContextValueEq] at hchainsRelation
  | some leftChains =>
      cases rightChains with
      | none => simp [FinalizationRunContextValueEq] at hchainsRelation
      | some rightChains =>
          simp only
          rw [hchainsRelation.2.2.1, hchainsRelation.2.2.2.1]
          rw [StateT.run_bind, runResolvedFromTable_bind]
          have hpath :=
            relTriple_runResolvedFromTable_revealPrivateLayerPathFamily_of_finalizationViewEq
              table lay (treeIndexAt index lay) (leafIndexAt index lay)
              (fun level : Fin maxLayerHeight => level) leftChains.context rightChains.1
              fuel leftChains.value.2 hchainsRelation.2.1.1
              hchainsRelation.2.1.2.1 hchainsRelation.2.1.2.2.1
              hchainsRelation.2.1.2.2.2
          apply relTriple_bind hpath
          intro leftPath rightPath hpathRelation
          cases leftPath with
          | none =>
              cases rightPath with
              | none => exact relTriple_pure_pure trivial
              | some rightPath => simp [FinalizationRunContextValueEq] at hpathRelation
          | some leftPath =>
              cases rightPath with
              | none => simp [FinalizationRunContextValueEq] at hpathRelation
              | some rightPath =>
                  apply relTriple_pure_pure
                  exact ⟨by rw [hchainsRelation.1, hpathRelation.1],
                    hpathRelation.2.1, hpathRelation.2.2.1,
                    hpathRelation.2.2.2.1,
                    hpathRelation.2.2.2.2.trans hchainsRelation.2.2.2.2⟩

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredSelectedChainFamily_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ {n : Nat} (family : Fin n → ChainIndex)
      (digits : Fin n → Digit) (left right : DeferredContext),
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (resolveDeferredSelectedChainFamily table lay tree leafIdx family digits left)
        (resolveDeferredSelectedChainFamily table lay tree leafIdx family digits right)
        (FinalizationContextValueEq table)
  | 0, family, digits, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      simp only [resolveDeferredSelectedChainFamily]
      apply relTriple_pure_pure
      exact ⟨rfl, hview, hleftValid, hrightValid, hleftCompletable⟩
  | n + 1, family, digits, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [resolveDeferredSelectedChainFamily, resolveDeferredSelectedChainFamily]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix_of_finalizationViewEq table lay tree leafIdx
          (family 0) (digits 0).val (by have := (digits 0).isLt; omega) left right hview
          hleftValid hrightValid hleftCompletable)
      intro leftHead rightHead hhead
      cases leftHead with
      | none =>
          cases rightHead with
          | none => simp [FinalizationContextValueEq]
          | some rightHead => simp [FinalizationResolutionEq] at hhead
      | some leftHead =>
          cases rightHead with
          | none => simp [FinalizationResolutionEq] at hhead
          | some rightHead =>
              apply relTriple_bind
                (relTriple_resolveDeferredSelectedChainFamily_of_finalizationViewEq table lay
                  tree leafIdx (fun index : Fin n => family index.succ)
                  (fun index : Fin n => digits index.succ) leftHead.toDeferredContext
                  rightHead.toDeferredContext hhead.2.1 hhead.2.2.1 hhead.2.2.2.1
                  hhead.2.2.2.2)
              intro leftTail rightTail htail
              cases leftTail with
              | none =>
                  cases rightTail with
                  | none => simp [FinalizationContextValueEq]
                  | some rightTail => simp [FinalizationContextValueEq] at htail
              | some leftTail =>
                  cases rightTail with
                  | none => simp [FinalizationContextValueEq] at htail
                  | some rightTail =>
                      apply relTriple_pure_pure
                      refine ⟨?_, htail.2⟩
                      funext position
                      refine Fin.cases ?_ (fun tailPosition => ?_) position
                      · simpa using congrArg truncateHash hhead.1
                      · exact congrFun htail.1 tailPosition

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredLayerPathFamily_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ {n : Nat} (family : Fin n → Fin maxLayerHeight)
      (left right : DeferredContext),
      FinalizationViewEq table left right → left.Valid → right.Valid →
      DeferredCompletable table left →
      RelTriple
        (resolveDeferredLayerPathFamily table lay tree leafIdx family left)
        (resolveDeferredLayerPathFamily table lay tree leafIdx family right)
        (FinalizationContextValueEq table)
  | 0, family, left, right, hview, hleftValid, hrightValid, hleftCompletable => by
      simp only [resolveDeferredLayerPathFamily]
      apply relTriple_pure_pure
      exact ⟨rfl, hview, hleftValid, hrightValid, hleftCompletable⟩
  | n + 1, family, left, right, hview, hleftValid, hrightValid,
      hleftCompletable => by
      rw [resolveDeferredLayerPathFamily, resolveDeferredLayerPathFamily]
      by_cases hinLayer : (family 0).val < layerHeight lay
      · simp only [hinLayer, ↓reduceDIte]
        apply relTriple_bind
          (relTriple_resolveDeferredTreeNode_of_finalizationViewEq table lay tree
            (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
            (by have := (family 0).isLt; omega) left right hview hleftValid hrightValid
            hleftCompletable)
        intro leftHead rightHead hhead
        cases leftHead with
        | none =>
            cases rightHead with
            | none => simp [FinalizationContextValueEq]
            | some rightHead => simp [FinalizationResolutionEq] at hhead
        | some leftHead =>
            cases rightHead with
            | none => simp [FinalizationResolutionEq] at hhead
            | some rightHead =>
                apply relTriple_bind
                  (relTriple_resolveDeferredLayerPathFamily_of_finalizationViewEq table lay tree
                    leafIdx (fun position : Fin n => family position.succ)
                    leftHead.toDeferredContext rightHead.toDeferredContext hhead.2.1
                    hhead.2.2.1 hhead.2.2.2.1 hhead.2.2.2.2)
                intro leftTail rightTail htail
                cases leftTail with
                | none =>
                    cases rightTail with
                    | none => simp [FinalizationContextValueEq]
                    | some rightTail => simp [FinalizationContextValueEq] at htail
                | some leftTail =>
                    cases rightTail with
                    | none => simp [FinalizationContextValueEq] at htail
                    | some rightTail =>
                        apply relTriple_pure_pure
                        refine ⟨?_, htail.2⟩
                        funext position
                        refine Fin.cases ?_ (fun tailPosition => ?_) position
                        · simpa using congrArg truncateHash hhead.1
                        · exact congrFun htail.1 tailPosition
      · simp only [hinLayer, ↓reduceDIte]
        apply relTriple_bind
          (relTriple_resolveDeferredLayerPathFamily_of_finalizationViewEq table lay tree leafIdx
            (fun position : Fin n => family position.succ) left right hview hleftValid
            hrightValid hleftCompletable)
        intro leftTail rightTail htail
        cases leftTail with
        | none =>
            cases rightTail with
            | none => simp [FinalizationContextValueEq]
            | some rightTail => simp [FinalizationContextValueEq] at htail
        | some leftTail =>
            cases rightTail with
            | none => simp [FinalizationContextValueEq] at htail
            | some rightTail =>
                apply relTriple_pure_pure
                refine ⟨?_, htail.2⟩
                funext position
                refine Fin.cases rfl (fun tailPosition => ?_) position
                exact congrFun htail.1 tailPosition

theorem relTriple_resolveDeferredLayerValues_of_finalizationViewEq
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (left right : DeferredContext)
    (hview : FinalizationViewEq table left right)
    (hleftValid : left.Valid) (hrightValid : right.Valid)
    (hleftCompletable : DeferredCompletable table left) :
    RelTriple
      (resolveDeferredLayerValues table index lay encoding left)
      (resolveDeferredLayerValues table index lay encoding right)
      (FinalizationContextValueEq table) := by
  rw [resolveDeferredLayerValues, resolveDeferredLayerValues]
  apply relTriple_bind
    (relTriple_resolveDeferredSelectedChainFamily_of_finalizationViewEq table lay
      (treeIndexAt index lay) (leafIndexAt index lay)
      (fun chainIdx : ChainIndex => chainIdx) encoding left right hview hleftValid hrightValid
      hleftCompletable)
  intro leftChains rightChains hchains
  cases leftChains with
  | none =>
      cases rightChains with
      | none => simp [FinalizationContextValueEq]
      | some rightChains => simp [FinalizationContextValueEq] at hchains
  | some leftChains =>
      cases rightChains with
      | none => simp [FinalizationContextValueEq] at hchains
      | some rightChains =>
          apply relTriple_bind
            (relTriple_resolveDeferredLayerPathFamily_of_finalizationViewEq table lay
              (treeIndexAt index lay) (leafIndexAt index lay)
              (fun level : Fin maxLayerHeight => level) leftChains.1 rightChains.1
              hchains.2.1 hchains.2.2.1 hchains.2.2.2.1 hchains.2.2.2.2)
          intro leftPath rightPath hpath
          cases leftPath with
          | none =>
              cases rightPath with
              | none => simp [FinalizationContextValueEq]
              | some rightPath => simp [FinalizationContextValueEq] at hpath
          | some leftPath =>
              cases rightPath with
              | none => simp [FinalizationContextValueEq] at hpath
              | some rightPath =>
                  apply relTriple_pure_pure
                  exact ⟨by rw [hchains.1, hpath.1], hpath.2⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
