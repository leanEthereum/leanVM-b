import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootCache

/-!
# Layer-root signer comparison

Once a middle or bottom layer root has been materialized, recomputing that tree root returns the
same digest. A proof-only signer can therefore keep the concrete structural computation while
substituting an independent comparison root only in the upper encoding call.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def StoredLayerRoot
    (state : LazyRevealProbe.State Coordinate) (position : Position)
    (root : Digest) : Prop :=
  ∃ output, state.values (.position position) = some output ∧ truncateHash output = root

theorem storedLayerRoot_mono
    {state finalState : LazyRevealProbe.State Coordinate}
    {position : Position} {root : Digest}
    (hroot : StoredLayerRoot state position root)
    (hle : LazyRevealProbe.ValuesLE state finalState) :
    StoredLayerRoot finalState position root := by
  obtain ⟨output, hvalue, hroot⟩ := hroot
  exact ⟨output, hle _ _ hvalue, hroot⟩

theorem StoredLayerRoot.ensure
    {state : LazyRevealProbe.State Coordinate} {position : Position} {root : Digest}
    (hroot : StoredLayerRoot state position root) (coordinate : Coordinate) :
    StoredLayerRoot (state.ensure coordinate) position root :=
  hroot

theorem StoredLayerRoot.addPending
    {state : LazyRevealProbe.State Coordinate} {position : Position} {root : Digest}
    (hroot : StoredLayerRoot state position root)
    (coordinate : Coordinate) (candidate : Digest) :
    StoredLayerRoot (state.addPending coordinate candidate) position root :=
  hroot

theorem StoredLayerRoot.publish
    {state : LazyRevealProbe.State Coordinate} {position : Position} {root : Digest}
    (hroot : StoredLayerRoot state position root) (coordinate : Coordinate) :
    StoredLayerRoot (state.publish coordinate) position root :=
  hroot

theorem StoredLayerRoot.materialize_of_ne
    {state : LazyRevealProbe.State Coordinate} {position : Position} {root : Digest}
    (hroot : StoredLayerRoot state position root)
    (coordinate : Coordinate) (output : HashOutput)
    (hne : coordinate ≠ .position position) :
    StoredLayerRoot (state.materialize coordinate output) position root := by
  obtain ⟨stored, hstored, hroot⟩ := hroot
  refine ⟨stored, ?_, hroot⟩
  simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne.symm] using hstored

set_option maxRecDepth 100000 in
theorem storedLayerRoot_of_mem_runCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (position : Position) (root : Digest)
    (hroot : StoredLayerRoot state position root)
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table computation)) :
    StoredLayerRoot result.state position root := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable] at hresult
      subst result
      exact hroot
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runCleanFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hroot hrest
      | hashOutput =>
          rw [runCleanFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hroot hrest
      | ensure coordinate =>
          rw [runCleanFromTable_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel (hroot.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih () state remaining hroot (by simpa [hrevealed] using hresult)
              · exact ih () (state.addPending coordinate candidate) remaining
                  (hroot.addPending coordinate candidate) (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runCleanFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hroot hresult
      | publish coordinate =>
          rw [runCleanFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel (hroot.publish coordinate) hresult
      | reveal coordinate =>
          rw [runCleanFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state fuel hroot hresult
          | none =>
              have hne : coordinate ≠ .position position := by
                intro heq
                subst coordinate
                obtain ⟨stored, hstored, _⟩ := hroot
                rw [hvalue] at hstored
                simp at hstored
              rw [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only at hresult
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)
                  · rw [if_pos hhit] at hresult
                    simp at hresult
                  · rw [if_neg hhit] at hresult
                    exact ih (table index)
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) (table index))
                      fuel (hroot.materialize_of_ne _ _ hne) (by simpa [index] using hresult)
              | position revealedPosition =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position revealedPosition) output
                  · simp [hhit] at hrest
                  · exact ih output (state.materialize (.position revealedPosition) output)
                      fuel (hroot.materialize_of_ne _ _ hne) (by simpa [hhit] using hrest)

set_option maxRecDepth 100000 in
theorem maskedTreeRoot_eq_of_stored_clean
    (lay : Layer) (tree : TreeIndex)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache)) (root : Digest)
    (hroot : StoredLayerRoot state (layerRootPosition lay tree) root)
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table ((maskedTreeRoot lay tree).run cache))) :
    result.value.1 = root ∧ StoredLayerRoot result.state (layerRootPosition lay tree) root := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  unfold maskedTreeRoot at hresult
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega,
    maskedTreeNode, StateT.run_bind, runCleanFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨administrative, hadministrative, hreveal⟩ := hresult
  cases administrative with
  | none => simp at hreveal
  | some administrative =>
      have hmiddleRoot := storedLayerRoot_of_mem_runCleanFromTable
        ((ensureTreeNode lay tree (layerHeight lay - 1 + 1) 0).run cache)
        state fuel table administrative (layerRootPosition lay tree) root hroot
        hadministrative
      simp only at hreveal
      rw [dif_pos hlevel] at hreveal
      obtain ⟨output, hstored, htruncate⟩ := hmiddleRoot
      change some result ∈ support
        (runCleanFromTable administrative.state administrative.remaining administrative.table
          ((revealCoordinate (.position (layerRootPosition lay tree))).run
            administrative.value.2)) at hreveal
      rw [runCleanFromTable_revealCoordinate_of_value _ output _ _ _ _ hstored] at hreveal
      simp at hreveal
      subst result
      exact ⟨htruncate, ⟨output, hstored, htruncate⟩⟩

set_option maxRecDepth 100000 in
theorem maskedTreeRoot_eq_of_stored
    (lay : Layer) (tree : TreeIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (value : Digest) (output : HashOutput)
    (hvalue : state.values (.position (layerRootPosition lay tree)) = some output)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((maskedTreeRoot lay tree).run cache))) :
    value = truncateHash output := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  unfold maskedTreeRoot at hresult
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega,
    maskedTreeNode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨administrative, hadministrative, hreveal⟩ := hresult
  cases administrative with
  | stopped hit => simp at hreveal
  | done middleState middleRemaining administrativeResult =>
      rcases administrativeResult with ⟨_, middleCache⟩
      have hpreserved := preservesCoordinate_ensureTreeNode
        (.position (layerRootPosition lay tree)) lay tree (layerHeight lay - 1 + 1) 0
        state cache fuel middleState middleRemaining () middleCache hadministrative
      have hmiddleValue : middleState.values (.position (layerRootPosition lay tree)) =
          some output := hpreserved.1.trans hvalue
      simp only at hreveal
      rw [dif_pos hlevel] at hreveal
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw middleState middleRemaining
          ((revealCoordinate (.position (layerRootPosition lay tree))).run middleCache)) at hreveal
      rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind, hmiddleValue] at hreveal
      simp [LazyRevealProbe.runRaw] at hreveal
      exact hreveal.2.2.1

noncomputable def maskedSignLayerWithComparisonRoot
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (comparisonRoot : Digest) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) := do
  let _ ← maskedLayerMessage parameter ftsSecret index lay
  maskedOtsLayerAfterMessage parameter index lay comparisonRoot

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_maskedSignLayer_comparisonRoot_of_message
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hnotBottom : lay ≠ bottomLayer)
    (leftRoot rightRoot : Digest)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter (layerMessagePosition index lay)
      leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hmessageRoot : ∀ result,
      some result ∈ support (runCleanFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
      result.value.1 = leftRoot) :
    RelTriple
      (runCleanFromTable state fuel table
        ((maskedSignLayer parameter ftsSecret index lay).run leftCache))
      (runCleanFromTable state fuel table
        ((maskedSignLayerWithComparisonRoot parameter ftsSecret index lay rightRoot).run
          rightCache))
      (RootEncodingCleanSameRel parameter (layerMessagePosition index lay)
        leftRoot rightRoot) := by
  unfold maskedSignLayer maskedSignLayerWithComparisonRoot
  change RelTriple
    (runCleanFromTable state fuel table
      ((maskedLayerMessage parameter ftsSecret index lay >>= fun message =>
        maskedOtsLayerAfterMessage parameter index lay message).run leftCache))
    (runCleanFromTable state fuel table
      ((maskedLayerMessage parameter ftsSecret index lay >>= fun _ =>
        maskedOtsLayerAfterMessage parameter index lay rightRoot).run rightCache)) _
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  let leftMessageRun := runCleanFromTable state fuel table
    ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)
  have hmessages := rootEncodingCacheCouples_maskedLayerMessage parameter
    (layerMessagePosition index lay) leftRoot rightRoot ftsSecret index lay
      leftCache rightCache hcache state fuel table
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hmessages
      (fun result => result ∈ support leftMessageRun) (fun result hresult => hresult)
  apply relTriple_bind hsupported
  intro leftResult rightResult hresult
  rcases hresult with ⟨hrelation, hleftSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingCleanSameRel] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingCleanSameRel] at hrelation
      | some rightResult =>
          rcases hrelation with ⟨hstate, hremaining, htable, _hmessage, hnextCache⟩
          have hactual := hmessageRoot leftResult hleftSupport
          simp only
          rw [← hstate, ← hremaining, ← htable, hactual]
          exact rootEncodingCacheRelates_maskedOtsLayerAfterMessage parameter index lay
            hnotBottom leftRoot rightRoot leftResult.value.2 rightResult.value.2 hnextCache
              leftResult.state leftResult.remaining leftResult.table

end SphincsSecurity.Concrete.OtsProbeSimulation
