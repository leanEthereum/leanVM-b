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

theorem not_encodingPositionNamesRoot_of_layerMessagePosition_ne
    (target : Position) (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    ¬EncodingPositionNamesRoot target
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ := by
  rintro ⟨otherIndex, htree, hleaf, _hnotBottom, htarget⟩
  apply hne
  rw [htarget]
  exact (layerMessagePosition_eq_of_position_eq otherIndex index lay htree hleaf).symm

theorem rootEncodingCacheCouples_maskedSignLayer_of_layerMessagePosition_ne
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (rootEncodingCacheCouples_maskedLayerMessage parameter target leftRoot rightRoot
    ftsSecret index lay).bind
  intro message
  exact rootEncodingCacheCouples_maskedOtsLayerAfterMessage_of_not_positionNames parameter
    target leftRoot rightRoot index lay message
      (not_encodingPositionNamesRoot_of_layerMessagePosition_ne target index lay hne)

theorem layer_ne_bottom_of_layerMessagePosition_isLayerRoot
    {target : Position} {index : Index} {lay : Layer}
    (htarget : layerMessagePosition index lay = target)
    (hroot : IsLayerRoot target) : lay ≠ bottomLayer := by
  intro hbottom
  subst lay
  obtain ⟨rootLay, rootTree, hrootPosition⟩ := hroot
  rw [layerMessagePosition_bottom] at htarget
  rw [← htarget] at hrootPosition
  simp [layerRootPosition] at hrootPosition

noncomputable def maskedSignLayerWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) :=
  if layerMessagePosition index lay = target then
    maskedSignLayerWithComparisonRoot parameter ftsSecret index lay comparisonRoot
  else
    maskedSignLayer parameter ftsSecret index lay

noncomputable def maskedSignLayersWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Layer → Option (Counter × (ChainIndex → Digit))) :=
  sequenceFin fun lay =>
    maskedSignLayerWithTargetComparison parameter target comparisonRoot ftsSecret index lay

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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_maskedSignLayer_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hmessageRoot : layerMessagePosition index lay = target → ∀ result,
      some result ∈ support (runCleanFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
      result.value.1 = leftRoot) :
    RelTriple
      (runCleanFromTable state fuel table
        ((maskedSignLayer parameter ftsSecret index lay).run leftCache))
      (runCleanFromTable state fuel table
        ((maskedSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay).run
          rightCache))
      (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  by_cases htarget : layerMessagePosition index lay = target
  · rw [maskedSignLayerWithTargetComparison, if_pos htarget]
    rw [← htarget] at hcache ⊢
    exact relTriple_maskedSignLayer_comparisonRoot_of_message parameter ftsSecret index lay
      (layer_ne_bottom_of_layerMessagePosition_isLayerRoot htarget hroot) leftRoot rightRoot
      leftCache rightCache hcache state fuel table (hmessageRoot htarget)
  · rw [maskedSignLayerWithTargetComparison, if_neg htarget]
    exact (rootEncodingCacheCouples_maskedSignLayer_of_layerMessagePosition_ne parameter target
      leftRoot rightRoot ftsSecret index lay htarget).relates leftCache rightCache hcache
        state fuel table

theorem rootEncodingCacheRelates_maskedSignLayers_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index)
    (hmessageRoot : ∀ lay leftCache rightCache,
      RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
      ∀ state fuel table, layerMessagePosition index lay = target → ∀ result,
        some result ∈ support (runCleanFromTable state fuel table
          ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
        result.value.1 = leftRoot) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (sequenceFin fun lay => maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayersWithTargetComparison parameter target rightRoot ftsSecret index) := by
  unfold maskedSignLayersWithTargetComparison
  apply rootEncodingCacheRelates_sequenceFin
  intro lay leftCache rightCache hcache state fuel table
  exact relTriple_maskedSignLayer_targetComparison parameter target hroot leftRoot rightRoot
    ftsSecret index lay leftCache rightCache hcache state fuel table
      (fun htarget => hmessageRoot lay leftCache rightCache hcache state fuel table htarget)

noncomputable def maskedSignAfterDigestWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option Signature) := do
  let ftsPath ← simulateQ ordinaryHashImpl
    (ftsOpen parameter index leaves (ftsSecret index))
  let layers ←
    maskedSignLayersWithTargetComparison parameter target comparisonRoot ftsSecret index
  match traverseOption layers with
  | none => pure none
  | some parts =>
      let revealed ← sequenceFin fun lay => revealLayerValues index lay (parts lay).2
      pure (some
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 })

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem rootEncodingCacheRelates_maskedSignAfterDigest_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hmessageRoot : ∀ lay leftCache rightCache,
      RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
      ∀ state fuel table, layerMessagePosition index lay = target → ∀ result,
        some result ∈ support (runCleanFromTable state fuel table
          ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
        result.value.1 = leftRoot) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves)
      (maskedSignAfterDigestWithTargetComparison parameter target rightRoot ftsSecret
        randomness index leaves) := by
  unfold maskedSignAfterDigest maskedSignAfterDigestWithTargetComparison
  apply (rootEncodingCacheCouples_ftsOpen parameter target leftRoot rightRoot index leaves
    (ftsSecret index)).relates.bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (rootEncodingCacheRelates_maskedSignLayers_targetComparison parameter target hroot
    leftRoot rightRoot ftsSecret index hmessageRoot).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  cases hparts : traverseOption leftLayers with
  | none =>
      exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none).relates
  | some parts =>
      apply (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot
        (fun lay => revealLayerValues index lay (parts lay).2)
        (fun lay => rootEncodingCacheCouples_revealLayerValues parameter target leftRoot
          rightRoot index lay (parts lay).2)).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := leftPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
        (some signature)).relates

noncomputable def maskedSignWithTargetComparison
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option Signature) := do
  let secretKey : SecretKey :=
    ⟨parameter, publicRoot, fun _ _ _ _ => 0, ftsSecret⟩
  match ← simulateQ ordinaryRomImpl
      (signDigestLoop digestAttemptLimit secretKey message) with
  | none => pure none
  | some (randomness, index, leaves) =>
      maskedSignAfterDigestWithTargetComparison parameter target comparisonRoot ftsSecret
        randomness index leaves

theorem rootEncodingCacheRelates_maskedSign_targetComparison
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (hmessageRoot : ∀ index lay leftCache rightCache,
      RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
      ∀ state fuel table, layerMessagePosition index lay = target → ∀ result,
        some result ∈ support (runCleanFromTable state fuel table
          ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
        result.value.1 = leftRoot) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (maskedSign parameter publicRoot ftsSecret message)
      (maskedSignWithTargetComparison parameter publicRoot target rightRoot ftsSecret message) := by
  unfold maskedSign maskedSignWithTargetComparison
  let secretKey : SecretKey :=
    ⟨parameter, publicRoot, fun _ _ _ _ => 0, ftsSecret⟩
  apply (rootEncodingCacheCouples_signDigestLoop target leftRoot rightRoot secretKey message
    digestAttemptLimit).relates.bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none =>
      exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none).relates
  | some selected =>
      exact rootEncodingCacheRelates_maskedSignAfterDigest_targetComparison parameter target
        hroot leftRoot rightRoot ftsSecret selected.1 selected.2.1 selected.2.2
          (hmessageRoot selected.2.1)

end SphincsSecurity.Concrete.OtsProbeSimulation
