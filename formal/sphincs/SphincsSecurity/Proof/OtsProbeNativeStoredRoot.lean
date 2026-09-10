import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSigner
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem resolveDeferredReveal_preserves_native_value
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (target : Position) (output : HashOutput)
    (hknown : context.positionValue target = some output)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    result.toDeferredContext.positionValue target = some output := by
  unfold resolveDeferredReveal at hresult
  split_ifs at hresult
  · exact resolveDeferredPosition_preserves_positionValue table position context result target output hknown hresult
  · exact resolveDeferredPositionValue_preserves_positionValue position target context result output hknown hresult

set_option maxRecDepth 100000 in
theorem positionValue_of_mem_runResolved
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α) (target : Position) (output : HashOutput)
    (hknown : context.positionValue target = some output)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    result.context.positionValue target = some output := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hknown
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hknown hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hknown hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            hknown hresult
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hknown (by simpa [hrevealed] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate candidate }
                  remaining hknown (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hknown hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            hknown hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hresolvedEq : resolveDeferredChainStart table index context = some resolved := by
                    simpa [index] using hresolved.symm
                  exact ih resolved.output (materializeResolvedChainStart context index resolved) fuel
                    (by rwa [materializeResolvedChainStart_positionValue_eq table index context resolved hresolvedEq])
                    (by simpa [index, OtsSecretIndex.coordinate, materializeResolvedChainStart] using hrest)
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hpreserved := resolveDeferredReveal_preserves_native_value
                    table position context resolved target output hknown hresolved
                  have hstate := resolveDeferredReveal_preserves_state_values table position context resolved hresolved
                  have hvalue := resolveDeferredReveal_resolves table position context resolved hresolved
                  exact ih resolved.output (materializeResolvedPosition context position resolved) fuel
                    (by
                      rw [materializeResolvedPosition_positionValue_eq context position resolved hstate hvalue]
                      exact hpreserved)
                    (by simpa [materializeResolvedPosition] using hrest)

def StoredNativeLayerRoot (context : DeferredContext) (target : Position) (root : Digest) : Prop :=
  ∃ output, context.positionValue target = some output ∧ truncateHash output = root

theorem storedNativeLayerRoot_of_mem_runResolved
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α) (target : Position) (root : Digest)
    (hroot : StoredNativeLayerRoot context target root)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    StoredNativeLayerRoot result.context target root := by
  obtain ⟨output, hknown, hroot⟩ := hroot
  exact ⟨output, positionValue_of_mem_runResolved computation context fuel table result target output hknown hresult, hroot⟩

theorem revealPosition_value_of_stored_native
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (position : Position) (cache : SplitHashCache) (root : Digest)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hroot : StoredNativeLayerRoot context position root)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((revealCoordinate (.position position)).run cache))) :
    result.value.1 = root := by
  rw [runResolvedFromTable_revealCoordinate, mem_support_bind_iff] at hresult
  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
  cases resolvedOption with
  | none => simp at hrest
  | some resolved =>
      simp only [mem_support_pure_iff, Option.some.injEq] at hrest
      subst result
      obtain ⟨output, hknown, htruncate⟩ := hroot
      have hpreserved := resolveDeferredReveal_preserves_native_value table position context resolved position output hknown hresolved
      have hvalue := resolveDeferredReveal_resolves table position context resolved hresolved
      have heq : resolved.output = output := Option.some.inj (hvalue.symm.trans hpreserved)
      exact heq ▸ htruncate

set_option maxRecDepth 100000 in
theorem maskedTreeRoot_eq_of_stored_native
    (lay : Layer) (tree : TreeIndex)
    (state : DeferredContext) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Digest × SplitHashCache)) (root : Digest)
    (hroot : StoredNativeLayerRoot state (layerRootPosition lay tree) root)
    (hresult : some result ∈ support
      (runResolvedFromTable state fuel table ((maskedTreeRoot lay tree).run cache))) :
    result.value.1 = root ∧ StoredNativeLayerRoot result.context (layerRootPosition lay tree) root := by
  have horiginal := hresult
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  unfold maskedTreeRoot at hresult
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega,
    maskedTreeNode, StateT.run_bind, runResolvedFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨administrative, hadministrative, hreveal⟩ := hresult
  cases administrative with
  | none => simp at hreveal
  | some administrative =>
      have hmiddleRoot := storedNativeLayerRoot_of_mem_runResolved
        ((ensureTreeNode lay tree (layerHeight lay - 1 + 1) 0).run cache)
        state fuel table administrative (layerRootPosition lay tree) root hroot
        hadministrative
      simp only at hreveal
      rw [dif_pos hlevel] at hreveal
      obtain ⟨output, hstored, htruncate⟩ := hmiddleRoot
      change some result ∈ support
        (runResolvedFromTable administrative.context administrative.remaining administrative.table
          ((revealCoordinate (.position (layerRootPosition lay tree))).run
            administrative.value.2)) at hreveal
      exact ⟨revealPosition_value_of_stored_native administrative.context administrative.remaining
        administrative.table (layerRootPosition lay tree) administrative.value.2 root result
        ⟨output, hstored, htruncate⟩ hreveal,
        storedNativeLayerRoot_of_mem_runResolved
          ((maskedTreeRoot lay tree).run cache) state fuel table result
          (layerRootPosition lay tree) root hroot horiginal⟩

theorem maskedLayerMessage_eq_of_stored_native_of_eq
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay below : Layer)
    (hcomputation : maskedLayerMessage parameter ftsSecret index lay =
      maskedTreeRoot below (treeIndexAt index below))
    (hposition : layerMessagePosition index lay =
      layerRootPosition below (treeIndexAt index below))
    (state : DeferredContext) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Digest × SplitHashCache)) (root : Digest)
    (hroot : StoredNativeLayerRoot state (layerMessagePosition index lay) root)
    (hresult : some result ∈ support
      (runResolvedFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run cache))) :
    result.value.1 = root ∧
      StoredNativeLayerRoot result.context (layerMessagePosition index lay) root := by
  rw [hcomputation] at hresult
  rw [hposition] at hroot ⊢
  exact maskedTreeRoot_eq_of_stored_native below (treeIndexAt index below)
    state cache fuel table result root hroot hresult

theorem maskedLayerMessage_value_eq_of_stored_native
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target) (root : Digest)
    (index : Index) (lay : Layer)
    (state : DeferredContext) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hstored : StoredNativeLayerRoot state target root)
    (htarget : layerMessagePosition index lay = target)
    (hresult : some result ∈ support
      (runResolvedFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run cache))) :
    result.value.1 = root := by
  obtain ⟨below, hcomputation, hposition⟩ :=
    layerMessage_root_witness_of_isLayerRoot parameter ftsSecret target hroot index lay htarget
  have hstoredMessage : StoredNativeLayerRoot state (layerMessagePosition index lay) root := by
    rw [htarget]
    exact hstored
  exact (maskedLayerMessage_eq_of_stored_native_of_eq parameter ftsSecret index lay below
    hcomputation hposition state cache fuel table result root hstoredMessage hresult).1

end SphincsSecurity.Concrete.OtsProbeSimulation
