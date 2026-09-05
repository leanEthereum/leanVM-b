import SphincsSecurity.Proof.OtsProbeSettledNativeValue
import SphincsSecurity.Proof.OtsProbeLiveKnownRootCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.settled_of_prehitFree_matching_query
    {secretKey : SecretKey} {initialCache finalCache : QueryCache HashSpec}
    {input : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hafter : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache target)
    (hmatch : candidate.candidate = honestValue (fromCache finalCache)
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret target)
    (next : HashOutput → OracleComp OracleWorld α) (value : α)
    (hrun : ((value, finalCache), false) ∈ support
      (TightEncoding.runEncodingPrehitMonitor secretKey (OracleWorld.query (.inr input) >>= next) initialCache false)) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret initialCache target := by
  obtain ⟨position, index, hat, htree, hleaf, _hnotBottom, rfl⟩ := hcandidate
  have heq : layerMessagePosition index position.lay = target := Coordinate.position.inj hposition
  subst target
  obtain ⟨otherIndex, hotherTree, hotherLeaf, hsettled⟩ :=
    TightEncoding.encodingMessageSettledAt_of_prehitFree_matching_query secretKey position index input
      htree hleaf hat next initialCache value finalCache hafter hmatch hrun
  have hsame := layerMessagePosition_eq_of_position_eq otherIndex index position.lay
    (hotherTree.trans htree.symm) (hotherLeaf.trans hleaf.symm)
  rwa [hsame] at hsettled

theorem EncodingLayerRootCandidateAt.settled_of_prehitFree_viewed_matching_query
    {accountingKey : SecretKey} (secretKey : SecretKey)
    {initialState finalState : ViewedFullTraceState}
    {input : HashInput} {candidate : Probe} {target : Position}
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hafter : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret finalState.cache target)
    (hmatch : candidate.candidate = honestValue (fromCache finalState.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (initialState, false))) :
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret initialState.cache target := by
  obtain ⟨log, hmonitor, _⟩ := encodingPrehitViewedAdversaryImpl_support_monitor accountingKey secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next) (initialState, false) (value, (finalState, false)) hrun
  have hcomputation :
      ((simulateQ (forwardOracles + signingOracle scheme secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run) =
      ((liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) >>= fun answer =>
        (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run) := by
    have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inl (.inr input))).run) =
        (fun output => (output, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) := rfl
    rw [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, hquery]
    erw [bind_map_left]
    apply bind_congr
    intro answer
    change (fun result : α × QueryLog SigningSpec => (result.1, [] ++ result.2)) <$>
      (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run = _
    simp
  rw [hcomputation] at hmonitor
  exact hcandidate.settled_of_prehitFree_matching_query hposition hafter hmatch
    (fun answer => (simulateQ (forwardOracles + signingOracle scheme secretKey) (next answer)).run) (value, log) hmonitor

theorem knownNativeRoot_at_source_of_prehitFree_matching_query
    (secretKey : SecretKey) (table : OtsSecretIndex → HashOutput)
    (initialContext finalContext : DeferredContext) (initialOrdinaryCache finalOrdinaryCache : QueryCache HashSpec)
    (initialState finalState : ViewedFullTraceState)
    (hinitial : ResolvedContextInvariant secretKey.parameter table initialContext initialOrdinaryCache initialState.cache)
    (hfinal : ResolvedContextInvariant secretKey.parameter table finalContext finalOrdinaryCache finalState.cache)
    (hcomputed : DeferredComputationsClosed finalContext)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : finalContext.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (initialState, false))) :
    ∃ initialOutput, initialContext.positionValue (layerRootPosition lay tree) = some initialOutput ∧
      candidate.candidate = truncateHash initialOutput := by
  have hroot := hcomputed.root_settled_value hfinal secretKey.ftsSecret lay tree output hvalue
  have hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalState.cache (layerRootPosition lay tree) := by
    simpa only [hsecrets] using hroot.1
  have hrootValue : honestValue (fromCache finalState.cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (layerRootPosition lay tree) = truncateHash output := by
    simpa only [hsecrets] using hroot.2
  have hbefore := hcandidate.settled_of_prehitFree_viewed_matching_query secretKey hposition hsettled
    (hmatch.trans hrootValue.symm) next value hrun
  obtain ⟨initialOutput, houtput, hinitialValue⟩ := hinitial.positionValue_of_settled hsecrets
    (by trivial : IsOtsPosition (layerRootPosition lay tree)) hbefore
  obtain ⟨log, hmonitor, _⟩ := encodingPrehitViewedAdversaryImpl_support_monitor secretKey secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next) (initialState, false) (value, (finalState, false)) hrun
  have hcacheLe := TightEncoding.cache_le_of_mem_runEncodingPrehitMonitor _ _ _ _ _ hmonitor
  have hvalueEq := honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hcacheLe) hbefore
  exact ⟨initialOutput, houtput, hmatch.trans (hrootValue.symm.trans (hvalueEq.trans hinitialValue))⟩

theorem probEvent_nativeStoredRootMatch_le_prehit_of_no_initial_match
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex)
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context)
    (hnomatch : ∀ output, context.positionValue (layerRootPosition lay tree) = some output →
      candidate.candidate ≠ truncateHash output) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    Pr[LiveNativeStoredRootMatch lay tree candidate.candidate | runResolvedFromTable context fuel table
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run cache)] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (state, false)] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  have hcoupling := relTriple_nativeChronological_computed_prehit parameter root table ftsSecret secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next) context fuel cache (state, false)
    hinvariant hvisible hpublished hcomputed
  apply probEvent_le_of_relTriple hcoupling
  rintro result ⟨value, finalState, hit⟩ hrelation hmatch
  cases hit with
  | true => rfl
  | false =>
      cases result with
      | none => exact False.elim hmatch
      | some result =>
          obtain ⟨hcomplete, output, hvalue, hmatch⟩ := hmatch
          rcases hrelation.1 with hclean | hdoomed
          · obtain ⟨initialOutput, houtput, heq⟩ := knownNativeRoot_at_source_of_prehitFree_matching_query
              secretKey table context result.context (ordinaryQueryCache cache) (ordinaryQueryCache result.value.2)
              state finalState hinvariant hclean.2.2.1 (hrelation.2.1 result rfl) rfl input candidate lay tree output
              hcandidate hposition hvalue hmatch.symm next value hrelation.2.2
            exact False.elim (hnomatch initialOutput houtput heq)
          · rw [hdoomed.1] at hcomplete
            exact False.elim (hdoomed.2.2.2 hcomplete)

def LiveNativeHiddenRootMatch (lay : Layer) (tree : TreeIndex) (candidate : Digest)
    (result : Option (ResolvedRunResult α)) : Prop :=
  LiveNativeStoredRootMatch lay tree candidate result ∧
    match result with
    | none => False
    | some result => .position (layerRootPosition lay tree) ∉ result.context.state.revealed

theorem probEvent_nativeHiddenRootMatch_le_prehit_of_not_known_source
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex)
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context)
    (hnot : ¬KnownHiddenEncodingRootQuery parameter input context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    Pr[LiveNativeHiddenRootMatch lay tree candidate.candidate | runResolvedFromTable context fuel table
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run cache)] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (state, false)] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  have hbase := relTriple_nativeChronological_computed_prehit parameter root table ftsSecret secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next) context fuel cache (state, false)
    hinvariant hvisible hpublished hcomputed
  have hcoupling := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => ∀ result, left = some result → context.state.revealed ⊆ result.context.state.revealed) (by
      intro left hleft result heq
      subst left
      exact revealed_subset_of_mem_runResolvedFromTable _ context fuel table result hleft)
  apply probEvent_le_of_relTriple hcoupling
  rintro result ⟨value, finalState, hit⟩ hrelation hmatch
  cases hit with
  | true => rfl
  | false =>
      cases result with
      | none => exact False.elim hmatch.1
      | some result =>
          obtain ⟨⟨hcomplete, output, hvalue, hmatch⟩, hhidden⟩ := hmatch
          rcases hrelation.1.1 with hclean | hdoomed
          · obtain ⟨initialOutput, houtput, _heq⟩ := knownNativeRoot_at_source_of_prehitFree_matching_query
              secretKey table context result.context (ordinaryQueryCache cache) (ordinaryQueryCache result.value.2)
              state finalState hinvariant hclean.2.2.1 (hrelation.1.2.1 result rfl) rfl input candidate lay tree output
              hcandidate hposition hvalue hmatch.symm next value hrelation.1.2.2
            exact False.elim (hnot ⟨candidate, layerRootPosition lay tree, initialOutput, hcandidate, hposition,
              houtput, fun hrevealed => hhidden (hrelation.2 result rfl hrevealed)⟩)
          · rw [hdoomed.1] at hcomplete
            exact False.elim (hdoomed.2.2.2 hcomplete)

end SphincsSecurity.Concrete.OtsProbeSimulation
