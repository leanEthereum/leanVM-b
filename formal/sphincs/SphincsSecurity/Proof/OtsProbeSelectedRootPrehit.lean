import SphincsSecurity.Proof.OtsProbeQueryCutPrehit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem relTriple_canonicalQuerySelection_prehitCut
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (canonicalQuerySelection parameter root ftsSecret computation ordinal context fuel table cache)
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        (outerQueryCutAt computation ordinal)).run state)
      (fun selection result =>
        CanonicalQuerySelectionRel parameter table selection (actualSelectionOfPrehitCut result) ∧
        result ∈ support ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
          (outerQueryCutAt computation ordinal)).run state)) := by
  classical
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hcanonical := relTriple_canonicalQuerySelection_actualQuerySelection parameter root table ftsSecret
    computation ordinal context fuel cache state.1.cache hinvariant hvisible hpublished hcomputed
  have hmonitor := relTriple_of_evalDist_map_eq_with_support_general
    (actualQuerySelection secretKey computation ordinal state.1.cache)
    ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
      (outerQueryCutAt computation ordinal)).run state)
    id actualSelectionOfPrehitCut (by
      rw [id_map, actualSelectionOfPrehitCut_projection])
  apply relTriple_post_mono (relTriple_trans_exists hcanonical hmonitor)
  rintro selection result ⟨actual, hrelation, hproject, _hactual, hsupport⟩
  exact ⟨hproject ▸ hrelation, hsupport⟩

set_option maxRecDepth 100000 in
theorem CanonicalQuerySelectionRel.cut_root_settled_value
    {accountingKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {selection : CanonicalQuerySelection} {cut : OuterQueryCut α} {state : ViewedFullTraceState × Bool}
    (hrelation : CanonicalQuerySelectionRel accountingKey.parameter table (some selection)
      (actualSelectionOfPrehitCut (cut, state)))
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : selection.context.positionValue (layerRootPosition lay tree) = some output) :
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret state.1.cache
        (layerRootPosition lay tree) ∧
      honestValue (fromCache state.1.cache) accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
        (layerRootPosition lay tree) = truncateHash output := by
  cases cut with
  | done value => exact False.elim hrelation
  | query input next =>
      obtain ⟨_hinput, _htable, hinvariant, _hvisible, _hpublished, hcomputed⟩ := hrelation
      rw [hsecrets]
      exact hcomputed.root_settled_value hinvariant accountingKey.ftsSecret lay tree output hvalue

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.ne_stored_root_of_prehitFree_queryCut
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {initialState finalState : ViewedFullTraceState} {selection : CanonicalQuerySelection}
    {previous : HashInput} {candidate : Probe} {lay : Layer} {tree : TreeIndex} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter previous candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hcached : initialState.cache previous ≠ none)
    (hbefore : ¬Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
      initialState.cache (layerRootPosition lay tree))
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (hvalue : selection.context.positionValue (layerRootPosition lay tree) = some output)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) (cut : OuterQueryCut α)
    (hrelation : CanonicalQuerySelectionRel accountingKey.parameter table (some selection)
      (actualSelectionOfPrehitCut (cut, (finalState, false))))
    (hrun : (cut, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        (outerQueryCutAt computation ordinal)).run (initialState, false))) :
    candidate.candidate ≠ truncateHash output := by
  have hroot := hrelation.cut_root_settled_value hsecrets lay tree output hvalue
  have hne := hcandidate.ne_honestValue_of_prehitFree_viewed_continuation secretKey
    hposition hcached hbefore hroot.1 (outerQueryCutAt computation ordinal) cut hrun
  simpa only [hroot.2] using hne

set_option maxRecDepth 100000 in
theorem EncodingLayerRootCandidateAt.refinedReserve_of_prehitFree_matching_queryCut
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {initialState finalState : ViewedFullTraceState} {selection : CanonicalQuerySelection}
    {input : HashInput} {candidate : Probe} {lay : Layer} {tree : TreeIndex} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (hvalue : selection.context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) (cut : OuterQueryCut α)
    (hrelation : CanonicalQuerySelectionRel accountingKey.parameter table (some selection)
      (actualSelectionOfPrehitCut (cut, (finalState, false))))
    (hrun : (cut, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= fun answer =>
          outerQueryCutAt (next answer) ordinal)).run (initialState, false))) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey initialState.cache input := by
  have hroot := hrelation.cut_root_settled_value hsecrets lay tree output hvalue
  exact hcandidate.refinedReserve_of_prehitFree_viewed_matching_query secretKey hposition hroot.1
    (hmatch.trans hroot.2.symm) (fun answer => outerQueryCutAt (next answer) ordinal) cut hrun


def SelectedLayerRootMatch (lay : Layer) (tree : TreeIndex) (candidate : Digest) :
    Option CanonicalQuerySelection → Prop
  | none => False
  | some selection => ∃ output,
      selection.context.positionValue (layerRootPosition lay tree) = some output ∧ truncateHash output = candidate

set_option maxRecDepth 100000 in
theorem probEvent_selectedRootMatch_le_prehit_of_insufficientReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex)
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    otsOpeningRefinedQueryReserve secretKey state.cache input < (4 / 3 : ℝ≥0∞) →
      Pr[SelectedLayerRootMatch lay tree candidate.candidate |
        canonicalQuerySelection parameter root ftsSecret
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)
          (ordinal + 1) context fuel table cache] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
          (outerQueryCutAt
            ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)
            (ordinal + 1))).run (state, false)] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  intro hreserve
  have hcoupling := relTriple_canonicalQuerySelection_prehitCut parameter root table ftsSecret secretKey
    ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)
    (ordinal + 1) context fuel cache (state, false) hinvariant hvisible hpublished hcomputed
  apply probEvent_le_of_relTriple hcoupling
  rintro selection ⟨cut, finalState, hit⟩ hrelation hmatch
  cases hit with
  | true => rfl
  | false =>
      cases selection with
      | none => exact False.elim hmatch
      | some selection =>
          obtain ⟨output, hvalue, hmatch⟩ := hmatch
          have hallowance := hcandidate.refinedReserve_of_prehitFree_matching_queryCut secretKey
            (accountingKey := secretKey) hposition rfl hvalue hmatch.symm next ordinal cut
            hrelation.1 hrelation.2
          exact False.elim ((not_le_of_gt hreserve) hallowance)

end SphincsSecurity.Concrete.OtsProbeSimulation
