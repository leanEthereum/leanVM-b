import SphincsSecurity.Proof.OtsProbeRootSourceTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem CanonicalQueryTraceRel.known_source_of_matching_history_roots
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel accountingKey.parameter table left right)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hrun : right ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hfinal : right.1.2.2 = false)
    (i j : Fin left.2.length) (hij : i.val < j.val)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hinput : (left.2.get i).input = .inl (.inr input))
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : (left.2.get j).context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output) :
    ∃ initialOutput, (left.2.get i).context.positionValue (layerRootPosition lay tree) = some initialOutput := by
  let actualI : Fin right.2.length := ⟨i.val, i.isLt.trans_le hrelation.length_le⟩
  let actualJ : Fin right.2.length := ⟨j.val, j.isLt.trans_le hrelation.length_le⟩
  have hsource := hrelation.selection_at i
  have htarget := hrelation.selection_at j
  obtain ⟨_htargetInput, _htable, hinvariant, _hvisible, _hpublished, hcomputed⟩ := htarget
  have hroot := hcomputed.root_settled_value hinvariant accountingKey.ftsSecret lay tree output hvalue
  have hsettled : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
      (right.2.get actualJ).state.1.cache (layerRootPosition lay tree) := by
    rw [hsecrets]
    exact hroot.1
  have hrootValue : honestValue (fromCache (right.2.get actualJ).state.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (layerRootPosition lay tree) =
        truncateHash output := by
    rw [hsecrets]
    exact hroot.2
  have hfalse := prehitQueryTrace_entry_false_of_final_false accountingKey secretKey computation state right hrun hfinal
    (right.2.get actualJ) (List.get_mem _ _)
  have hpairs := prehitQueryTrace_pairwise_encodingSourceSettled accountingKey secretKey computation state right hrun
  have hpair := hpairs.rel_get_of_lt (show actualI < actualJ from hij)
  have hbefore := hpair input candidate (layerRootPosition lay tree) (hsource.1.symm.trans hinput)
    hcandidate hposition hfalse hsettled (hmatch.trans hrootValue.symm)
  obtain ⟨initialOutput, houtput, _⟩ := hsource.2.2.1.positionValue_of_settled hsecrets
    (by trivial : IsOtsPosition (layerRootPosition lay tree)) hbefore
  exact ⟨initialOutput, houtput⟩

set_option maxRecDepth 100000 in
theorem CanonicalQueryTraceRel.known_source_of_matching_final_root
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel accountingKey.parameter table left right)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hrun : right ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hfinal : right.1.2.2 = false)
    (terminal : ResolvedRunResult (α × SplitHashCache)) (hterminal : left.1 = some terminal)
    (i : Fin left.2.length)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hinput : (left.2.get i).input = .inl (.inr input))
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : terminal.context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output) :
    ∃ initialOutput, (left.2.get i).context.positionValue (layerRootPosition lay tree) = some initialOutput := by
  have hterminalRelation := hrelation.1
  rw [hterminal] at hterminalRelation
  obtain ⟨_htable, _hvalue, hinvariant, _hvisible, _hpublished, hcomputed⟩ := hterminalRelation
  have hroot := hcomputed.root_settled_value hinvariant accountingKey.ftsSecret lay tree output hvalue
  have hsettled : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
      right.1.2.1.cache (layerRootPosition lay tree) := by
    rw [hsecrets]
    exact hroot.1
  have hrootValue : honestValue (fromCache right.1.2.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (layerRootPosition lay tree) =
        truncateHash output := by
    rw [hsecrets]
    exact hroot.2
  have hbefore := prehitQueryTrace_encodingSourceSettled_at_final accountingKey secretKey computation state right hrun _ (List.get_mem _ _)
    input candidate (layerRootPosition lay tree) ((hrelation.selection_at i).1.symm.trans hinput)
    hcandidate hposition hfinal hsettled (hmatch.trans hrootValue.symm)
  obtain ⟨initialOutput, houtput, _⟩ := (hrelation.selection_at i).2.2.1.positionValue_of_settled hsecrets
    (by trivial : IsOtsPosition (layerRootPosition lay tree)) hbefore
  exact ⟨initialOutput, houtput⟩

def UnknownSourceStoredRootMatch (parameter : PublicParameter) (history : List CanonicalQuerySelection) : Prop :=
  ∃ (i j : Fin history.length), i.val < j.val ∧
    ∃ (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput),
      (history.get i).input = .inl (.inr input) ∧
      EncodingLayerRootCandidateAt parameter input candidate ∧
      candidate.coordinate = .position (layerRootPosition lay tree) ∧
      (history.get j).context.positionValue (layerRootPosition lay tree) = some output ∧
      candidate.candidate = truncateHash output ∧
      (history.get i).context.positionValue (layerRootPosition lay tree) = none

def UnknownSourceFinalRootMatch (parameter : PublicParameter)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  ∃ terminal, result.1 = some terminal ∧ ∃ (i : Fin result.2.length),
    ∃ (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput),
      (result.2.get i).input = .inl (.inr input) ∧
      EncodingLayerRootCandidateAt parameter input candidate ∧
      candidate.coordinate = .position (layerRootPosition lay tree) ∧
      terminal.context.positionValue (layerRootPosition lay tree) = some output ∧
      candidate.candidate = truncateHash output ∧
      (result.2.get i).context.positionValue (layerRootPosition lay tree) = none

theorem CanonicalQueryTraceRel.hit_of_unknown_source_root_match
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel accountingKey.parameter table left right)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hrun : right ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hmatch : UnknownSourceStoredRootMatch accountingKey.parameter left.2 ∨ UnknownSourceFinalRootMatch accountingKey.parameter left) :
    right.1.2.2 = true := by
  by_cases hhit : right.1.2.2 = true
  · exact hhit
  have hfalse := Bool.eq_false_iff.mpr hhit
  rcases hmatch with hhistory | hterminal
  · obtain ⟨i, j, hij, input, candidate, lay, tree, output, hinput, hcandidate, hposition, hvalue, hmatch, hnone⟩ := hhistory
    obtain ⟨initialOutput, hknown⟩ := hrelation.known_source_of_matching_history_roots secretKey hsecrets
      computation state hrun hfalse i j hij input candidate lay tree output hinput hcandidate hposition hvalue hmatch
    rw [hnone] at hknown
    contradiction
  · obtain ⟨terminal, hterminal, i, input, candidate, lay, tree, output, hinput, hcandidate, hposition, hvalue, hmatch, hnone⟩ := hterminal
    obtain ⟨initialOutput, hknown⟩ := hrelation.known_source_of_matching_final_root secretKey hsecrets
      computation state hrun hfalse terminal hterminal i input candidate lay tree output hinput hcandidate hposition hvalue hmatch
    rw [hnone] at hknown
    contradiction

theorem probEvent_unknownSourceRootMatch_le_prehit_of_trace_coupling
    (accountingKey secretKey : SecretKey) (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (hcoupling : RelTriple leftRun (runPrehitQueryTrace accountingKey secretKey computation state)
      (CanonicalQueryTraceRel accountingKey.parameter table)) :
    Pr[fun result => UnknownSourceStoredRootMatch accountingKey.parameter result.2 ∨
      UnknownSourceFinalRootMatch accountingKey.parameter result | leftRun] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state] := by
  rw [← runPrehitQueryTrace_projection, probEvent_map]
  apply probEvent_le_of_relTriple (FtsProbeSimulation.relTriple_and_right_support hcoupling)
  intro left right hrelation hmatch
  exact hrelation.1.hit_of_unknown_source_root_match secretKey hsecrets computation state hrelation.2 hmatch

theorem probEvent_canonicalUnknownSourceRootMatch_le_prehit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    Pr[fun result => UnknownSourceStoredRootMatch parameter result.2 ∨ UnknownSourceFinalRootMatch parameter result |
      runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey) computation).run state] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  exact probEvent_unknownSourceRootMatch_le_prehit_of_trace_coupling secretKey secretKey table _ computation state rfl
    (relTriple_canonicalQueryTrace_prehitQueryTrace parameter root table ftsSecret secretKey computation context fuel cache state
      hinvariant hvisible hpublished hcomputed)

end SphincsSecurity.Concrete.OtsProbeSimulation
