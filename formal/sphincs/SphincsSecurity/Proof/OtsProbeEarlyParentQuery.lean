import SphincsSecurity.Proof.OtsProbeFullQueryTraceCoupling
import SphincsSecurity.Proof.OtsProbeNativeTraceCompletion
import SphincsSecurity.Proof.OtsProbeParentSettlement
import SphincsSecurity.Proof.SigningParentSettlement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem FullCanonicalQueryTraceRel.exists_selection
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (h : FullCanonicalQueryTraceRel parameter table left right) (hsome : left.1 ≠ none)
    {snapshot : PrehitQuerySnapshot} (hmem : snapshot ∈ right.2) :
    ∃ selection ∈ left.2, CanonicalQuerySelectionRel parameter table (some selection) (some snapshot.actual) := by
  rcases left with ⟨leftResult, leftHistory⟩
  rcases right with ⟨rightResult, rightHistory⟩
  change snapshot ∈ rightHistory at hmem
  change ∃ selection ∈ leftHistory, CanonicalQuerySelectionRel parameter table (some selection) (some snapshot.actual)
  have hlist : List.Forall₂ (fun a b => CanonicalQuerySelectionRel parameter table (some a) (some b.actual))
      leftHistory rightHistory := h.2 hsome
  clear h hsome
  induction hlist with
  | nil => simp at hmem
  | @cons a b as bs hhead htail ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨a, List.mem_cons_self, hhead⟩
      · obtain ⟨selection, hselection, hrel⟩ := ih hmem
        exact ⟨selection, List.mem_cons_of_mem a hselection, hrel⟩

def EarlyOtsParentAtQuery (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  ∃ snapshot ∈ result.2, ∃ child parent,
    IsOtsPosition parent ∧ child.parentOf = some parent ∧
    ¬ Settled parameter otsSecret ftsSecret snapshot.state.1.cache child ∧
    Settled parameter otsSecret ftsSecret result.1.2.1.cache parent ∧
    snapshot.state.1.cache (cachedInput parameter otsSecret ftsSecret result.1.2.1.cache parent) ≠ none

theorem EarlyOtsParentAtQuery.of_signing_cut
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf) (ordinal : Nat)
    {actual : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    {snapshot : PrehitQuerySnapshot} (hsnapshot : snapshot ∈ actual.2)
    {loopCache middleCache : QueryCache HashSpec}
    (hloop : (some (randomness, index, leaves), loopCache) ∈ support
      ((simulateQ romImpl (signDigestLoop digestAttemptLimit secretKey message)).run snapshot.state.1.cache))
    {cut : HashQueryCut (Option Signature)}
    (hcut : (cut, middleCache) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (hashQueryCutAt (signAfterDigest secretKey randomness index leaves) ordinal)).run loopCache))
    {input : HashInput} {answer : HashOutput}
    (hots : ∀ position, AtPosition secretKey.parameter input position → IsOtsPosition position)
    (hparent : ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret middleCache input answer)
    (hle : middleCache.cacheQuery input answer ≤ actual.1.2.1.cache) :
    EarlyOtsParentAtQuery secretKey.parameter secretKey.otsSecret secretKey.ftsSecret actual := by
  obtain ⟨child, parent, hat, hparentOf, hunsettled, hsettled, hcached⟩ :=
    signAfterDigest_parentSettlement_input_cached_signingEntry secretKey message randomness index leaves ordinal
      hloop hcut (agreesWithFn_fromCache middleCache) hparent hle
  exact ⟨snapshot, hsnapshot, child, parent, (hots child hat).parent hparentOf,
    hparentOf, hunsettled, hsettled, hcached⟩

theorem not_earlyOtsParentAtQuery_of_full_native_trace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (nativeResult : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (actual : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hsupport : (some nativeResult, history) ∈ support
      (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hrelation : FullCanonicalQueryTraceRel parameter table (some nativeResult, history) actual) :
    ¬ EarlyOtsParentAtQuery parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret actual := by
  rintro ⟨snapshot, hsnapshot, child, parent, hots, hparent, hbefore, hafter, hcached⟩
  obtain ⟨selection, hselection, hselected⟩ := hrelation.exists_selection (by simp) hsnapshot
  have hfinal : ResolvedContextInvariant parameter table nativeResult.context
      (ordinaryQueryCache nativeResult.value.2) actual.1.2.1.cache := hrelation.1.1.2.2.1
  obtain ⟨completion, hcompletion⟩ := hfinal.2.2.2.1
  have hbeforeCompletion := (nativeTrace_completion_facts parameter root ftsSecret computation context fuel table cache
    nativeResult history completion hconsistent hstarts hsupport hcompletion).2 selection hselection
  apply no_shared_completion_of_early_parent_input hselected.2.2.1.1 hfinal.1 hselected.2.2.2.2.2
    ftsSecret hots (Position.mem_children_iff.mpr hparent) hbefore hafter hcached
  exact ⟨completion, hbeforeCompletion.2.2.1, hcompletion⟩

theorem relTriple_nativeQueryTrace_prehit_earlyParent
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)
      (runPrehitQueryTrace accountingKey secretKey computation state)
      (fun left right => EarlyOtsParentAtQuery parameter secretKey.otsSecret ftsSecret right → left.1 = none) := by
  dsimp only
  have hcoupling := relTriple_nativeQueryTrace_full_prehitQueryTrace parameter root table ftsSecret accountingKey
    computation context fuel cache state hinvariant hvisible hpublished hcomputed
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hcoupling
    (fun result => result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (by intro result hresult; exact hresult)
  apply relTriple_post_mono hsupported
  rintro ⟨native, history⟩ actual hrelation hearly
  cases native with
  | none => rfl
  | some result =>
      exact False.elim (not_earlyOtsParentAtQuery_of_full_native_trace parameter root ftsSecret computation context fuel table cache
        result history actual hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hrelation.2 hrelation.1 hearly)

theorem probEvent_earlyOtsParentAtQuery_le_nativeTraceFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    Pr[EarlyOtsParentAtQuery parameter secretKey.otsSecret ftsSecret |
      runPrehitQueryTrace accountingKey secretKey computation state] ≤
      Pr[fun result => result.1 = none |
        runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] := by
  exact probEvent_le_of_relTriple (relTriple_symm
    (relTriple_nativeQueryTrace_prehit_earlyParent parameter root table ftsSecret accountingKey
      computation context fuel cache state hinvariant hvisible hpublished hcomputed))
    (fun _ _ hrelation hearly => hrelation hearly)

end SphincsSecurity.Concrete.OtsProbeSimulation
