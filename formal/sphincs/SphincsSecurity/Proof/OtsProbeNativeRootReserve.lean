import SphincsSecurity.Proof.OtsProbeInitializedGameCharge
import SphincsSecurity.Proof.OtsProbeSelectedRootPrehit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem remainingOtsQueryReserve_eq_refined_of_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position) :
    remainingOtsQueryReserve secretKey cache input = otsOpeningRefinedQueryReserve secretKey cache input := by
  apply remainingOtsQueryReserve_eq_refined_of_not_ots
  rintro ⟨target, _hots, htarget⟩
  exact hat.not_atPosition target htarget

theorem EncodingLayerRootCandidateAt.remainingReserve_eq_refined
    {secretKey : SecretKey} (cache : QueryCache HashSpec) {input : HashInput} {candidate : Probe}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate) :
    remainingOtsQueryReserve secretKey cache input = otsOpeningRefinedQueryReserve secretKey cache input := by
  obtain ⟨position, index, hat, _⟩ := hcandidate
  exact remainingOtsQueryReserve_eq_refined_of_atEncodingPosition secretKey cache input position hat

theorem DeferredComputationsClosed.remainingReserve_of_encoding_candidate
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target) (hvalue : context.positionValue target = some output) :
    (4 / 3 : ENNReal) ≤ remainingOtsQueryReserve secretKey actualCache input := by
  rw [hcandidate.remainingReserve_eq_refined actualCache]
  exact hclosed.refinedReserve_of_encoding_candidate hinvariant hsecrets hcandidate hposition hvalue

theorem ensuredInitialContext_computed (targets : Finset Position) :
    DeferredComputationsClosed (ensuredInitialContext targets) :=
  deferredComputationsClosed_empty.of_positionValue_eq (fun _ => rfl)

theorem relTriple_nativeChronological_computed_prehit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple
      (runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache))
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state)
      (fun left right => ReachableResolvedRunRel parameter table left (right.1, right.2.1.cache) ∧
        (∀ result, left = some result → DeferredComputationsClosed result.context) ∧
        right ∈ support ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state)) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hnative := reachableResolvedCouples_simulateQ
    (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (unloggedMappedAdversaryImpl secretKey)
    (reachableResolvedCouples_chronologicalNative_concrete parameter root table ftsSecret) computation
    context fuel cache state.1.cache hinvariant hvisible hpublished
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hnative
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact hcomputed.of_mem_runResolved _ context fuel table result hleft)
  have hprojection := encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey computation state
  have hmonitor := relTriple_of_evalDist_map_eq_with_support_general
    ((simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run state.1.cache)
    ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state)
    id (fun result => (result.1, result.2.1.cache)) (by
      simpa only [id_map] using congrArg evalDist hprojection.symm)
  apply relTriple_post_mono (relTriple_trans_exists hsupported hmonitor)
  rintro left right ⟨actual, hrelation, heq, _hactual, hsupport⟩
  exact ⟨heq ▸ hrelation.1, hrelation.2, hsupport⟩

def LiveNativeStoredRootMatch (lay : Layer) (tree : TreeIndex) (candidate : Digest) :
    Option (ResolvedRunResult α) → Prop
  | none => False
  | some result => DeferredCompletable result.table result.context ∧
      ∃ output, result.context.positionValue (layerRootPosition lay tree) = some output ∧ truncateHash output = candidate

theorem probEvent_nativeStoredRootMatch_le_prehit_of_insufficientRemainingReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex)
    (hcandidate : EncodingLayerRootCandidateAt parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    remainingOtsQueryReserve secretKey state.cache input < (4 / 3 : ENNReal) →
      Pr[LiveNativeStoredRootMatch lay tree candidate.candidate | runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run cache)] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (state, false)] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  intro hreserve
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
          · have hroot := (hrelation.2.1 result rfl).root_settled_value hclean.2.2.1 ftsSecret lay tree output hvalue
            have hallowance := hcandidate.refinedReserve_of_prehitFree_viewed_matching_query secretKey
              (accountingKey := secretKey) hposition hroot.1 (hmatch.symm.trans hroot.2.symm) next value hrelation.2.2
            rw [← hcandidate.remainingReserve_eq_refined (secretKey := secretKey) state.cache] at hallowance
            exact False.elim ((not_le_of_gt hreserve) hallowance)
          · exact False.elim (hdoomed.2.2.2 (hdoomed.1 ▸ hcomplete))

end SphincsSecurity.Concrete.OtsProbeSimulation
