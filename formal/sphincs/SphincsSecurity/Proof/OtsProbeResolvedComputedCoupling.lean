import SphincsSecurity.Proof.OtsProbeResolvedComputedExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.root_settled_value
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache cache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : context.positionValue (layerRootPosition lay tree) = some output) :
    Settled parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      ftsSecret cache (layerRootPosition lay tree) ∧
    honestValue (fromCache cache) parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      ftsSecret (layerRootPosition lay tree) = truncateHash output := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  have hcomputed := hclosed (layerRootPosition lay tree)
    (resolvableOtsPosition_layerRootPosition lay tree) ⟨output, hvalue⟩
  have hsettled := hcomputed.settled_value hinvariant.1 completion hcompletion ftsSecret
  rw [hcompletion.tableOtsSecret_eq] at hsettled
  simpa only [tableValue, hcompletion.eq_positionValue _ output hvalue] using hsettled

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.refinedReserve_of_encoding_candidate
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hvalue : context.positionValue target = some output) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  obtain ⟨position, hcoordinate, hroot⟩ := encodingLayerRootCandidateAt_isLayerRoot hcandidate
  have heq : position = target := Coordinate.position.inj (hcoordinate.symm.trans hposition)
  have hresolvable : ResolvableOtsPosition target := by
    rw [← heq]
    obtain ⟨lay, tree, rfl⟩ := hroot
    exact resolvableOtsPosition_layerRootPosition lay tree
  exact (hclosed target hresolvable ⟨output, hvalue⟩).refinedReserve_of_encoding_candidate hinvariant.1
    completion hcompletion (hsecrets.trans hcompletion.tableOtsSecret_eq.symm) hcandidate hposition

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.encoding_weightedCharge_le_refinedReserve
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hvalue : context.positionValue target = some output)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan secretKey.parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? secretKey.parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input :=
  (probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds
    secretKey.parameter input publicState plan cache context fuel).trans
    (hclosed.refinedReserve_of_encoding_candidate hinvariant hsecrets hcandidate hposition hvalue)

set_option maxRecDepth 100000 in
theorem relTriple_synchronizedCanonical_computed
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hcomputed : DeferredComputationsClosed context) :
    RelTriple
      (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache)
      ((simulateQ (unloggedMappedAdversaryImpl
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)) computation).run concreteCache)
      (fun left right => ReachableResolvedRunRel parameter table left right ∧
        ∀ result, left = some result → DeferredComputationsClosed result.context) := by
  apply FtsProbeSimulation.relTriple_and_left_support
    (relTriple_runSynchronizedResolved_reachable
      (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table ftsSecret)
      computation context fuel cache concreteCache hinvariant hvisible hpublished)
  intro left hleft result heq
  subst left
  exact hcomputed.of_mem_synchronizedCanonical parameter root table ftsSecret computation context fuel cache result
    hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hleft

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_synchronizedCanonical_computed_after_root
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (fuel : Nat) (rootResult : ResolvedRunResult (Digest × SplitHashCache))
    (hroot : some rootResult ∈ support
      (runResolvedFromTable { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table rootResult.context
      (ordinaryQueryCache rootResult.value.2) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table rootResult.context concreteCache)
    (hpublished : PublishedValues rootResult.context.state) :
    RelTriple
      (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation rootResult.context rootResult.remaining table rootResult.value.2)
      ((simulateQ (unloggedMappedAdversaryImpl
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)) computation).run concreteCache)
      (fun left right => ReachableResolvedRunRel parameter table left right ∧
        ∀ result, left = some result → DeferredComputationsClosed result.context) :=
  relTriple_synchronizedCanonical_computed parameter root table ftsSecret computation rootResult.context
    rootResult.remaining rootResult.value.2 concreteCache hinvariant hvisible hpublished
    (deferredComputationsClosed_empty.of_mem_runResolved _ _ fuel table rootResult hroot)

set_option maxRecDepth 100000 in
theorem encoding_weightedCharge_le_refinedReserve_of_computedSelection
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {left : PrivateOrdinalSelection} {right : PermissivePrivateOrdinalSelection}
    {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed left.context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table left.context ordinaryCache actualCache)
    (hselection : CanonicalSelectionPreserved (some left) (some right))
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input right.candidate)
    (hposition : right.candidate.coordinate = .position target)
    (hvalue : right.state.values (.position target) = some output)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan secretKey.parameter input publicState plan).run cache)
          (directDeferredContext right.state) fuel +
      (materializedCandidateCharge right.state (rootAwareCandidateForPlan? secretKey.parameter input plan) : ℝ≥0∞) *
        (4 / 3) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input := by
  have hleftValue : left.context.positionValue target = some output := by
    rw [← hselection.2.1.values] at hvalue
    exact hvalue
  exact (probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds
    secretKey.parameter input publicState plan cache (directDeferredContext right.state) fuel).trans
    (hclosed.refinedReserve_of_encoding_candidate hinvariant hsecrets hcandidate hposition hleftValue)

end SphincsSecurity.Concrete.OtsProbeSimulation
