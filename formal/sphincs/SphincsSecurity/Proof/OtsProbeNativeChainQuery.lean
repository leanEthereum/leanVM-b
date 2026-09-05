import SphincsSecurity.Proof.OtsProbeSigningChainFailureCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem relTriple_chainFailure_of_preserves
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : StateT (QueryCache HashSpec) ProbComp α)
    (hbase : ReachableResolvedCouples parameter table left right)
    (hpreserves : ResolvedPreservesChainMaterialization left)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hchain : MaterializedChainsPublished context) :
    RelTriple (runResolvedFromTable context fuel table (left.run cache)) (right.run concreteCache)
      (SigningChainFailureRunRel parameter table) := by
  have hsupported := FtsProbeSimulation.relTriple_and_left_support
    (hbase context fuel cache concreteCache hinvariant hvisible hpublished)
    (fun result => result ∈ support (runResolvedFromTable context fuel table (left.run cache))) (fun _ h => h)
  apply relTriple_post_mono hsupported
  intro leftResult rightResult hrel
  refine ⟨hrel.1, ?_⟩
  intro result heq _
  subst leftResult
  exact Or.inl (hpreserves context cache fuel table result hchain hrel.2)

theorem relTriple_nativeQuery_chainFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hchain : MaterializedChainsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))
      ((unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ input).run concreteCache)
      (SigningChainFailureRunRel parameter table) := by
  cases input with
  | inl input =>
      apply relTriple_chainFailure_of_preserves parameter table _ _
        (reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter root table ftsSecret _) _
        context fuel cache concreteCache hinvariant hvisible hpublished hchain
      cases input with
      | inl n =>
          exact .of_preservesCoordinate fun coordinate => resolvedPreservesCoordinate_splitUniformImpl coordinate n
      | inr hashInput => exact resolvedPreservesChainMaterialization_probingHashQuery parameter hashInput
  | inr message =>
      exact relTriple_sign_chainFailure_concrete parameter root table ftsSecret message context fuel cache concreteCache
        hinvariant hvisible hpublished hchain

def LiveChainPublicationFailure (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none => False
  | some result => DeferredCompletable table result.context ∧ ¬MaterializedChainsPublished result.context

theorem SigningChainFailureRunRel.encoding_failure_of_chain_failure
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache))} {right : α × QueryCache HashSpec}
    (hrel : SigningChainFailureRunRel parameter table left right) (hfailure : LiveChainPublicationFailure table left) :
    CachedOtsEncodingFailure right.2 := by
  cases left with
  | none => exact False.elim hfailure
  | some result => exact (hrel.2 result rfl hfailure.1).resolve_left hfailure.2

theorem probEvent_nativeQuery_chainFailure_le_cachedFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hchain : MaterializedChainsPublished context) :
    Pr[LiveChainPublicationFailure table | runResolvedFromTable context fuel table
      ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)] ≤
    Pr[fun result => CachedOtsEncodingFailure result.2 | (unloggedMappedAdversaryImpl
      ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ input).run concreteCache] := by
  apply probEvent_le_of_relTriple (relTriple_nativeQuery_chainFailure parameter root table ftsSecret input context fuel
    cache concreteCache hinvariant hvisible hpublished hchain)
  intro left right hrel hfailure
  exact hrel.encoding_failure_of_chain_failure hfailure

end SphincsSecurity.Concrete.OtsProbeSimulation
