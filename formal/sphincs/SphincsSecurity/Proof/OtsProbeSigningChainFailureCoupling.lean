import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSigningChainPublication
import SphincsSecurity.Proof.OtsProbeSigningFailureCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def SigningChainFailureRunRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache))) (right : α × QueryCache HashSpec) : Prop :=
  ReachableResolvedRunRel parameter table left right ∧
    ∀ result, left = some result → DeferredCompletable table result.context →
      MaterializedChainsPublished result.context ∨ CachedOtsEncodingFailure right.2

theorem relTriple_signAfterDigest_chainFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedChainsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache))
      ((concreteSignAfterDigestFromTable parameter root table ftsSecret randomness index leaves).run concreteCache)
      (SigningChainFailureRunRel parameter table) := by
  have hbase := reachableResolvedCouples_maskedPublishedChronologicalSignAfterDigest_concrete
    parameter root table ftsSecret randomness index leaves context fuel cache concreteCache hinvariant hvisible hpublished
  have hleft := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache)))
    (fun _ h => h)
  apply relTriple_post_mono (FtsProbeSimulation.relTriple_and_right_support hleft)
  intro left right hrel
  refine ⟨hrel.1.1, ?_⟩
  intro result heq hcomplete
  subst left
  by_cases hsuccess : result.value.1 ≠ none
  · exact Or.inl (materializedChainsPublished_of_mem_successful_signAfterDigest parameter ftsSecret randomness index leaves
      context fuel table cache result hstarts hrel.1.2 hsuccess)
  · have hfailed : result.value.1 = none := not_not.mp hsuccess
    have hvalue : result.value.1 = right.1 := by
      rcases hrel.1.1 with hclean | hdoomed
      · exact hclean.2.1
      · exact False.elim (hdoomed.2.2.2 hcomplete)
    right
    apply cachedOtsEncodingFailure_of_mem_signAfterDigest_none parameter root table ftsSecret randomness index leaves
      concreteCache right.2
    have hright : right = (none, right.2) := Prod.ext (hvalue.symm.trans hfailed) rfl
    rw [← hright]
    exact hrel.2

theorem relTriple_chainFailure_of_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : ProbComp (α × QueryCache HashSpec))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple (runResolvedFromTable context fuel table (computation.run cache)) right
      (SigningChainFailureRunRel parameter table) := by
  have hbase := relTriple_runResolvedFromTable_of_doomed_reachable parameter table computation right context fuel cache hdoomed
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left ∈ support (runResolvedFromTable context fuel table (computation.run cache))) (fun _ h => h)
  apply relTriple_post_mono hsupported
  intro left right hrel
  refine ⟨hrel.1, ?_⟩
  intro result heq hcomplete
  subst left
  exact False.elim (not_deferredCompletable_of_mem_runResolvedFromTable (computation.run cache)
    context fuel table result hdoomed.1 hdoomed.2.1 hrel.2 hdoomed.2.2 hcomplete)

theorem relTriple_chainFailure_pure
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (value : α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedChainsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table ((pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α).run cache))
      (pure (value, concreteCache) : ProbComp _) (SigningChainFailureRunRel parameter table) := by
  simp only [StateT.run_pure, runResolvedFromTable]
  apply relTriple_pure_pure
  refine ⟨Or.inl ⟨rfl, rfl, hinvariant, hvisible, hpublished⟩, ?_⟩
  intro result heq _
  cases heq
  exact Or.inl hstarts

theorem relTriple_chainFailure_bind_publicPrefix
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : StateT (QueryCache HashSpec) ProbComp α)
    (leftNext : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (rightNext : α → StateT (QueryCache HashSpec) ProbComp β)
    (hprefix : ReachableResolvedCouples parameter table left right)
    (hnext : ∀ value context fuel cache concreteCache,
      ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache →
      VisibleResolvedComputationsCached parameter table context concreteCache → PublishedValues context.state →
      MaterializedChainsPublished context →
      RelTriple (runResolvedFromTable context fuel table ((leftNext value).run cache))
        ((rightNext value).run concreteCache) (SigningChainFailureRunRel parameter table))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hstarts : ∀ result, some result ∈ support (runResolvedFromTable context fuel table (left.run cache)) →
      MaterializedChainsPublished result.context) :
    RelTriple (runResolvedFromTable context fuel table ((left >>= leftNext).run cache))
      ((right >>= rightNext).run concreteCache) (SigningChainFailureRunRel parameter table) := by
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind]
  have hbase := hprefix context fuel cache concreteCache hinvariant hvisible hpublished
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support (runResolvedFromTable context fuel table (left.run cache))) (fun _ h => h)
  apply relTriple_bind hsupported
  intro leftResult rightResult hrel
  cases leftResult with
  | none =>
      have hbase := relTriple_true
        (pure (none : Option (ResolvedRunResult (β × SplitHashCache))) : ProbComp _)
        ((rightNext rightResult.1).run rightResult.2)
      have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
        (fun finalLeft => finalLeft = none) (by intro finalLeft h; simpa using h)
      apply relTriple_post_mono hsupported
      intro finalLeft finalRight hfinal
      rw [hfinal.2]
      exact ⟨True.intro, by intro result h; cases h⟩
  | some result =>
      rcases hrel.1 with hclean | hdoomed
      · rcases rightResult with ⟨rightValue, rightCache⟩
        have hvalue : result.value.1 = rightValue := hclean.2.1
        subst rightValue
        simpa only [hclean.1] using hnext result.value.1 result.context result.remaining result.value.2 rightCache
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 (hstarts result hrel.2)
      · simpa only [hdoomed.1] using relTriple_chainFailure_of_doomed parameter table
          (leftNext result.value.1) ((rightNext rightResult.1).run rightResult.2)
          result.context result.remaining result.value.2 hdoomed.2

theorem relTriple_sign_chainFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedChainsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache))
      ((resolvedImmediateSign parameter root table ftsSecret message).run concreteCache)
      (SigningChainFailureRunRel parameter table) := by
  let maskedSecretKey : SecretKey := ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  let concreteSecretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  unfold maskedPublishedChronologicalSign resolvedImmediateSign
  change RelTriple
    (runResolvedFromTable context fuel table ((do
      match ← simulateQ ordinaryRomImpl (signDigestLoop digestAttemptLimit maskedSecretKey message) with
      | none => pure none
      | some (randomness, index, leaves) =>
          maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache))
    ((do
      match ← simulateQ romImpl (signDigestLoop digestAttemptLimit concreteSecretKey message) with
      | none => pure none
      | some (randomness, index, leaves) =>
          resolvedImmediateSignAfterDigest parameter table ftsSecret randomness index leaves).run concreteCache)
    (SigningChainFailureRunRel parameter table)
  rw [← signDigestLoop_eq_of_parameter_root maskedSecretKey concreteSecretKey rfl rfl message digestAttemptLimit]
  apply relTriple_chainFailure_bind_publicPrefix parameter table _ _ _ _
    (reachableResolvedCouples_signDigestLoop table maskedSecretKey message digestAttemptLimit) _
    context fuel cache concreteCache hinvariant hvisible hpublished
  · intro result hresult coordinate hchain hknown
    have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl coordinate _
      context fuel table cache result hresult
    exact hpreserved.2.mpr (hstarts coordinate hchain (by rwa [hpreserved.1] at hknown))
  · intro selected current remaining currentCache actualCache hcurrent hvisible hpublished hstarts
    cases selected with
    | none =>
        exact relTriple_chainFailure_pure parameter table none current remaining currentCache actualCache
          hcurrent hvisible hpublished hstarts
    | some selected =>
        rcases selected with ⟨randomness, index, leaves⟩
        dsimp only
        rw [resolvedImmediateSignAfterDigest_eq_concrete parameter root table ftsSecret randomness index leaves]
        exact relTriple_signAfterDigest_chainFailure parameter root table ftsSecret randomness index leaves
          current remaining currentCache actualCache hcurrent hvisible hpublished hstarts

theorem relTriple_sign_chainFailure_concrete
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedChainsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache))
      ((simulateQ romImpl (scheme.sign
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
        message)).run concreteCache)
      (SigningChainFailureRunRel parameter table) := by
  rw [← resolvedImmediateSign_eq_concrete]
  exact relTriple_sign_chainFailure parameter root table ftsSecret message context fuel cache concreteCache
    hinvariant hvisible hpublished hstarts

end SphincsSecurity.Concrete.OtsProbeSimulation
