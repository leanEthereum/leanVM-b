import SphincsSecurity.Proof.OtsProbeSigningStartValues
import SphincsSecurity.Proof.EncodingSigningFailure

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def SigningStartFailureRunRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache))) (right : α × QueryCache HashSpec) : Prop :=
  ReachableResolvedRunRel parameter table left right ∧
    ∀ result, left = some result → DeferredCompletable table result.context →
      MaterializedStartsPublished result.context ∨ CachedOtsEncodingFailure right.2

theorem cachedOtsEncodingFailure_of_mem_signAfterDigest_none
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (cache finalCache : QueryCache HashSpec)
    (hresult : (none, finalCache) ∈ support
      ((concreteSignAfterDigestFromTable parameter root table ftsSecret randomness index leaves).run cache)) :
    CachedOtsEncodingFailure finalCache := by
  rw [concreteSignAfterDigestFromTable_eq_signAfterDigest] at hresult
  obtain ⟨_hle, f, hagrees, hfailed, hcached⟩ := exists_answerFn_replay_of_mem_support _ _ _ _ hresult
  exact cachedOtsEncodingFailure_of_signAfterDigest_none f finalCache _ randomness index leaves hagrees hcached hfailed

theorem relTriple_signAfterDigest_startFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedStartsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache))
      ((concreteSignAfterDigestFromTable parameter root table ftsSecret randomness index leaves).run concreteCache)
      (SigningStartFailureRunRel parameter table) := by
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
  · exact Or.inl (materializedStartsPublished_of_mem_successful_signAfterDigest parameter ftsSecret randomness index leaves
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

theorem relTriple_startFailure_of_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : ProbComp (α × QueryCache HashSpec))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple (runResolvedFromTable context fuel table (computation.run cache)) right
      (SigningStartFailureRunRel parameter table) := by
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

theorem relTriple_startFailure_pure
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (value : α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedStartsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table ((pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α).run cache))
      (pure (value, concreteCache) : ProbComp _) (SigningStartFailureRunRel parameter table) := by
  simp only [StateT.run_pure, runResolvedFromTable]
  apply relTriple_pure_pure
  refine ⟨Or.inl ⟨rfl, rfl, hinvariant, hvisible, hpublished⟩, ?_⟩
  intro result heq _
  cases heq
  exact Or.inl hstarts

theorem relTriple_startFailure_bind_publicPrefix
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : StateT (QueryCache HashSpec) ProbComp α)
    (leftNext : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (rightNext : α → StateT (QueryCache HashSpec) ProbComp β)
    (hprefix : ReachableResolvedCouples parameter table left right)
    (hnext : ∀ value context fuel cache concreteCache,
      ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache →
      VisibleResolvedComputationsCached parameter table context concreteCache → PublishedValues context.state →
      MaterializedStartsPublished context →
      RelTriple (runResolvedFromTable context fuel table ((leftNext value).run cache))
        ((rightNext value).run concreteCache) (SigningStartFailureRunRel parameter table))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hstarts : ∀ result, some result ∈ support (runResolvedFromTable context fuel table (left.run cache)) →
      MaterializedStartsPublished result.context) :
    RelTriple (runResolvedFromTable context fuel table ((left >>= leftNext).run cache))
      ((right >>= rightNext).run concreteCache) (SigningStartFailureRunRel parameter table) := by
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
      · simpa only [hdoomed.1] using relTriple_startFailure_of_doomed parameter table
          (leftNext result.value.1) ((rightNext rightResult.1).run rightResult.2)
          result.context result.remaining result.value.2 hdoomed.2

theorem relTriple_sign_startFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedStartsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache))
      ((resolvedImmediateSign parameter root table ftsSecret message).run concreteCache)
      (SigningStartFailureRunRel parameter table) := by
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
    (SigningStartFailureRunRel parameter table)
  rw [← signDigestLoop_eq_of_parameter_root maskedSecretKey concreteSecretKey rfl rfl message digestAttemptLimit]
  apply relTriple_startFailure_bind_publicPrefix parameter table _ _ _ _
    (reachableResolvedCouples_signDigestLoop table maskedSecretKey message digestAttemptLimit) _
    context fuel cache concreteCache hinvariant hvisible hpublished
  · intro result hresult start hknown
    have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl start.coordinate _
      context fuel table cache result hresult
    exact hpreserved.2.mpr (hstarts start (by rwa [hpreserved.1] at hknown))
  · intro selected current remaining currentCache actualCache hcurrent hvisible hpublished hstarts
    cases selected with
    | none =>
        exact relTriple_startFailure_pure parameter table none current remaining currentCache actualCache
          hcurrent hvisible hpublished hstarts
    | some selected =>
        rcases selected with ⟨randomness, index, leaves⟩
        dsimp only
        rw [resolvedImmediateSignAfterDigest_eq_concrete parameter root table ftsSecret randomness index leaves]
        exact relTriple_signAfterDigest_startFailure parameter root table ftsSecret randomness index leaves
          current remaining currentCache actualCache hcurrent hvisible hpublished hstarts

theorem relTriple_sign_startFailure_concrete
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedStartsPublished context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache))
      ((simulateQ romImpl (scheme.sign
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
        message)).run concreteCache)
      (SigningStartFailureRunRel parameter table) := by
  rw [← resolvedImmediateSign_eq_concrete]
  exact relTriple_sign_startFailure parameter root table ftsSecret message context fuel cache concreteCache
    hinvariant hvisible hpublished hstarts

def LiveSigningStartErasure (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none => False
  | some result => DeferredCompletable table result.context ∧
      ∃ start : OtsSecretIndex, result.context.state.values start.coordinate ≠ none ∧
        (canonicalizeMaterializedValues table result.context).state.values start.coordinate = none

theorem SigningStartFailureRunRel.encoding_failure_of_erasure
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache))} {right : α × QueryCache HashSpec}
    (hrel : SigningStartFailureRunRel parameter table left right) (herasure : LiveSigningStartErasure table left) :
    CachedOtsEncodingFailure right.2 := by
  cases left with
  | none => exact False.elim herasure
  | some result =>
      obtain ⟨hcomplete, start, hknown, herased⟩ := herasure
      rcases hrel.2 result rfl hcomplete with hpublic | hfailed
      · have hrevealed := hpublic start hknown
        change (if start.coordinate ∈ result.context.state.revealed then some (table start) else none) = none at herased
        simp [hrevealed] at herased
      · exact hfailed

theorem probEvent_liveSigningStartErasure_le_cachedFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hstarts : MaterializedStartsPublished context) :
    Pr[LiveSigningStartErasure table | runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)] ≤
    Pr[fun result => CachedOtsEncodingFailure result.2 |
      (simulateQ romImpl (scheme.sign
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
        message)).run concreteCache] := by
  apply probEvent_le_of_relTriple (relTriple_sign_startFailure_concrete parameter root table ftsSecret message
    context fuel cache concreteCache hinvariant hvisible hpublished hstarts)
  intro left right hrel herasure
  exact hrel.encoding_failure_of_erasure herasure

theorem SigningStartFailureRunRel.materializedStartsPublished_of_no_exhaustion
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {result : ResolvedRunResult (α × SplitHashCache)} {right : α × QueryCache HashSpec}
    (hrel : SigningStartFailureRunRel parameter table (some result) right)
    (hcomplete : DeferredCompletable table result.context)
    (hnoExhaustion : ¬AnyEncodingInputsExhausted right.2) : MaterializedStartsPublished result.context := by
  rcases hrel.2 result rfl hcomplete with hpublic | hfailed
  · exact hpublic
  · exact False.elim (hnoExhaustion (anyEncodingInputsExhausted_of_cachedOtsEncodingFailure right.2 hfailed))

theorem SigningStartFailureRunRel.start_values_preserved_of_no_exhaustion
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {result : ResolvedRunResult (α × SplitHashCache)} {right : α × QueryCache HashSpec}
    (hrel : SigningStartFailureRunRel parameter table (some result) right)
    (hcomplete : DeferredCompletable table result.context)
    (hnoExhaustion : ¬AnyEncodingInputsExhausted right.2) (start : OtsSecretIndex) :
    (canonicalizeMaterializedValues table result.context).state.values start.coordinate =
      result.context.state.values start.coordinate := by
  have hpublic := hrel.materializedStartsPublished_of_no_exhaustion hcomplete hnoExhaustion
  rcases hrel.1 with hclean | hdoomed
  · exact canonicalize_start_values_eq_of_materializedStartsPublished table result.context hpublic
      hclean.2.2.2.2 hclean.2.2.1.2.2.1 start
  · exact False.elim (hdoomed.2.2.2 hcomplete)

theorem SigningStartFailureRunRel.completedStartTable_preserved_of_no_exhaustion
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {result : ResolvedRunResult (α × SplitHashCache)} {right : α × QueryCache HashSpec}
    (hrel : SigningStartFailureRunRel parameter table (some result) right)
    (hcomplete : DeferredCompletable table result.context)
    (hnoExhaustion : ¬AnyEncodingInputsExhausted right.2) (base : OtsSecretIndex → HashOutput) :
    completedStartTable (canonicalizeMaterializedValues table result.context).state base =
      completedStartTable result.context.state base := by
  funext start
  unfold completedStartTable
  rw [hrel.start_values_preserved_of_no_exhaustion hcomplete hnoExhaustion start]

theorem SigningStartFailureRunRel.historyHit_preserved_of_no_exhaustion
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {result : ResolvedRunResult (α × SplitHashCache)} {right : α × QueryCache HashSpec}
    (hrel : SigningStartFailureRunRel parameter table (some result) right)
    (hcomplete : DeferredCompletable table result.context)
    (hnoExhaustion : ¬AnyEncodingInputsExhausted right.2) (history : List Probe) (base : OtsSecretIndex → HashOutput) :
    ChainStartHistoryHit (canonicalizeMaterializedValues table result.context) history base =
      ChainStartHistoryHit result.context history base :=
  chainStartHistoryHit_eq_of_start_values_eq result.context (canonicalizeMaterializedValues table result.context)
    history base (hrel.start_values_preserved_of_no_exhaustion hcomplete hnoExhaustion)

end SphincsSecurity.Concrete.OtsProbeSimulation
