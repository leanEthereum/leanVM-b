import SphincsSecurity.Proof.OtsProbeSigningFailureCoupling
import SphincsSecurity.Proof.OtsProbeCanonicalVerifierTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalStartErasureStep
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult ((OracleWorld + SigningSpec).Range query × SplitHashCache)) × Bool) := do
  let result ← runResolvedFromTable context fuel table
    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
  pure (canonicalizeResolvedRun table result, decide (LiveSigningStartErasure table result))

def StartErasureTraceRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × Bool) (right : α × QueryCache HashSpec) : Prop :=
  ReachableResolvedRunRel parameter table left.1 right ∧ CanonicalResolvedRun table left.1 ∧
    (left.2 = true → AnyEncodingInputsExhausted right.2)

theorem relTriple_rawQuery_startFailure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache))
      ((unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
        query).run concreteCache)
      (SigningStartFailureRunRel parameter table) := by
  cases query with
  | inr message =>
      exact relTriple_sign_startFailure_concrete parameter root table ftsSecret message context fuel cache concreteCache
        hinvariant hvisible hpublished (materializedStartsPublished_of_canonical table context hcanonical)
  | inl query =>
      have hbase := reachableResolvedCouples_probingRomImpl parameter table query context fuel cache concreteCache
        hinvariant hvisible hpublished
      have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
        (fun left => left ∈ support (runResolvedFromTable context fuel table ((probingRomImpl parameter query).run cache)))
        (fun _ h => h)
      apply relTriple_post_mono hsupported
      intro left right hrel
      refine ⟨hrel.1, ?_⟩
      intro result heq _
      subst left
      exact Or.inl (materializedStartsPublished_of_canonical table result.context
        (canonicalMaterializedValues_of_mem_probingRomImpl parameter query context fuel table cache result
          hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hcanonical hpublished hrel.2))

theorem relTriple_canonicalStartErasureStep
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    RelTriple (canonicalStartErasureStep parameter root table ftsSecret query context fuel cache)
      ((unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
        query).run concreteCache)
      (StartErasureTraceRel parameter table) := by
  have hbase := relTriple_rawQuery_startFailure parameter root table ftsSecret query context fuel cache concreteCache
    hinvariant hvisible hpublished hcanonical
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left ∈ support (runResolvedFromTable context fuel table
      ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache))) (fun _ h => h)
  unfold canonicalStartErasureStep
  rw [show (unloggedMappedAdversaryImpl
      ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
      query).run concreteCache = (unloggedMappedAdversaryImpl
      ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
      query).run concreteCache >>= fun result => pure result by simp]
  apply relTriple_bind hsupported
  intro left right hrel
  apply relTriple_pure_pure
  refine ⟨hrel.1.1.canonicalizeResolvedRun, ?_, ?_⟩
  · apply canonicalResolvedRun_canonicalize table left
    intro result heq
    subst left
    exact (resolvedCore_of_mem_runResolvedFromTable _ context fuel table result
      hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hrel.2).2.1
  · intro hflag
    exact anyEncodingInputsExhausted_of_cachedOtsEncodingFailure right.2
      (hrel.1.encoding_failure_of_erasure (of_decide_eq_true hflag))

noncomputable def runCanonicalStartErasureTrace
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → SplitHashCache → Bool →
      ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool) :=
  OracleComp.construct
    (fun value context fuel cache flagged =>
      if DeferredCompletable table context then pure (some ⟨context, fuel, (value, cache), table⟩, flagged)
      else pure (none, flagged))
    (fun query _next recur context fuel cache flagged =>
      if DeferredCompletable table context then do
        let step ← canonicalStartErasureStep parameter root table ftsSecret query context fuel cache
        let flagged := flagged || step.2
        match step.1 with
        | none => pure (none, flagged)
        | some result => recur result.value.1 result.context result.remaining result.value.2 flagged
      else pure (none, flagged)) computation

theorem runCanonicalStartErasureTrace_of_not_completable
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (flagged : Bool)
    (hnot : ¬DeferredCompletable table context) :
    runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache flagged =
      pure (none, flagged) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [runCanonicalStartErasureTrace, OracleComp.construct_pure, if_neg hnot]
  | query_bind query next ih =>
      simp only [runCanonicalStartErasureTrace, OracleComp.construct_query_bind, if_neg hnot]

theorem relTriple_stoppedStartErasureTrace
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (flagged : Bool)
    (hflag : flagged = true → AnyEncodingInputsExhausted cache) :
    RelTriple (pure (none, flagged) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool))
      ((simulateQ (unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
        computation).run cache) (StartErasureTraceRel parameter table) := by
  have hbase := relTriple_true (pure (none, flagged) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool))
    ((simulateQ (unloggedMappedAdversaryImpl
      ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
      computation).run cache)
  have hleft := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun left => left = (none, flagged)) (by intro left h; simpa using h)
  apply relTriple_post_mono (FtsProbeSimulation.relTriple_and_right_support hleft)
  intro left right hrel
  rw [hrel.1.2]
  refine ⟨True.intro, True.intro, ?_⟩
  intro htrue
  exact (hflag htrue).mono (FtsProbeSimulation.simulateQ_unloggedMappedAdversaryImpl_cache_le _ computation
    cache right.2 right.1 hrel.2)

theorem relTriple_runCanonicalStartErasureTrace
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec) (flagged : Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context)
    (hflag : flagged = true → AnyEncodingInputsExhausted concreteCache) :
    RelTriple (runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache flagged)
      ((simulateQ (unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
        computation).run concreteCache) (StartErasureTraceRel parameter table) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache concreteCache flagged with
  | pure value =>
      simp only [runCanonicalStartErasureTrace, OracleComp.construct_pure, if_pos hinvariant.2.2.2.1,
        simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨Or.inl ⟨rfl, rfl, hinvariant, hvisible, hpublished⟩, hcanonical, hflag⟩
  | query_bind query next ih =>
      rw [runCanonicalStartErasureTrace, OracleComp.construct_query_bind, simulateQ_query_bind, StateT.run_bind]
      simp only [if_pos hinvariant.2.2.2.1]
      have hstep := relTriple_canonicalStartErasureStep parameter root table ftsSecret query context fuel cache concreteCache
        hinvariant hvisible hpublished hcanonical
      apply relTriple_bind (FtsProbeSimulation.relTriple_and_right_support hstep)
      rintro ⟨stepOption, stepFlag⟩ right hrel
      have hnextFlag : (flagged || stepFlag) = true → AnyEncodingInputsExhausted right.2 := by
        intro htrue
        rcases Bool.or_eq_true_iff.mp htrue with hprevious | hnew
        · exact (hflag hprevious).mono (unloggedMappedAdversaryImpl_cache_le _ query concreteCache right hrel.2)
        · exact hrel.1.2.2 hnew
      cases stepOption with
      | none =>
          exact relTriple_stoppedStartErasureTrace parameter root table ftsSecret (next right.1) right.2
            (flagged || stepFlag) hnextFlag
      | some result =>
          have hnextCanonical : CanonicalMaterializedValues table result.context := hrel.1.2.1
          rcases hrel.1.1 with hclean | hdoomed
          · rcases right with ⟨rightValue, rightCache⟩
            have hvalue : result.value.1 = rightValue := hclean.2.1
            subst rightValue
            exact ih result.value.1 result.context result.remaining result.value.2 rightCache (flagged || stepFlag)
              hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hnextCanonical hnextFlag
          · change RelTriple
              (runCanonicalStartErasureTrace parameter root table ftsSecret (next result.value.1)
                result.context result.remaining result.value.2 (flagged || stepFlag)) _ _
            rw [runCanonicalStartErasureTrace_of_not_completable parameter root table ftsSecret (next result.value.1)
              result.context result.remaining result.value.2 (flagged || stepFlag) hdoomed.2.2.2]
            exact relTriple_stoppedStartErasureTrace parameter root table ftsSecret (next right.1) right.2
              (flagged || stepFlag) hnextFlag

theorem probEvent_canonicalStartErasureTrace_le_exhaustion
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    Pr[fun result => result.2 = true |
      runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache false] ≤
    Pr[fun result => AnyEncodingInputsExhausted result.2 |
      (simulateQ (unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
        computation).run concreteCache] := by
  apply probEvent_le_of_relTriple (relTriple_runCanonicalStartErasureTrace parameter root table ftsSecret computation
    context fuel cache concreteCache false hinvariant hvisible hpublished hcanonical (by simp))
  intro left right hrel hflag
  exact hrel.2.2 hflag

theorem canonicalStartErasureStep_projection
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    Prod.fst <$> canonicalStartErasureStep parameter root table ftsSecret query context fuel cache =
      canonicalChronologicalAdversaryImpl parameter root table ftsSecret query context fuel table cache := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize]
  simp only [canonicalStartErasureStep, map_bind, map_pure]

theorem runCanonicalStartErasureTrace_projection
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (flagged : Bool)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (Prod.fst <$> runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache flagged) =
      evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache flagged with
  | pure value =>
      simp only [runCanonicalStartErasureTrace, runSynchronizedResolved, OracleComp.construct_pure]
      split_ifs <;> simp
  | query_bind query next ih =>
      rw [runCanonicalStartErasureTrace, OracleComp.construct_query_bind, runSynchronizedResolved,
        OracleComp.construct_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [if_pos hcomplete, dif_pos hcomplete, map_bind]
        rw [← canonicalStartErasureStep_projection, bind_map_left]
        apply evalDist_bind_congr
        rintro ⟨stepOption, stepFlag⟩ hstep
        have hproject : stepOption ∈ support
            (canonicalChronologicalAdversaryImpl parameter root table ftsSecret query context fuel table cache) := by
          rw [← canonicalStartErasureStep_projection, support_map]
          exact ⟨(stepOption, stepFlag), hstep, rfl⟩
        cases stepOption with
        | none => simp
        | some result =>
            have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret query
              context fuel cache result hconsistent hstarts hproject
            dsimp only
            rw [hcore.1]
            exact ih result.value.1 result.context result.remaining result.value.2 (flagged || stepFlag) hcore.2.1 hcore.2.2
      · simp [hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
