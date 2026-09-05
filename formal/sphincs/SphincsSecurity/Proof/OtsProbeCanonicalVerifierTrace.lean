import SphincsSecurity.Proof.OtsProbePublicHashValues
import SphincsSecurity.Proof.OtsProbeQueryTraceProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem canonicalMaterializedValues_of_mem_probingRomImpl
    (parameter : PublicParameter) (query : OracleWorld.Domain)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (OracleWorld.Range query × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((probingRomImpl parameter query).run cache))) :
    CanonicalMaterializedValues table result.context := by
  have hcore := resolvedCore_of_mem_runResolvedFromTable ((probingRomImpl parameter query).run cache)
    context fuel table result hconsistent hstarts hresult
  exact canonicalMaterializedValues_of_public
    (resolvedPreservesPublicMaterialization_probingRomImpl parameter query context cache fuel table result
      (.of_canonical hcanonical) hresult)
    (resolvedPreservesPublishedValuesImpl_probingRomImpl parameter query context cache fuel table result hpublished hresult)
    hcore.2.2

theorem evalDist_canonicalChronologicalAdversaryImpl_oracle_eq_raw
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : OracleWorld.Domain) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (hpublished : PublishedValues context.state) :
    evalDist (canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl query) context fuel table cache) =
      evalDist (runResolvedFromTable context fuel table ((probingRomImpl parameter query).run cache)) := by
  unfold canonicalChronologicalAdversaryImpl
  conv_rhs => rw [← bind_pure (runResolvedFromTable context fuel table ((probingRomImpl parameter query).run cache))]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcanonicalResult := canonicalMaterializedValues_of_mem_probingRomImpl parameter query context fuel table cache
        result hconsistent hstarts hcanonical hpublished hresult
      simp only [canonicalizeResolvedRun, canonicalizeMaterializedValues_eq_of_canonical table result.context hcanonicalResult]
      rfl

set_option maxRecDepth 100000 in
theorem runSynchronizedResolved_liftOracleWorldLeft
    (impl : ResolvedQueryImpl (OracleWorld + SigningSpec)) (computation : OracleComp OracleWorld α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runSynchronizedResolved impl (liftOracleWorldLeft computation) context fuel table cache =
      runSynchronizedResolved (fun query => impl (.inl query)) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => rfl
  | query_bind input next ih =>
      change runSynchronizedResolved impl ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl input)) :
        OracleComp (OracleWorld + SigningSpec) (OracleWorld.Range input)) >>= fun value => liftOracleWorldLeft (next value))
        context fuel table cache = _
      rw [runSynchronizedResolved, OracleComp.construct_query_bind,
        runSynchronizedResolved, OracleComp.construct_query_bind]
      split_ifs
      · apply bind_congr
        intro result
        cases result with
        | none => rfl
        | some result => exact ih result.value.1 result.context result.remaining result.table result.value.2
      · rfl

set_option maxRecDepth 100000 in
theorem evalDist_synchronizedCanonicalRom_finish_eq_raw
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (hpublished : PublishedValues context.state) :
    evalDist (runSynchronizedResolved
      (fun query => canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl query))
      computation context fuel table cache >>= finishResolvedRunIsNone) =
      evalDist (runResolvedFromTable context fuel table ((simulateQ (probingRomImpl parameter) computation).run cache) >>=
        finishResolvedRunIsNone) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure _ value context fuel table cache hcomplete]
        simp [simulateQ_pure, runResolvedFromTable]
      · rw [runSynchronizedResolved_pure_of_not_completable _ value context fuel table cache hcomplete]
        simp [simulateQ_pure, runResolvedFromTable, finishResolvedRunIsNone, finishResolvedRun, hcomplete]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runSynchronizedResolved, OracleComp.construct_query_bind]
        simp only [dif_pos hcomplete, bind_assoc]
        rw [simulateQ_query_bind, StateT.run_bind, runResolvedFromTable_bind, bind_assoc]
        rw [evalDist_bind, evalDist_canonicalChronologicalAdversaryImpl_oracle_eq_raw parameter root ftsSecret input
          context fuel table cache hconsistent hstarts hcanonical hpublished, ← evalDist_bind]
        apply evalDist_bind_congr
        intro result hresult
        cases result with
        | none => simp
        | some result =>
            have hcore := resolvedCore_of_mem_runResolvedFromTable ((probingRomImpl parameter input).run cache)
              context fuel table result hconsistent hstarts hresult
            have hnextCanonical := canonicalMaterializedValues_of_mem_probingRomImpl parameter input context fuel table cache
              result hconsistent hstarts hcanonical hpublished hresult
            have hnextPublished := resolvedPreservesPublishedValuesImpl_probingRomImpl parameter input context cache fuel table
              result hpublished hresult
            dsimp only
            rw [hcore.1]
            exact ih result.value.1 result.context result.remaining result.value.2 hcore.2.1 hcore.2.2
              hnextCanonical hnextPublished
      · rw [runSynchronizedResolved_of_not_completable _ _ context fuel table cache hcomplete]
        simp only [pure_bind, finishResolvedRunIsNone, finishResolvedRun, map_pure, Option.isNone_none]
        exact (evalDist_runResolvedFinishIsNone_eq_true_of_not_completable context fuel table _
          hconsistent hstarts hcomplete).symm

theorem evalDist_canonicalQueryTrace_oracle_finish_eq_raw
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp OracleWorld α) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (hpublished : PublishedValues context.state) :
    evalDist (runCanonicalQueryTrace parameter root ftsSecret (liftOracleWorldLeft computation) context fuel table cache >>=
      fun result => finishResolvedRunIsNone result.1) =
      evalDist (runResolvedFromTable context fuel table ((simulateQ (probingRomImpl parameter) computation).run cache) >>=
        finishResolvedRunIsNone) := by
  rw [runCanonicalQueryTrace_observer_projection parameter root ftsSecret _ context fuel table cache _ hconsistent hstarts,
    runSynchronizedResolved_liftOracleWorldLeft]
  exact evalDist_synchronizedCanonicalRom_finish_eq_raw parameter root ftsSecret computation context fuel table cache
    hconsistent hstarts hcanonical hpublished

end SphincsSecurity.Concrete.OtsProbeSimulation
