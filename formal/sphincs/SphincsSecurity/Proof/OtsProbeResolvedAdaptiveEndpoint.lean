import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveBridge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def verifierFinishObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) : ProbComp Bool :=
  runResolvedFinishIsNone context fuel table
    ((canonicalVerifierFinish parameter root value.1).run value.2)

instance verifierFinishObserve_observerDooms
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest) :
    ObserverDooms table (verifierFinishObserve table parameter root) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact evalDist_runResolvedFinishIsNone_eq_true_of_not_completable context fuel table
      ((canonicalVerifierFinish parameter root value.1).run value.2)
        hconsistent hstarts hdoomed

instance verifierFinishObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest) :
    ObserverSynchronized table (verifierFinishObserve table parameter root) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    exact evalDist_runResolvedFinishIsNone_eq_of_finalizationSynchronized
      ((canonicalVerifierFinish parameter root value.1).run value.2)
        left right fuel table hcontext hvalues hrevealed

instance verifierFinishObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest) :
    ObserverPositionNeutral table (verifierFinishObserve table parameter root) where
  eq_resolve position context fuel value hvalid hcompletable hensured := by
    exact evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone position
      ((canonicalVerifierFinish parameter root value.1).run value.2)
        context fuel table hvalid hcompletable hensured

noncomputable def boundaryDeferredRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let rootResult ← runResolvedFromTable
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure true
  | some rootResult =>
      boundaryObserve (maskedExpandedAdversaryImpl parameter rootResult.value.1 ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        (verifierFinishObserve table parameter rootResult.value.1)
        rootResult.context rootResult.remaining table rootResult.value.2

theorem finalizationMaterializedCouples_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) :
    FinalizationMaterializedCouples table maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (finalizationMaterializedCouples_ensureTreeNode table topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact finalizationMaterializedCouples_revealPublishedCoordinate table
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

theorem resolvedPreservesPublished_maskedPublishedTreeRoot :
    ResolvedPreservesPublished maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (resolvedPreservesPublishedValues_ensureTreeNode topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact resolvedPreservesPublishedValues_revealPublishedCoordinate _

set_option maxRecDepth 100000 in
theorem resolvedCore_of_mem_runSynchronizedResolved_canonicalDeferred
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runSynchronizedResolved
        (canonicalDeferredAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table ∧ PublishedValues result.context.state := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache result with
  | pure value =>
      rw [runSynchronizedResolved_pure _ value context fuel table cache hcompletable] at hresult
      simp only [mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact ⟨rfl, hvalid.valuesConsistent,
        startTableAgrees_of_deferredCompletable hcompletable, hpublished⟩
  | query_bind query next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      simp only [dif_pos hcompletable, mem_support_bind_iff] at hresult
      obtain ⟨stepOption, hstep, htail⟩ := hresult
      cases stepOption with
      | none => simp at htail
      | some stepResult =>
          have hstepCore := canonicalDeferredAdversaryImpl_core parameter root table ftsSecret
            query context fuel cache stepResult hvalid hcompletable hpublished hstep
          change some result ∈ support
            (runSynchronizedResolved
              (canonicalDeferredAdversaryImpl parameter root table ftsSecret)
              (next stepResult.value.1) stepResult.context stepResult.remaining
                stepResult.table stepResult.value.2) at htail
          rw [hstepCore.1] at htail
          by_cases hnextCompletable : DeferredCompletable table stepResult.context
          · have hnextValid := valid_of_resolvedCore_completable table stepResult.context
              hstepCore.2.1 hstepCore.2.2.1 hnextCompletable
            exact ih stepResult.value.1 stepResult.context stepResult.remaining
              stepResult.value.2 result hnextValid hnextCompletable hstepCore.2.2.2 htail
          · rw [runSynchronizedResolved_of_not_completable] at htail
            · simp at htail
            · exact hnextCompletable

set_option maxRecDepth 100000 in
theorem evalDist_canonicalDeferredRetainedFinishIsNone_eq_boundary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist
        (canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
          finishResolvedRunIsNone) =
      evalDist
        (boundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret fuel) := by
  unfold canonicalDeferredRetainedRunAfterFtsSecrets
    boundaryDeferredRetainedFinishIsNone
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some rootResult =>
      have hrootCore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table
        fuel rootResult hroot
      have hrootInvariants :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
          maskedPublishedTreeRoot
          (finalizationMaterializedCouples_maskedPublishedTreeRoot table)
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel emptySplitHashCache rootResult DeferredContext.valid_empty
            (deferredCompletable_empty table) hroot
      have hrootPublished : PublishedValues rootResult.context.state :=
        resolvedPreservesPublished_maskedPublishedTreeRoot
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          emptySplitHashCache fuel table rootResult publishedValues_empty hroot
      simp only
      rw [hrootCore.1]
      calc
        _ = evalDist
            (runSynchronizedResolved
              (canonicalDeferredAdversaryImpl parameter rootResult.value.1 table ftsSecret)
              (signingTraceComputation
                (adversary.main ⟨rootResult.value.1, parameter⟩))
              rootResult.context rootResult.remaining table rootResult.value.2 >>=
                finishObserve
                  (verifierFinishObserve table parameter rootResult.value.1)) := by
              rw [bind_assoc]
              apply evalDist_bind_congr
              intro adversaryOption hadversary
              cases adversaryOption with
              | none => simp [canonicalVerifierContinuation, finishResolvedRunIsNone,
                  finishResolvedRun]
              | some adversaryResult =>
                  have hadversaryCore :=
                    resolvedCore_of_mem_runSynchronizedResolved_canonicalDeferred parameter
                      rootResult.value.1 table ftsSecret
                      (signingTraceComputation
                        (adversary.main ⟨rootResult.value.1, parameter⟩))
                      rootResult.context rootResult.remaining rootResult.value.2
                      adversaryResult hrootInvariants.1 hrootInvariants.2 hrootPublished
                        hadversary
                  simp [canonicalVerifierContinuation, finishObserve,
                    verifierFinishObserve, runResolvedFinishIsNone, hadversaryCore.1]
        _ = _ := evalDist_canonicalDeferred_adaptive_eq_boundaryObserve parameter
          rootResult.value.1 table ftsSecret
          (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
          (verifierFinishObserve table parameter rootResult.value.1)
          rootResult.context rootResult.remaining rootResult.value.2 hrootInvariants.1
            hrootInvariants.2 hrootPublished

end SphincsSecurity.Concrete.OtsProbeSimulation
