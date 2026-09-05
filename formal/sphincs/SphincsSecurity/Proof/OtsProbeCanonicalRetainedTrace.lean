import SphincsSecurity.Proof.OtsProbeCanonicalVerifierTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem canonicalMaterializedValues_of_mem_canonicalChronologicalQuery
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)) :
    CanonicalMaterializedValues table result.context := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some raw =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff, Option.some.injEq] at hcanonical
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table raw hconsistent hstarts hraw
      exact canonicalizeMaterializedValues_canonical table raw.context hcore.2.1

set_option maxRecDepth 100000 in
theorem canonicalMaterializedValues_of_mem_synchronizedCanonical
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context)
    (hresult : some result ∈ support (runSynchronizedResolved
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret) computation context fuel table cache)) :
    CanonicalMaterializedValues table result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure _ value context fuel table cache hcomplete] at hresult
        simp only [mem_support_pure_iff, Option.some.injEq] at hresult
        subst result
        exact hcanonical
      · rw [runSynchronizedResolved_pure_of_not_completable _ value context fuel table cache hcomplete] at hresult
        simp at hresult
  | query_bind input next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · simp only [dif_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨stepOption, hstep, htail⟩ := hresult
        cases stepOption with
        | none => simp at htail
        | some step =>
            have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret input
              context fuel cache step hconsistent hstarts hstep
            have hstepCanonical := canonicalMaterializedValues_of_mem_canonicalChronologicalQuery parameter root ftsSecret
              input context fuel table cache step hconsistent hstarts hstep
            change some result ∈ support (runSynchronizedResolved
              (canonicalChronologicalAdversaryImpl parameter root table ftsSecret) (next step.value.1)
              step.context step.remaining step.table step.value.2) at htail
            rw [hcore.1] at htail
            exact ih step.value.1 step.context step.remaining step.value.2 hcore.2.1 hcore.2.2 hstepCanonical htail
      · simp [hcomplete] at hresult

theorem finishResolvedRunIsNone_value_eq
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (left : α) (right : β) :
    finishResolvedRunIsNone (some ⟨context, fuel, left, table⟩) =
      finishResolvedRunIsNone (some ⟨context, fuel, right, table⟩) := by
  unfold finishResolvedRunIsNone finishResolvedRun
  dsimp only
  split_ifs
  · simp only [map_bind]
    apply bind_congr
    intro result
    cases result <;> simp
  · simp

theorem evalDist_canonicalVerifierFinish_eq_rest_finish
    (parameter : PublicParameter) (root : Digest) (forgeryLog : Forgery × QueryLog SigningSpec)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    evalDist (runResolvedFromTable context fuel table ((canonicalVerifierFinish parameter root forgeryLog).run cache) >>=
      finishResolvedRunIsNone) =
      evalDist (runResolvedFromTable context fuel table
        ((simulateQ (probingRomImpl parameter) (do
          let verified ← scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature
          pure (forgeryLog, verified))).run cache) >>= finishResolvedRunIsNone) := by
  unfold canonicalVerifierFinish
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, runResolvedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result _hresult
  cases result with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure, pure_bind]
      rw [finishResolvedRunIsNone_value_eq result.context result.remaining result.table
        ((root, (forgeryLog, result.value.1)), result.value.2) ((forgeryLog, result.value.1), result.value.2)]

set_option maxRecDepth 100000 in
theorem evalDist_synchronizedCanonicalRetainedRest_finish_eq_split
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (retainedGameRestComputation adversary ⟨root, parameter⟩) context fuel table cache >>= finishResolvedRunIsNone) =
      evalDist (do
        let result ← runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
          (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel table cache
        canonicalVerifierContinuation parameter root result >>= finishResolvedRunIsNone) := by
  unfold retainedGameRestComputation
  rw [runSynchronizedResolved_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => simp [canonicalVerifierContinuation, finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      have hcore := resolvedCore_of_mem_runSynchronizedResolved_canonicalChronological parameter root table ftsSecret
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel cache result
        hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hresult
      have hnextCanonical := canonicalMaterializedValues_of_mem_synchronizedCanonical parameter root ftsSecret
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel table cache result
        hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hcanonical hresult
      have hrel := relTriple_runSynchronizedResolved_reachable
        (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel cache actualCache
        hinvariant hvisible hpublished
      obtain ⟨actual, _hactual, hrelation⟩ := exists_right_of_relTriple_of_mem_support hrel hresult
      dsimp only [canonicalVerifierContinuation]
      rw [hcore.1]
      rcases hrelation with hclean | hdoomed
      · have hlift : liftOracleWorldLeft (do
            let verified ← scheme.verify ⟨root, parameter⟩ result.value.1.1.message result.value.1.1.signature
            pure (result.value.1, verified)) = (do
              let verified ← liftOracleWorldLeft
                (scheme.verify ⟨root, parameter⟩ result.value.1.1.message result.value.1.1.signature)
              pure ((result.value.1.1, result.value.1.2), verified)) := by
          simp only [liftOracleWorldLeft, liftM_bind, liftM_pure]
        rw [← hlift]
        change evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
          (liftOracleWorldLeft (do
            let verified ← scheme.verify ⟨root, parameter⟩ result.value.1.1.message result.value.1.1.signature
            pure (result.value.1, verified))) result.context result.remaining table result.value.2 >>=
              finishResolvedRunIsNone) = _
        rw [runSynchronizedResolved_liftOracleWorldLeft,
          evalDist_synchronizedCanonicalRom_finish_eq_raw parameter root ftsSecret _ result.context result.remaining
            table result.value.2 hcore.2.1 hcore.2.2 hnextCanonical hclean.2.2.2.2]
        exact (evalDist_canonicalVerifierFinish_eq_rest_finish parameter root result.value.1
          result.context result.remaining table result.value.2).symm
      · rw [runSynchronizedResolved_of_not_completable _ _ result.context result.remaining table result.value.2 hdoomed.2.2.2]
        simp only [pure_bind, finishResolvedRunIsNone, finishResolvedRun, map_pure, Option.isNone_none]
        exact (evalDist_runResolvedFinishIsNone_eq_true_of_not_completable result.context result.remaining table _
          hcore.2.1 hcore.2.2 hdoomed.2.2.2).symm

def retainedResultWithRoot (root : Digest) (result : ResolvedRunResult (RetainedRestResult × SplitHashCache)) :
    ResolvedRunResult (RetainedGameResult × SplitHashCache) :=
  ⟨result.context, result.remaining, ((root, result.value.1), result.value.2), result.table⟩

theorem finishResolvedRunIsNone_retainedRoot
    (root : Digest) (result : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache))) :
    finishResolvedRunIsNone (result.map (retainedResultWithRoot root)) = finishResolvedRunIsNone result := by
  cases result with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result => exact finishResolvedRunIsNone_value_eq result.context result.remaining result.table _ _

noncomputable def canonicalRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) := do
  let rootResult ← runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (none, [])
  | some result => do
      let rest ← runCanonicalQueryTrace parameter result.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining result.table result.value.2
      pure (rest.1.map (retainedResultWithRoot result.value.1), rest.2)

set_option maxRecDepth 100000 in
theorem evalDist_canonicalRetainedQueryTrace_finish_eq_original
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel >>=
      fun result => finishResolvedRunIsNone result.1) =
      evalDist (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
        finishResolvedRunIsNone) := by
  unfold canonicalRetainedQueryTrace canonicalChronologicalRetainedRunAfterFtsSecrets
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hroot
      have hcanonical := canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel result hroot
      have hrel := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
        (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
      obtain ⟨actual, _hactual, hrelation⟩ := exists_right_of_relTriple_of_mem_support hrel hroot
      dsimp only
      simp only [bind_assoc, pure_bind, finishResolvedRunIsNone_retainedRoot]
      rw [hcore.1, runCanonicalQueryTrace_observer_projection parameter result.value.1 ftsSecret _
        result.context result.remaining table result.value.2 _ hcore.2.1 hcore.2.2]
      rcases hrelation with hclean | hdoomed
      · simpa only [bind_assoc] using
          evalDist_synchronizedCanonicalRetainedRest_finish_eq_split adversary parameter result.value.1 table ftsSecret
          result.context result.remaining result.value.2 actual.2 hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hcanonical
      · rw [runSynchronizedResolved_of_not_completable _ _ result.context result.remaining table result.value.2 hdoomed.2.2.2,
          runSynchronizedResolved_of_not_completable _ _ result.context result.remaining table result.value.2 hdoomed.2.2.2]
        simp [canonicalVerifierContinuation, finishResolvedRunIsNone, finishResolvedRun]

theorem probEvent_winningRetainedVerifyProbe_le_canonicalQueryTrace_failure
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[= true | canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel >>=
        fun result => finishResolvedRunIsNone result.1] := by
  rw [_root_.OracleComp.probOutput_congr rfl
    (evalDist_canonicalRetainedQueryTrace_finish_eq_original adversary parameter table ftsSecret fuel)]
  have hbound := probEvent_winningRetainedVerifyProbe_le_canonicalFinishedResolvedRun_none adversary parameter table ftsSecret fuel
  rw [probEvent_eq_eq_probOutput, probEvent_finishResolvedRun_none_eq_isNone] at hbound
  exact hbound

theorem expectedCanonicalRetainedQueryTrace_charge_eq
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' result, Pr[= result | canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel] *
      canonicalTraceCharge (canonicalJointOuterCharge parameter) result.2) =
      canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel := by
  unfold canonicalRetainedQueryTrace canonicalJointChargeAfterTable
  rw [tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases result with
    | none => simp [canonicalTraceCharge]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hresult
        dsimp only
        simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
        rw [hcore.1, expectedCanonicalTraceCharge_eq]
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp

theorem expectedCanonicalRetainedQueryTrace_charge_le_gameReserve
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' result, Pr[= result | canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel] *
      canonicalTraceCharge (canonicalJointOuterCharge parameter) result.2) ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  rw [expectedCanonicalRetainedQueryTrace_charge_eq]
  exact canonicalJointChargeAfterTable_le_gameReserve adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
