import SphincsSecurity.Proof.OtsProbeHistoryOuterComposition
import SphincsSecurity.Proof.OtsProbeStartErasureBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable def eraseFlaggedResult (result : Option (ResolvedRunResult α) × Bool) :
    Option (ResolvedRunResult α) := if result.2 then none else result.1

theorem runCanonicalStartErasureTrace_query_bind
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range query → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (flagged : Bool) :
    runCanonicalStartErasureTrace parameter root table ftsSecret (OracleSpec.query query >>= next) context fuel cache flagged =
      (if DeferredCompletable table context then do
        let step ← canonicalStartErasureStep parameter root table ftsSecret query context fuel cache
        match step.1 with
        | none => pure (none, flagged || step.2)
        | some result =>
            runCanonicalStartErasureTrace parameter root table ftsSecret (next result.value.1)
              result.context result.remaining result.value.2 (flagged || step.2)
      else pure (none, flagged)) := by
  rfl

theorem runGuardedCanonicalNative_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range query → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runGuardedCanonicalNative parameter root ftsSecret (OracleSpec.query query >>= next) context fuel table cache =
      (do
        let raw ← runResolvedFromTable context fuel table
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
        match canonicalHistoryBoundary raw with
        | none => pure none
        | some result =>
            runGuardedCanonicalNative parameter root ftsSecret (next result.value.1)
              result.context result.remaining result.table result.value.2) := by
  rfl

theorem canonicalHistoryBoundary_of_erasure
    (result : ResolvedRunResult (α × SplitHashCache))
    (herasure : LiveSigningStartErasure result.table (some result)) :
    canonicalHistoryBoundary (some result) = none := by
  have hnot : ¬MaterializedStartsPublished result.context := by
    intro hpublic
    obtain ⟨_, start, hknown, herased⟩ := herasure
    have hrevealed := hpublic start hknown
    change (if start.coordinate ∈ result.context.state.revealed then some (result.table start) else none) = none at herased
    simp [hrevealed] at herased
  simp [canonicalHistoryBoundary, hnot]

theorem resolvedPreservesPublishedValues_maskedChronologicalExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) :
    ResolvedPreservesPublished (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query) := by
  cases query with
  | inl query => exact resolvedPreservesPublishedValuesImpl_probingRomImpl parameter query
  | inr message => exact resolvedPreservesPublishedValues_maskedPublishedChronologicalSign parameter root ftsSecret message

theorem evalDist_guardedCanonicalNative_of_not_completable
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runGuardedCanonicalNative parameter root ftsSecret computation context fuel table cache) =
      evalDist (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [runGuardedCanonicalNative, canonicalHistoryBoundary, hdoomed]
  | query_bind query next ih =>
      rw [runGuardedCanonicalNative, OracleComp.construct_query_bind]
      apply evalDist_runResolved_observe_of_not_completable context fuel table _ (pure none) _
        (by rfl) _ hconsistent hstarts hdoomed
      intro result _ _ hdead
      simp [canonicalHistoryBoundary, hdead]

theorem evalDist_eraseFlagged_trace_true
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    evalDist (eraseFlaggedResult <$> runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache true) =
      evalDist (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp only [runCanonicalStartErasureTrace, OracleComp.construct_pure]
      split_ifs <;> simp [eraseFlaggedResult]
  | query_bind query next ih =>
      rw [runCanonicalStartErasureTrace_query_bind]
      split_ifs
      · rw [map_bind]
        calc
          _ = evalDist (canonicalStartErasureStep parameter root table ftsSecret query context fuel cache >>= fun _ =>
              (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))) := by
            apply evalDist_bind_congr
            rintro ⟨option, flag⟩ _
            cases option with
            | none => simp [eraseFlaggedResult]
            | some entry => simpa only [Bool.true_or] using ih entry.value.1 entry.context entry.remaining entry.value.2
          _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp [canonicalStartErasureStep, runResolvedFromTable]) _
      · simp [eraseFlaggedResult]

theorem evalDist_eraseFlagged_trace_eq_guardedCanonicalNative
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (eraseFlaggedResult <$> runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache false) =
      evalDist (runGuardedCanonicalNative parameter root ftsSecret computation context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      have hpublic := materializedStartsPublished_of_canonical table context hcanonical
      simp only [runCanonicalStartErasureTrace, runGuardedCanonicalNative, OracleComp.construct_pure]
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [eraseFlaggedResult, canonicalHistoryBoundary, hcomplete, hpublic, hpublished,
          canonicalizeMaterializedValues_eq_of_canonical table context hcanonical]
  | query_bind query next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runCanonicalStartErasureTrace_query_bind, if_pos hcomplete, runGuardedCanonicalNative_query_bind]
        simp only [canonicalStartErasureStep, map_bind, bind_assoc, pure_bind, Bool.false_or]
        apply evalDist_bind_congr
        intro option hoption
        cases option with
        | none => simp [canonicalizeResolvedRun, canonicalHistoryBoundary, LiveSigningStartErasure, eraseFlaggedResult]
        | some result =>
            have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
            have hpub := resolvedPreservesPublishedValues_maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query
              context cache fuel table result hpublished hoption
            have hcanonicalNext := canonicalizeMaterializedValues_canonical table result.context hcore.2.1
            have hconsistentNext := canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1
            have hstartsNext := canonicalizeMaterializedValues_startTableAgrees table result.context
            have hpubNext : PublishedValues (canonicalizeMaterializedValues table result.context).state := hpub.to_canonicalizedMaterializedValues
            by_cases herasure : LiveSigningStartErasure table (some result)
            · have hboundary := canonicalHistoryBoundary_of_erasure result (hcore.1 ▸ herasure)
              simp only [hboundary, decide_true, herasure, canonicalizeResolvedRun]
              exact evalDist_eraseFlagged_trace_true parameter root table ftsSecret (next result.value.1)
                (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            · have hboundary := canonicalHistoryBoundary_eq_liveCanonical_of_no_erasure result hcore.2.1
                (hcore.1 ▸ hcore.2.2) hpub (hcore.1 ▸ herasure)
              rw [hboundary]
              simp only [canonicalizeResolvedRun, hcore.1, decide_eq_false herasure]
              by_cases hlive : DeferredCompletable table (canonicalizeMaterializedValues table result.context)
              · simp only [retainCompletableResult, if_pos hlive]
                exact ih result.value.1 (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
                  hconsistentNext hstartsNext hpubNext hcanonicalNext
              · simp only [retainCompletableResult, if_neg hlive]
                rw [runCanonicalStartErasureTrace_of_not_completable parameter root table ftsSecret (next result.value.1)
                  (canonicalizeMaterializedValues table result.context) result.remaining result.value.2 false hlive]
                simp [eraseFlaggedResult]
      · rw [runCanonicalStartErasureTrace_of_not_completable parameter root table ftsSecret _ context fuel cache false hcomplete]
        simp only [map_pure, eraseFlaggedResult, Bool.false_eq_true, if_false]
        exact (evalDist_guardedCanonicalNative_of_not_completable parameter root ftsSecret _ context fuel table cache
          hconsistent hstarts hcomplete).symm

theorem probEvent_fst_le_erased_add_flag
    (run : ProbComp (Option (ResolvedRunResult α) × Bool)) (event : Option (ResolvedRunResult α) → Prop) :
    Pr[event | Prod.fst <$> run] ≤
      Pr[event | eraseFlaggedResult <$> run] + Pr[fun result => result.2 = true | run] := by
  simp only [probEvent_map]
  calc
    _ ≤ Pr[fun result => event (eraseFlaggedResult result) ∨ result.2 = true | run] := by
      apply probEvent_mono
      intro result _ hevent
      by_cases hflag : result.2 = true
      · exact Or.inr hflag
      · exact Or.inl (by simpa [eraseFlaggedResult, hflag] using hevent)
    _ ≤ _ := probEvent_or_le _ _ _

theorem expected_erased_le_fst
    (run : ProbComp (Option (ResolvedRunResult α) × Bool))
    (cost : Option (ResolvedRunResult α) → ENNReal) (hnone : cost none = 0) :
    (∑' result, Pr[= result | eraseFlaggedResult <$> run] * cost result) ≤
      ∑' result, Pr[= result | Prod.fst <$> run] * cost result := by
  simp only [tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  by_cases hflag : result.2 = true
  · simp [eraseFlaggedResult, hflag, hnone]
  · simp [eraseFlaggedResult, hflag]

theorem probEvent_canonical_le_guarded_add_erasure
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (event : Option (ResolvedRunResult (α × SplitHashCache)) → Prop)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) (hcanonical : CanonicalMaterializedValues table context) :
    Pr[event | runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      computation context fuel table cache] ≤
    Pr[event | runGuardedCanonicalNative parameter root ftsSecret computation context fuel table cache] +
      Pr[fun result => result.2 = true |
        runCanonicalStartErasureTrace parameter root table ftsSecret computation context fuel cache false] := by
  have hprojection := runCanonicalStartErasureTrace_projection parameter root table ftsSecret computation context fuel cache
    false hconsistent hstarts
  have hguard := evalDist_eraseFlagged_trace_eq_guardedCanonicalNative parameter root table ftsSecret computation context fuel cache
    hconsistent hstarts hpublished hcanonical
  rw [← OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hprojection,
    ← OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hguard]
  exact probEvent_fst_le_erased_add_flag _ event

noncomputable def guardedCanonicalAfterRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache))) := do
  let root ← runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match root with
  | none => pure none
  | some root =>
      runGuardedCanonicalNative parameter root.value.1 ftsSecret (continuation root.value.1)
        root.context root.remaining table root.value.2

theorem evalDist_eraseFlagged_afterRoot_eq_guarded
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    evalDist (eraseFlaggedResult <$> canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation) =
      evalDist (guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation) := by
  simp only [canonicalStartErasureAfterRoot, guardedCanonicalAfterRoot, map_bind]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp [eraseFlaggedResult]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable _ _ fuel table result
        DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hoption
      exact evalDist_eraseFlagged_trace_eq_guardedCanonicalNative parameter result.value.1 table ftsSecret
        (continuation result.value.1) result.context result.remaining result.value.2 hcore.2.1 hcore.2.2
        (resolvedPreservesPublished_maskedPublishedTreeRoot _ _ _ _ _ publishedValues_empty hoption)
        (canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel result hoption)

theorem probEvent_canonicalAfterRoot_le_guarded_add_inv216
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (event : Option (ResolvedRunResult (α × SplitHashCache)) → Prop) :
    Pr[event | Prod.fst <$> canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation] ≤
      Pr[event | guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation] + ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hguard := evalDist_eraseFlagged_afterRoot_eq_guarded parameter table ftsSecret fuel continuation
  rw [← OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hguard]
  exact (probEvent_fst_le_erased_add_flag _ event).trans
    (add_le_add le_rfl (probEvent_canonicalStartErasureAfterRoot_le_inv216 parameter table ftsSecret fuel continuation))

noncomputable def sampledGuardedCanonicalRetained (adversary : Adversary) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))) := do
  let parameter ← sampleParameter
  let table ← sampleOtsHashTable
  let ftsSecret ← sampleFtsSecrets
  guardedCanonicalAfterRoot parameter table ftsSecret fuel fun root =>
    (fun rest => (root, rest)) <$> retainedGameRestComputation adversary ⟨root, parameter⟩

theorem evalDist_eraseFlagged_sampledTrace_eq_guarded (adversary : Adversary) (fuel : Nat) :
    evalDist (eraseFlaggedResult <$> sampledCanonicalStartErasureTrace adversary fuel) =
      evalDist (sampledGuardedCanonicalRetained adversary fuel) := by
  simp only [sampledCanonicalStartErasureTrace, sampledGuardedCanonicalRetained, map_bind]
  apply evalDist_bind_congr
  intro parameter _
  apply evalDist_bind_congr
  intro table _
  apply evalDist_bind_congr
  intro ftsSecret _
  exact evalDist_eraseFlagged_afterRoot_eq_guarded parameter table ftsSecret fuel _

theorem probEvent_sampledCanonical_le_guarded_add_inv216
    (adversary : Adversary) (fuel : Nat)
    (event : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) → Prop) :
    Pr[event | Prod.fst <$> sampledCanonicalStartErasureTrace adversary fuel] ≤
      Pr[event | sampledGuardedCanonicalRetained adversary fuel] + ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  rw [← OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_eraseFlagged_sampledTrace_eq_guarded adversary fuel)]
  exact (probEvent_fst_le_erased_add_flag _ event).trans
    (add_le_add le_rfl (probEvent_sampledCanonicalStartErasureTrace_le_inv216 adversary fuel))

end SphincsSecurity.Concrete.OtsProbeSimulation
