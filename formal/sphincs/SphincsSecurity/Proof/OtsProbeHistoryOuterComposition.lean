import SphincsSecurity.Proof.OtsProbeHistoryOuterPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def runGuardedCanonicalNative
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option (ResolvedRunResult (α × SplitHashCache))) :=
  OracleComp.construct
    (fun value context fuel table cache => pure (canonicalHistoryBoundary (some ⟨context, fuel, (value, cache), table⟩)))
    (fun query _next recur context fuel table cache => do
      let result ← runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
      match canonicalHistoryBoundary result with
      | none => pure none
      | some result => recur result.value.1 result.context result.remaining result.table result.value.2) computation

noncomputable def sampledGuardedCanonicalNative
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache))) := do
  let base ← sampleOtsHashTable
  if ChainStartHistoryHit context history base then pure none
  else runGuardedCanonicalNative parameter root ftsSecret computation context fuel (completedStartTable context.state base) cache

noncomputable def runCanonicalHistoryAdaptive
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → List Probe → SplitHashCache → ProbComp (Option (ResolvedRunResult (α × SplitHashCache))) :=
  OracleComp.construct
    (fun value context fuel history cache =>
      completeHistoryResolvedPrefix (canonicalHistoryPrefix (some ⟨context, fuel, (value, cache), history⟩)))
    (fun query _next recur context fuel history cache => do
      let option ← runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache
      match option with
      | none => pure none
      | some entry => recur entry.value.1 entry.context entry.remaining entry.history entry.value.2) computation

noncomputable def guardedCanonicalNativeContinuation
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α) :
    Option (ResolvedRunResult (β × SplitHashCache)) → ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))
  | none => pure none
  | some result => runGuardedCanonicalNative parameter root ftsSecret (next result.value.1)
      result.context result.remaining result.table result.value.2

theorem completeHistoryResolvedPrefix_guardedContinuation
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α) (entry : HistoryResolvedPrefix (β × SplitHashCache)) :
    (completeHistoryResolvedPrefix (some entry) >>= guardedCanonicalNativeContinuation parameter root ftsSecret next) =
      sampledGuardedCanonicalNative parameter root ftsSecret (next entry.value.1)
        entry.context entry.remaining entry.history entry.value.2 := by
  simp only [completeHistoryResolvedPrefix, completeResolvedHistory, sampledGuardedCanonicalNative, bind_assoc]
  apply bind_congr
  intro base
  split_ifs <;> simp only [pure_bind, guardedCanonicalNativeContinuation]

theorem sampledGuardedCanonicalNative_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range query → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    sampledGuardedCanonicalNative parameter root ftsSecret (OracleSpec.query query >>= next) context fuel history cache =
      (sampledHistoryFilteredRun ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
        context fuel history >>= fun result =>
          guardedCanonicalNativeContinuation parameter root ftsSecret next (canonicalHistoryBoundary result)) := by
  simp only [sampledGuardedCanonicalNative, sampledHistoryFilteredRun, bind_assoc]
  apply bind_congr
  intro base
  split_ifs
  · simp only [pure_bind, canonicalHistoryBoundary, guardedCanonicalNativeContinuation]
  · rw [runGuardedCanonicalNative, OracleComp.construct_query_bind]
    apply bind_congr
    intro result
    cases canonicalHistoryBoundary result <;> rfl

theorem evalDist_sampledGuardedCanonicalNative_eq_historyAdaptive
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hpublished : PublishedValues context.state)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (hbudget : history.length + bound ≤ 2 ^ 126) :
    evalDist (sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache) =
      evalDist (runCanonicalHistoryAdaptive parameter root ftsSecret computation context fuel history cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel bound history cache with
  | pure value =>
      have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
      have hcard : context.state.pending.card < Fintype.card Digest :=
        (hcovered.card_le.trans (by omega : history.length ≤ 2 ^ 126)).trans_lt hspace
      have h := completeHistoryResolvedPrefix_canonicalBoundary
        (⟨context, fuel, (value, cache), history⟩ : HistoryResolvedPrefix (α × SplitHashCache)) hconsistent hcovered hcard
      simp only [runCanonicalHistoryAdaptive, OracleComp.construct_pure]
      calc
        _ = evalDist (completeHistoryResolvedPrefix (some ⟨context, fuel, (value, cache), history⟩) >>=
            fun result => pure (canonicalHistoryBoundary result)) := by
          simp only [sampledGuardedCanonicalNative, completeHistoryResolvedPrefix, completeResolvedHistory, bind_assoc]
          apply evalDist_bind_congr
          intro base _
          split_ifs <;> simp only [runGuardedCanonicalNative, OracleComp.construct_pure, pure_bind, canonicalHistoryBoundary]
        _ = _ := h
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hqueryBudget : history.length + (if IsOuterHash query then 1 else 0) ≤ 2 ^ 126 := by
        by_cases hhash : IsOuterHash query
        · have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hhash)
          simp only [if_pos hhash]
          omega
        · simp only [if_neg hhash]
          omega
      have hquery := evalDist_sampledHistoryOuter_canonicalPrefix_observe parameter root ftsSecret query context fuel history cache
        (fun _ => guardedCanonicalNativeContinuation parameter root ftsSecret next) hconsistent
        (fun index hrevealed => hpublished index.coordinate hrevealed) hcovered hqueryBudget
      rw [sampledGuardedCanonicalNative_query_bind]
      calc
        _ = _ := hquery
        _ = _ := by
          rw [runCanonicalHistoryAdaptive, OracleComp.construct_query_bind]
          apply evalDist_bind_congr
          intro option hsupport
          cases option with
          | none => rfl
          | some entry =>
              dsimp only
              rw [completeHistoryResolvedPrefix_guardedContinuation]
              have hinvariant := canonicalHistoryOuterPrefix_invariant parameter root ftsSecret query context fuel history cache
                entry hconsistent hcovered hsupport
              have hlength := canonicalHistoryOuterPrefix_history_length parameter root ftsSecret query context fuel history cache
                entry hsupport
              have hnextBound := hbound.2 entry.value.1
              apply ih entry.value.1 entry.context entry.remaining
                (if IsOuterHash query then bound - 1 else bound) entry.history entry.value.2
                hinvariant.1 hinvariant.2.1 hinvariant.2.2.1 hnextBound
              by_cases hhash : IsOuterHash query
              · have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hhash)
                simp only [if_pos hhash] at hlength ⊢
                omega
              · simp only [if_neg hhash] at hlength ⊢
                omega

noncomputable def runCanonicalHistoryAdaptivePrefix
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → List Probe → SplitHashCache → ProbComp (Option (HistoryResolvedPrefix (α × SplitHashCache))) :=
  OracleComp.construct
    (fun value context fuel history cache => pure (canonicalHistoryPrefix (some ⟨context, fuel, (value, cache), history⟩)))
    (fun query _next recur context fuel history cache => do
      let option ← runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache
      match option with
      | none => pure none
      | some entry => recur entry.value.1 entry.context entry.remaining entry.history entry.value.2) computation

theorem runCanonicalHistoryAdaptive_eq_prefix_complete
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runCanonicalHistoryAdaptive parameter root ftsSecret computation context fuel history cache =
      runCanonicalHistoryAdaptivePrefix parameter root ftsSecret computation context fuel history cache >>= completeHistoryResolvedPrefix := by
  induction computation using OracleComp.inductionOn generalizing context fuel history cache with
  | pure value => simp only [runCanonicalHistoryAdaptive, runCanonicalHistoryAdaptivePrefix, OracleComp.construct_pure, pure_bind]
  | query_bind query next ih =>
      rw [runCanonicalHistoryAdaptive, OracleComp.construct_query_bind, runCanonicalHistoryAdaptivePrefix,
        OracleComp.construct_query_bind, bind_assoc]
      apply bind_congr
      intro option
      cases option with
      | none => simp only [pure_bind, completeHistoryResolvedPrefix]
      | some entry => exact ih entry.value.1 entry.context entry.remaining entry.history entry.value.2

theorem canonicalHistoryAdaptivePrefix_history_length
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (α × SplitHashCache))
    (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (hresult : some result ∈ support (runCanonicalHistoryAdaptivePrefix parameter root ftsSecret computation context fuel history cache)) :
    result.history.length ≤ history.length + bound := by
  induction computation using OracleComp.inductionOn generalizing context fuel bound history cache with
  | pure value =>
      simp only [runCanonicalHistoryAdaptivePrefix, OracleComp.construct_pure, mem_support_pure_iff] at hresult
      have hhistory := canonicalHistoryPrefix_history_length _ result hresult.symm
      rw [hhistory]
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runCanonicalHistoryAdaptivePrefix, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨option, hstep, htail⟩ := hresult
      cases option with
      | none => simp at htail
      | some entry =>
          have hlength := canonicalHistoryOuterPrefix_history_length parameter root ftsSecret query context fuel history cache entry hstep
          have hrest := ih entry.value.1 entry.context entry.remaining
            (if IsOuterHash query then bound - 1 else bound) entry.history entry.value.2 (hbound.2 entry.value.1) htail
          by_cases hhash : IsOuterHash query
          · have hpositive := hbound.1.resolve_left (not_not.mpr hhash)
            simp only [if_pos hhash] at hlength hrest
            omega
          · simp only [if_neg hhash] at hlength hrest
            omega

theorem expected_guardedCanonical_unresolvedStart_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (cache : SplitHashCache)
    (candidate : DeferredContext → (α × SplitHashCache) → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hpublished : PublishedValues context.state)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (hbudget : history.length + bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] *
      historyUnresolvedStartAllowance candidate result) ≤
    (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] *
      historyUnresolvedStartCharge candidate result) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hdist := evalDist_sampledGuardedCanonicalNative_eq_historyAdaptive parameter root ftsSecret computation context fuel bound
    history cache hconsistent hcovered hpublished hbound hbudget
  rw [runCanonicalHistoryAdaptive_eq_prefix_complete] at hdist
  have hcost (cost : Option (ResolvedRunResult (α × SplitHashCache)) → ENNReal) :
      (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] * cost result) =
      ∑' result, Pr[= result | runCanonicalHistoryAdaptivePrefix parameter root ftsSecret computation context fuel history cache >>=
        completeHistoryResolvedPrefix] * cost result := by
    apply tsum_congr
    intro result
    rw [_root_.OracleComp.probOutput_congr rfl hdist]
  rw [hcost, hcost]
  simp only [tsum_probOutput_bind_mul]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hsupport : option ∈ support (runCanonicalHistoryAdaptivePrefix parameter root ftsSecret computation context fuel history cache)
  · cases option with
    | none => simp [completeHistoryResolvedPrefix, historyUnresolvedStartAllowance, historyUnresolvedStartCharge]
    | some entry =>
        have hlength := canonicalHistoryAdaptivePrefix_history_length parameter root ftsSecret computation context fuel bound
          history cache entry hbound hsupport
        have hlocal := expected_completeHistoryResolvedPrefix_unresolvedStart_le entry candidate (hlength.trans hbudget)
        simpa only [mul_assoc] using mul_le_mul' le_rfl hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

theorem retainCompletableResult_of_mem_guardedCanonicalNative
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : Option (ResolvedRunResult (α × SplitHashCache)))
    (hresult : result ∈ support (runGuardedCanonicalNative parameter root ftsSecret computation context fuel table cache)) :
    retainCompletableResult result = result := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [runGuardedCanonicalNative, OracleComp.construct_pure, mem_support_pure_iff] at hresult
      subst result
      exact retainCompletableResult_canonicalHistoryBoundary _
  | query_bind query next ih =>
      rw [runGuardedCanonicalNative, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, _, htail⟩ := hresult
      cases hboundary : canonicalHistoryBoundary raw with
      | none =>
          simp only [hboundary, mem_support_pure_iff] at htail
          subst result
          rfl
      | some entry =>
          rw [hboundary] at htail
          exact ih entry.value.1 entry.context entry.remaining entry.table entry.value.2 htail

theorem retainCompletableResult_of_mem_sampledGuardedCanonicalNative
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (result : Option (ResolvedRunResult (α × SplitHashCache)))
    (hresult : result ∈ support (sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache)) :
    retainCompletableResult result = result := by
  rw [sampledGuardedCanonicalNative, mem_support_bind_iff] at hresult
  obtain ⟨base, _, hresult⟩ := hresult
  split_ifs at hresult with hhit
  · simp only [mem_support_pure_iff] at hresult
    subst result
    rfl
  · exact retainCompletableResult_of_mem_guardedCanonicalNative parameter root ftsSecret computation context fuel
      (completedStartTable context.state base) cache result hresult

theorem probEvent_guardedCanonical_unresolvedStart_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (cache : SplitHashCache)
    (candidate : DeferredContext → (α × SplitHashCache) → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hpublished : PublishedValues context.state)
    (hbound : computation.IsQueryBoundP IsOuterHash bound) (hbudget : history.length + bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] ≤
      (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] *
        historyUnresolvedStartCharge candidate result) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected]
  have hretain :
      (∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] *
        historyUnresolvedStartAllowance candidate (retainCompletableResult result)) =
      ∑' result, Pr[= result | sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache] *
        historyUnresolvedStartAllowance candidate result := by
    apply tsum_congr
    intro result
    by_cases hsupport : result ∈ support (sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache)
    · rw [retainCompletableResult_of_mem_sampledGuardedCanonicalNative parameter root ftsSecret computation context fuel history cache result hsupport]
    · simp [probOutput_eq_zero_of_not_mem_support hsupport]
  rw [hretain]
  exact expected_guardedCanonical_unresolvedStart_le parameter root ftsSecret computation context fuel bound history cache candidate
    hconsistent hcovered hpublished hbound hbudget

end SphincsSecurity.Concrete.OtsProbeSimulation
