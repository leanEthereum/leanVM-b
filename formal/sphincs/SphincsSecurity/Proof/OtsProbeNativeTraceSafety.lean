import SphincsSecurity.Proof.OtsProbeNativeSupportedBudget

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem pendingCoveredBy_of_mem_nativeChronologicalQuery
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (prior : List Probe)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hcovered : PendingCoveredBy prior context)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))) :
    PendingCoveredBy (prior ++ canonicalQueryCandidates parameter input context) result.context := by
  have hprior : PendingCoveredBy (prior ++ canonicalQueryCandidates parameter input context) context :=
    hcovered.mono_candidates (List.sublist_append_left _ _)
  cases input with
  | inl query =>
      cases query with
      | inl n =>
          exact pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table result hprior
            (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe _)
              (splitUniformImpl_probeFree n cache)) hresult
      | inr input =>
          change some result ∈ support (runResolvedFromTable context fuel table
            ((probingHashQuery parameter input).run cache)) at hresult
          rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
          apply pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table result hprior _ hresult
          apply probingHashQueryAfterPlan_probeBound
          intro candidate hcandidate
          apply List.mem_append_right
          simp [canonicalQueryCandidates, hcandidate]
  | inr message =>
      exact pendingCoveredBy_of_mem_runResolvedFromTable _ _ context fuel table result hprior
        (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe _)
          (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache)) hresult

set_option maxRecDepth 100000 in
theorem pendingCoveredBy_of_mem_nativeQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (prior : List Probe) (hcovered : PendingCoveredBy prior context)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (∀ ordinal entry, result.2[ordinal]? = some entry →
      PendingCoveredBy (prior ++ canonicalTraceCandidates parameter (result.2.take ordinal)) entry.context) ∧
    (∀ terminal, result.1 = some terminal →
      PendingCoveredBy (prior ++ canonicalTraceCandidates parameter result.2) terminal.context) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache prior result with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hrun
      split_ifs at hrun <;> simp only [mem_support_pure_iff] at hrun <;> subst result
      · constructor
        · intro ordinal entry hentry
          simp at hentry
        · intro terminal hterminal
          simp only [Option.some.injEq] at hterminal
          subst terminal
          simpa [canonicalTraceCandidates] using hcovered
      · simp
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at hrun
      split_ifs at hrun with hcomplete
      · rw [mem_support_bind_iff] at hrun
        obtain ⟨stepOption, hstep, hrun⟩ := hrun
        cases stepOption with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at hrun
            subst result
            constructor
            · intro ordinal entry hentry
              cases ordinal with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                  subst entry
                  simpa [canonicalTraceCandidates] using hcovered
              | succ ordinal => simp at hentry
            · simp
        | some step =>
            rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff] at hpure
            subst result
            have hstepCovered := pendingCoveredBy_of_mem_nativeChronologicalQuery parameter root ftsSecret
              input context fuel table cache prior step hcovered hstep
            have htailCovered := ih step.value.1 step.context step.remaining step.table step.value.2
              (prior ++ canonicalQueryCandidates parameter input context) hstepCovered tail htail
            constructor
            · intro ordinal entry hentry
              cases ordinal with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                  subst entry
                  simpa [canonicalTraceCandidates] using hcovered
              | succ ordinal =>
                  simp only [List.getElem?_cons_succ] at hentry
                  simpa [canonicalTraceCandidates, List.append_assoc] using htailCovered.1 ordinal entry hentry
            · intro terminal hterminal
              simpa [canonicalTraceCandidates, List.append_assoc] using htailCovered.2 terminal hterminal
      · simp only [mem_support_pure_iff] at hrun
        subst result
        simp

set_option maxRecDepth 100000 in
theorem fuel_le_entry_add_hashCount_of_nativeQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    ∀ entry ∈ result.2, fuel ≤ entry.fuel + canonicalTraceHashCount result.2 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache result with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hrun
      split_ifs at hrun <;> simp only [mem_support_pure_iff] at hrun <;> subst result <;> simp
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at hrun
      split_ifs at hrun with hcomplete
      · rw [mem_support_bind_iff] at hrun
        obtain ⟨step, hstep, hrun⟩ := hrun
        cases step with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at hrun
            subst result
            intro entry hentry
            simp only [List.mem_singleton] at hentry
            subst entry
            exact Nat.le_add_right _ _
        | some step =>
            rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff] at hpure
            subst result
            intro entry hentry
            rcases List.mem_cons.mp hentry with heq | htailEntry
            · subst entry
              exact Nat.le_add_right _ _
            · have htailFuel := ih step.value.1 step.context step.remaining step.table step.value.2 tail htail
                entry htailEntry
              have hstepFuel := fuel_bounds_of_mem_runResolvedFromTable _ context fuel (outerHashQueryCount input) table step
                (maskedChronologicalExpandedAdversaryImpl_probeBound parameter root ftsSecret input cache) hstep
              simp only [canonicalTraceHashCount, List.map_cons, List.sum_cons]
              unfold canonicalTraceHashCount at htailFuel
              omega
      · simp only [mem_support_pure_iff] at hrun
        subst result
        simp

theorem nativeChainTraceAfterRoot_entry_resources
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)) :
    ∀ entry ∈ trace.2, fuel ≤ entry.fuel + canonicalTraceHashCount trace.2 ∧
      entry.context.state.pending.card ≤ canonicalTraceHashCount trace.2 := by
  rw [nativeChainTraceAfterRoot, mem_support_bind_iff] at htrace
  obtain ⟨root, hroot, htrace⟩ := htrace
  cases root with
  | none =>
      simp only [mem_support_pure_iff] at htrace
      subst trace
      simp
  | some root =>
      have hrootFuel := fuel_bounds_of_mem_runResolvedFromTable _ (ensuredInitialContext targets) fuel 0 table root
        (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hroot
      have hrootCovered := pendingCoveredBy_of_mem_runResolvedFromTable [] _ (ensuredInitialContext targets) fuel table root
        (by intro entry hentry; simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hentry)
        (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe [])
          (maskedPublishedTreeRoot_probeFree emptySplitHashCache)) hroot
      have hcovered := pendingCoveredBy_of_mem_nativeQueryTrace parameter root.value.1 ftsSecret (continuation root.value.1)
        root.context root.remaining root.table root.value.2 [] hrootCovered trace htrace
      intro entry hentry
      have hfuel := fuel_le_entry_add_hashCount_of_nativeQueryTrace parameter root.value.1 ftsSecret (continuation root.value.1)
        root.context root.remaining root.table root.value.2 trace htrace entry hentry
      refine ⟨by omega, ?_⟩
      obtain ⟨ordinal, hordinal⟩ := List.mem_iff_getElem?.mp hentry
      have hpending := (hcovered.1 ordinal entry hordinal).card_le
      simp only [List.nil_append] at hpending
      exact hpending.trans ((canonicalTraceCandidates_length_le_hashCount parameter _).trans
        (canonicalTraceHashCount_take_le trace.2 ordinal))

theorem nativeRetainedTraceAfterRoot_entry_safe_of_querySpace
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))) :
    ∀ entry ∈ trace.2, 0 < entry.fuel ∧ entry.context.state.pending.card + 1 < Fintype.card Digest := by
  have hcount := nativeRetainedTraceAfterRoot_hashCount_le targets adversary q hq parameter hparameter table ftsSecret hfts (q + 1) trace htrace
  have hresources := nativeChainTraceAfterRoot_entry_resources targets parameter table ftsSecret (q + 1) _ trace htrace
  intro entry hentry
  have hentry := hresources entry hentry
  constructor <;> omega

theorem nativeRetainedTraceAfterRoot_entry_safe
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))) :
    ∀ entry ∈ trace.2, 0 < entry.fuel ∧ entry.context.state.pending.card + 1 < Fintype.card Digest := by
  exact nativeRetainedTraceAfterRoot_entry_safe_of_querySpace targets adversary q hq
    (by
      have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
      omega) parameter hparameter table ftsSecret hfts trace htrace

theorem canonicalGuessCharge_of_nativeRetainedTraceAfterRoot
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)))
    (entry : CanonicalQuerySelection) (hentry : entry ∈ trace.2) :
    canonicalGuessCharge parameter table entry.input entry.context entry.fuel entry.cache =
      match entry.input with
      | .inl (.inr input) => candidateFailureAllowance table entry.context
          (purePlanProbingHashQuery parameter input entry.context.state).candidate?
      | _ => 0 := by
  have hsafe := nativeRetainedTraceAfterRoot_entry_safe targets adversary q hq hqMax parameter hparameter table ftsSecret hfts trace htrace entry hentry
  simp only [canonicalGuessCharge, if_pos hsafe]
  cases entry.input with
  | inl input => cases input <;> rfl
  | inr message => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
