import SphincsSecurity.Proof.OtsProbeStartHistorySupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem canonical_startHistory_of_mem_canonicalQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcanonical : CanonicalMaterializedValues table context) (prior : List Probe)
    (hprior : UnrevealedChainStartHistoryMisses table context.state prior)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hpositive : ∀ entry ∈ result.2, 0 < entry.fuel) :
    ∀ ordinal entry, result.2[ordinal]? = some entry → CanonicalMaterializedValues table entry.context ∧
      UnrevealedChainStartHistoryMisses table entry.context.state
        (prior ++ canonicalTraceCandidates parameter (result.2.take ordinal)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache prior result with
  | pure value =>
      simp only [runCanonicalQueryTrace, OracleComp.construct_pure] at hrun
      split_ifs at hrun <;> simp only [mem_support_pure_iff] at hrun <;> subst result <;> simp
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind] at hrun
      split_ifs at hrun with hcomplete
      · rw [mem_support_bind_iff] at hrun
        obtain ⟨stepOption, hstep, hrun⟩ := hrun
        cases stepOption with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at hrun
            subst result
            intro ordinal entry hentry
            cases ordinal with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                subst entry
                simpa [canonicalTraceCandidates] using And.intro hcanonical hprior
            | succ ordinal => simp at hentry
        | some step =>
            rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff] at hpure
            subst result
            intro ordinal entry hentry
            cases ordinal with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
                subst entry
                simpa [canonicalTraceCandidates] using And.intro hcanonical hprior
            | succ ordinal =>
                simp only [List.getElem?_cons_succ] at hentry
                have hstepComplete : DeferredCompletable step.table step.context := by
                  by_contra hnot
                  rw [runCanonicalQueryTrace_of_not_completable parameter root ftsSecret _ step.context
                    step.remaining step.table step.value.2 hnot, mem_support_pure_iff] at htail
                  subst tail
                  simp at hentry
                have hfuel : 0 < fuel := hpositive ⟨input, context, fuel, table, cache⟩ (by simp)
                cases fuel with
                | zero => omega
                | succ remaining =>
                    have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret
                      input context (remaining + 1) cache step hconsistent hstarts hstep
                    have hnextCanonical := canonicalMaterializedValues_of_mem_canonicalChronologicalQuery
                      parameter root ftsSecret input context (remaining + 1) table cache step hconsistent hstarts hstep
                    have hnextPrior := unrevealedChainStartHistoryMisses_append_canonicalQuery parameter root table ftsSecret
                      input context remaining cache prior step hconsistent hstarts hprior hstep hstepComplete
                    have htailPositive : ∀ selected ∈ tail.2, 0 < selected.fuel := by
                      intro selected hselected
                      exact hpositive selected (List.mem_cons_of_mem _ hselected)
                    rw [hcore.1] at htail
                    have htailHistory := ih step.value.1 step.context step.remaining table step.value.2
                      hcore.2.1 hcore.2.2 hnextCanonical (prior ++ canonicalQueryCandidates parameter input context)
                      hnextPrior tail htail htailPositive ordinal entry hentry
                    simpa [canonicalTraceCandidates, List.append_assoc] using htailHistory
      · simp only [mem_support_pure_iff] at hrun
        subst result
        simp

theorem canonical_startHistory_of_mem_canonicalRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (hpositive : ∀ entry ∈ result.2, 0 < entry.fuel) :
    ∀ ordinal entry, result.2[ordinal]? = some entry → CanonicalMaterializedValues table entry.context ∧
      UnrevealedChainStartHistoryMisses table entry.context.state
        (canonicalTraceCandidates parameter (result.2.take ordinal)) := by
  rw [canonicalRetainedQueryTrace, mem_support_bind_iff] at hrun
  obtain ⟨rootOption, hroot, hrun⟩ := hrun
  cases rootOption with
  | none =>
      simp only [mem_support_pure_iff] at hrun
      subst result
      simp
  | some root =>
      rw [mem_support_bind_iff] at hrun
      obtain ⟨rest, hrest, hpure⟩ := hrun
      simp only [mem_support_pure_iff] at hpure
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache)
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel table root (by intro coordinate output hvalue; simp [LazyRevealProbe.State.empty] at hvalue)
        (by intro index output hvalue; simp [LazyRevealProbe.State.empty] at hvalue) hroot
      have hcanonical := canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel root hroot
      rw [hcore.1] at hrest
      have hhistory := canonical_startHistory_of_mem_canonicalQueryTrace parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining table root.value.2 hcore.2.1 hcore.2.2 hcanonical []
        (by simp [UnrevealedChainStartHistoryMisses]) rest hrest hpositive
      simpa only [List.nil_append] using hhistory

theorem UnrevealedChainStartHistoryMisses.not_historyHit_of_canonical
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext} {history : List Probe}
    (hmiss : UnrevealedChainStartHistoryMisses table context.state history)
    (hcanonical : CanonicalMaterializedValues table context) : ¬ChainStartHistoryHit context history table := by
  rintro ⟨candidate, hcandidate, hmissing, hhit⟩
  rcases candidate with ⟨coordinate, digest⟩
  cases coordinate with
  | position position => simp [ChainStartEntryHit] at hhit
  | chainStart lay tree leafIdx chainIdx =>
      apply hmiss ⟨.chainStart lay tree leafIdx chainIdx, digest⟩ hcandidate _ hhit
      intro hrevealed
      rw [hcanonical] at hmissing
      simp [publicMaterializedValues, hrevealed, resolvedCompletionValue] at hmissing

theorem no_chainStartHistoryHit_of_coupled_canonicalRetainedTrace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hleft : left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret (q + 1)))
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (ordinal : Nat) (entry : CanonicalQuerySelection) (hentry : left.2[ordinal]? = some entry) :
    ¬ChainStartHistoryHit entry.context (canonicalTraceCandidates parameter (left.2.take ordinal)) table := by
  have hpositive := positive_fuel_of_coupled_canonicalRetainedTrace adversary q hq parameter hparameter table ftsSecret
    hfts left right hleft hright hrelation
  have hhistory := canonical_startHistory_of_mem_canonicalRetainedQueryTrace adversary parameter table ftsSecret
    (q + 1) left hleft hpositive ordinal entry hentry
  exact hhistory.2.not_historyHit_of_canonical hhistory.1

theorem completedStartTable_self_of_canonical
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hcanonical : CanonicalMaterializedValues table context) : completedStartTable context.state table = table := by
  funext index
  unfold completedStartTable
  rw [hcanonical]
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  simp only [publicMaterializedValues, OtsSecretIndex.coordinate, resolvedCompletionValue]
  split_ifs <;> rfl

theorem evalDist_resolveDeferredReveal_eq_recompletion_of_historyMisses
    (table base : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (history : List Probe) (hcovered : PendingCoveredBy history context)
    (hcanonical : CanonicalMaterializedValues table context)
    (hmiss : UnrevealedChainStartHistoryMisses table context.state history)
    (hbase : ¬ChainStartHistoryHit context history base) :
    evalDist (resolveDeferredReveal table position context) =
      evalDist (resolveDeferredReveal (completedStartTable context.state base) position context) := by
  have heq := evalDist_resolveDeferredReveal_eq_of_history_clean table base position context history hcovered
    (hmiss.not_historyHit_of_canonical hcanonical) hbase
  rwa [completedStartTable_self_of_canonical table context hcanonical] at heq

theorem probEvent_no_chainStartHistoryHit_coupled_prefix_ge_three_quarters
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (ordinal : Nat) (context : DeferredContext) :
    (3 / 4 : ℝ≥0∞) ≤ Pr[fun base =>
      ¬ChainStartHistoryHit context (canonicalTraceCandidates parameter (left.2.take ordinal)) base | sampleOtsHashTable] := by
  apply probEvent_no_chainStartHistoryHit_ge_three_quarters
  exact (canonicalTraceCandidates_length_le_hashCount parameter _).trans
    ((canonicalTraceHashCount_take_le _ _).trans (hrelation.hashCount_le.trans
      ((prehitRetainedTraceHashCount_le adversary q hq parameter hparameter table ftsSecret hfts right hright).trans hqMax)))

end SphincsSecurity.Concrete.OtsProbeSimulation
