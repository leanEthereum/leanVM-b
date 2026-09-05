import SphincsSecurity.Proof.OtsProbeFreshGuessRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalGuessCharge (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (_cache : SplitHashCache) : ℝ≥0∞ :=
  if 0 < fuel ∧ context.state.pending.card + 1 < Fintype.card Digest then
    match input with
    | .inl (.inr input) => candidateFailureAllowance table context
        (purePlanProbingHashQuery parameter input context.state).candidate?
    | _ => 0
  else 1

theorem probEvent_canonicalQuery_finished_le_guessCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun verdict => verdict = true |
      canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache >>=
        finishResolvedRunIsNone] ≤
      resolvedContextFailureRisk table context + canonicalGuessCharge parameter table input context fuel cache := by
  classical
  by_cases hsafe : 0 < fuel ∧ context.state.pending.card + 1 < Fintype.card Digest
  · unfold canonicalGuessCharge
    rw [if_pos hsafe]
    by_cases hhash : ∃ hashInput, input = .inl (.inr hashInput)
    · obtain ⟨hashInput, rfl⟩ := hhash
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hsafe.1)
      exact probEvent_canonicalHashQuery_finished_le_initial_add_allowance parameter root table ftsSecret
        hashInput context remaining cache hconsistent hstarts hsafe.2
    · have hcount : outerHashQueryCount input = 0 := by
        cases input with
        | inl query => cases query <;> simp_all [outerHashQueryCount]
        | inr message => rfl
      have hzero : (match input with
          | .inl (.inr hashInput) => candidateFailureAllowance table context
              (purePlanProbingHashQuery parameter hashInput context.state).candidate?
          | _ => (0 : ℝ≥0∞)) = 0 := by
        cases input with
        | inl query => cases query <;> simp_all
        | inr message => rfl
      rw [hzero, add_zero]
      have hbound := maskedChronologicalExpandedAdversaryImpl_probeBound parameter root ftsSecret input cache
      rw [hcount] at hbound
      have hdist := (evalDist_canonicalQuery_finished_eq_raw parameter root table ftsSecret input
        context fuel cache hconsistent hstarts).trans
        (evalDist_runResolvedFinishIsNone_probeFree_of_core _ context fuel table () hbound hconsistent hstarts (by omega))
      have hprob := congrArg (fun distribution : SPMF Bool => distribution true) hdist
      change Pr[= true | _] = Pr[= true | _] at hprob
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
        finishResolvedRunIsNone_metadata_eq context table fuel 0 () ()] at hprob
      exact le_of_eq hprob
  · unfold canonicalGuessCharge
    rw [if_neg hsafe]
    exact probEvent_le_one.trans (le_add_of_nonneg_left bot_le)

noncomputable def resolvedOutcomeFailureRisk : Option (ResolvedRunResult α) → ℝ≥0∞
  | none => 1
  | some result => resolvedContextFailureRisk result.table result.context

theorem probEvent_finished_eq_expected_outcomeRisk
    (computation : ProbComp (Option (ResolvedRunResult α))) :
    Pr[fun verdict => verdict = true | computation >>= finishResolvedRunIsNone] =
      ∑' option, Pr[= option | computation] * resolvedOutcomeFailureRisk option := by
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro option
  cases option with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun, resolvedOutcomeFailureRisk]
  | some result =>
      rw [finishResolvedRunIsNone_metadata_eq result.context result.table result.remaining 0 result.value ()]
      rfl

noncomputable def expectedCanonicalTerminalRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ℝ≥0∞ :=
  ∑' result, Pr[= result | runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] *
    resolvedOutcomeFailureRisk result.1

theorem expectedCanonicalTerminalRisk_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    expectedCanonicalTerminalRisk parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache =
      ∑' option, Pr[= option | canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache] *
        match option with
        | none => 1
        | some result => expectedCanonicalTerminalRisk parameter root ftsSecret (next result.value.1)
            result.context result.remaining result.table result.value.2 := by
  rw [expectedCanonicalTerminalRisk, runCanonicalQueryTrace_query_bind, if_pos hcomplete, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro option
  cases option with
  | none => simp [resolvedOutcomeFailureRisk]
  | some result =>
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem expectedCanonicalTerminalRisk_le_initial_add_guessCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedCanonicalTerminalRisk parameter root ftsSecret computation context fuel table cache ≤
      resolvedContextFailureRisk table context + expectedCanonicalQueryCharge parameter root ftsSecret
        (canonicalGuessCharge parameter table) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context
      · simp [expectedCanonicalTerminalRisk, runCanonicalQueryTrace, expectedCanonicalQueryCharge,
          resolvedOutcomeFailureRisk, hcomplete]
      · simp [expectedCanonicalTerminalRisk, runCanonicalQueryTrace, expectedCanonicalQueryCharge,
          resolvedOutcomeFailureRisk, hcomplete, resolvedContextFailureRisk_of_not_completable table context hcomplete]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [expectedCanonicalTerminalRisk_query_bind parameter root ftsSecret input next context fuel table cache hcomplete]
        let queryRun := canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
        let tailCharge := fun option : Option (ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache)) =>
          match option with
          | none => (0 : ℝ≥0∞)
          | some result => expectedCanonicalQueryCharge parameter root ftsSecret (canonicalGuessCharge parameter table)
              (next result.value.1) result.context result.remaining result.table result.value.2
        have hstep := probEvent_canonicalQuery_finished_le_guessCharge parameter root table ftsSecret input
          context fuel cache hconsistent hstarts
        rw [probEvent_finished_eq_expected_outcomeRisk] at hstep
        calc
          _ ≤ ∑' option, Pr[= option | queryRun] * (resolvedOutcomeFailureRisk option + tailCharge option) := by
            apply ENNReal.tsum_le_tsum
            intro option
            by_cases hoption : option ∈ support queryRun
            · cases option with
              | none => simp [queryRun, resolvedOutcomeFailureRisk, tailCharge]
              | some result =>
                  have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret
                    input context fuel cache result hconsistent hstarts hoption
                  simp only [resolvedOutcomeFailureRisk, tailCharge, hcore.1]
                  exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.value.2
                    hcore.2.1 hcore.2.2)
            · have hzero := probOutput_eq_zero_of_not_mem_support hoption
              change Pr[= option | queryRun] * _ ≤ _
              simp only [hzero, zero_mul, le_refl]
          _ = (∑' option, Pr[= option | queryRun] * resolvedOutcomeFailureRisk option) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
          _ ≤ (resolvedContextFailureRisk table context + canonicalGuessCharge parameter table input context fuel cache) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := add_le_add hstep le_rfl
          _ = _ := by
            rw [expectedCanonicalQueryCharge_query_bind, if_pos hcomplete]
            exact add_assoc _ _ _
      · rw [expectedCanonicalTerminalRisk, runCanonicalQueryTrace_of_not_completable parameter root ftsSecret _
          context fuel table cache hcomplete, tsum_probOutput_pure_mul,
          expectedCanonicalQueryCharge_eq_zero_of_not_completable parameter root ftsSecret _ _
            context fuel table cache hcomplete,
          resolvedContextFailureRisk_of_not_completable table context hcomplete]
        simp only [resolvedOutcomeFailureRisk, add_zero, le_refl]

theorem probEvent_canonicalTrace_none_le_initial_add_guessCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun result => result.1 = none |
      runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] ≤
      resolvedContextFailureRisk table context + expectedCanonicalQueryCharge parameter root ftsSecret
        (canonicalGuessCharge parameter table) computation context fuel table cache := by
  apply le_trans ?_ (expectedCanonicalTerminalRisk_le_initial_add_guessCharge parameter root table ftsSecret
    computation context fuel cache hconsistent hstarts)
  rw [probEvent_eq_tsum_ite, expectedCanonicalTerminalRisk]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result.1 <;> simp [resolvedOutcomeFailureRisk]

attribute [local irreducible] maskedPublishedTreeRoot

theorem canonicalGuessCharge_of_coupled_retainedTrace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hleft : left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret (q + 1)))
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (ordinal : Nat) (entry : CanonicalQuerySelection) (hentry : left.2[ordinal]? = some entry) :
    canonicalGuessCharge parameter table entry.input entry.context entry.fuel entry.cache =
      match entry.input with
      | .inl (.inr input) => candidateFailureAllowance table entry.context
          (purePlanProbingHashQuery parameter input entry.context.state).candidate?
      | _ => 0 := by
  have hfuel := positive_fuel_of_coupled_canonicalRetainedTrace adversary q hq parameter hparameter table ftsSecret hfts
    left right hleft hright hrelation entry (List.mem_iff_getElem?.mpr ⟨ordinal, hentry⟩)
  have hcard := pending_card_le_of_coupled_canonicalRetainedTrace adversary q hq parameter hparameter table ftsSecret
    hfts (q + 1) left right hleft hright hrelation ordinal entry hentry
  have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
  unfold canonicalGuessCharge
  rw [if_pos ⟨hfuel, by omega⟩]

end SphincsSecurity.Concrete.OtsProbeSimulation
