import SphincsSecurity.Proof.Prelude
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

attribute [local irreducible] maskedPublishedTreeRoot

end SphincsSecurity.Concrete.OtsProbeSimulation
