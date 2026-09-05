import SphincsSecurity.Proof.OtsProbeHashCutRisk
import SphincsSecurity.Proof.OtsProbeCanonicalCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalHashOrdinalCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ _ => 0)
    (fun input _ next ordinal context fuel table cache =>
      if DeferredCompletable table context then
        if IsOuterHash input ∧ ordinal = 0 then charge input context fuel cache
        else ∑' result, Pr[= result | canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
          match result with
          | none => 0
          | some result =>
              next result.value.1 (if IsOuterHash input then ordinal - 1 else ordinal)
                result.context result.remaining result.table result.value.2
      else 0) computation

theorem canonicalHashOrdinalCharge_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    canonicalHashOrdinalCharge parameter root ftsSecret charge (OracleSpec.query input >>= next) ordinal context fuel table cache =
      (if DeferredCompletable table context then
        if IsOuterHash input ∧ ordinal = 0 then charge input context fuel cache
        else ∑' result, Pr[= result | canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
          match result with
          | none => 0
          | some result =>
              canonicalHashOrdinalCharge parameter root ftsSecret charge (next result.value.1)
                (if IsOuterHash input then ordinal - 1 else ordinal) result.context result.remaining result.table result.value.2
      else 0) := by
  rfl

theorem sum_canonicalHashOrdinalCharge_le_expected
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑ ordinal ∈ Finset.range q, canonicalHashOrdinalCharge parameter root ftsSecret charge computation ordinal context fuel table cache) ≤
      expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table cache with
  | pure value => simp [canonicalHashOrdinalCharge, expectedCanonicalQueryCharge]
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have htail (n : Nat) :
            (∑ ordinal ∈ Finset.range n, ∑' result,
              Pr[= result | canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
                match result with
                | none => 0
                | some result =>
                    canonicalHashOrdinalCharge parameter root ftsSecret charge (next result.value.1)
                      ordinal result.context result.remaining result.table result.value.2) ≤
            ∑' result, Pr[= result | canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
              match result with
              | none => 0
              | some result =>
                  expectedCanonicalQueryCharge parameter root ftsSecret charge (next result.value.1)
                    result.context result.remaining result.table result.value.2 := by
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          apply ENNReal.tsum_le_tsum
          intro option
          cases option with
          | none => simp
          | some result =>
              simp only [← Finset.mul_sum]
              exact mul_le_mul' le_rfl (ih result.value.1 n result.context result.remaining result.table result.value.2)
        by_cases hhash : IsOuterHash input
        · cases q with
          | zero => simp
          | succ q =>
              rw [Finset.sum_range_succ']
              simp only [canonicalHashOrdinalCharge_query_bind, if_pos hcomplete, hhash, Nat.add_eq_zero_iff,
                Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel, and_self, if_true]
              exact (add_le_add (htail q) (le_refl (charge input context fuel cache))).trans_eq (add_comm _ _)
        · simp only [canonicalHashOrdinalCharge_query_bind, if_pos hcomplete, hhash, false_and, if_false]
          exact (htail q).trans (le_add_of_nonneg_left bot_le)
      · simp [canonicalHashOrdinalCharge_query_bind, hcomplete]

noncomputable def cutQueryCharge
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) :
    Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) → ENNReal
  | none => 0
  | some result =>
      match result.value.1.input? with
      | none => 0
      | some input => charge input result.context result.remaining result.value.2

theorem runSynchronizedCanonical_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (OracleSpec.query input >>= next) context fuel table cache =
      (if DeferredCompletable table context then do
        let step ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
        match step with
        | none => pure none
        | some result =>
            runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
              (next result.value.1) result.context result.remaining result.table result.value.2
      else pure none) := by
  rw [runSynchronizedResolved, OracleComp.construct_query_bind]
  split_ifs
  · apply bind_congr
    intro option
    cases option <;> rfl
  · rfl

theorem expected_hashCut_eq_canonicalHashOrdinalCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    (∑' result, Pr[= result | runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (outerHashQueryCutAt computation ordinal) context fuel table cache] * cutQueryCharge charge result) =
      canonicalHashOrdinalCharge parameter root ftsSecret charge computation ordinal context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [outerHashQueryCutAt, runSynchronizedResolved, hcomplete, canonicalHashOrdinalCharge, cutQueryCharge, OuterQueryCut.input?]
  | query_bind input next ih =>
      rw [canonicalHashOrdinalCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have htail (n : Nat) :
            (∑' final, Pr[= final | (do
              let step ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
              match step with
              | none => pure none
              | some result =>
                  runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                    (outerHashQueryCutAt (next result.value.1) n) result.context result.remaining result.table result.value.2)] *
                cutQueryCharge charge final) =
            ∑' result, Pr[= result | canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache] *
              match result with
              | none => 0
              | some result =>
                  canonicalHashOrdinalCharge parameter root ftsSecret charge (next result.value.1) n
                    result.context result.remaining result.table result.value.2 := by
          rw [tsum_probOutput_bind_mul]
          apply tsum_congr
          intro option
          by_cases hsupport : option ∈ support
              (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)
          · cases option with
            | none => simp [cutQueryCharge]
            | some result =>
                have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret input
                  context fuel cache result hconsistent hstarts hsupport
                dsimp only
                rw [hcore.1]
                rw [ih result.value.1 n result.context result.remaining table result.value.2 hcore.2.1 hcore.2.2]
          · simp [probOutput_eq_zero_of_not_mem_support hsupport]
        rw [outerHashQueryCutAt_query_bind]
        by_cases hhash : IsOuterHash input
        · rw [if_pos hhash]
          cases ordinal with
          | zero => simp [runSynchronizedResolved_pure _ _ _ _ _ _ hcomplete, cutQueryCharge, OuterQueryCut.input?, hhash]
          | succ ordinal =>
              rw [runSynchronizedCanonical_query_bind, if_pos hcomplete]
              simpa only [hhash, true_and, Nat.succ_ne_zero, if_false, if_true, Nat.add_sub_cancel] using htail ordinal
        · rw [if_neg hhash, runSynchronizedCanonical_query_bind, if_pos hcomplete]
          simpa only [hhash, false_and, if_false] using htail ordinal
      · rw [if_neg hcomplete, runSynchronizedResolved_of_not_completable _ _ context fuel table cache hcomplete]
        simp [cutQueryCharge]

theorem sum_expected_hashCut_le_canonicalQueryCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    (∑ ordinal ∈ Finset.range q, ∑' result,
      Pr[= result | runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        (outerHashQueryCutAt computation ordinal) context fuel table cache] * cutQueryCharge charge result) ≤
      expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache := by
  simp_rw [expected_hashCut_eq_canonicalHashOrdinalCharge parameter root ftsSecret charge computation _ context fuel table cache
    hconsistent hstarts]
  exact sum_canonicalHashOrdinalCharge_le_expected parameter root ftsSecret charge computation q context fuel table cache

noncomputable def sampledCanonicalAccumulatedCharge
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) : ENNReal :=
  ∑' table, Pr[= table | sampleOtsHashTable] *
    ∑' option, Pr[= option | runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
      match option with
      | none => 0
      | some result =>
          expectedCanonicalQueryCharge parameter result.value.1 ftsSecret charge (continuation result.value.1)
            result.context result.remaining result.table result.value.2

theorem sum_expected_sampledHashCut_le_accumulatedCharge
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) :
    (∑ ordinal ∈ Finset.range q, ∑' result,
      Pr[= result | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] * cutQueryCharge charge result) ≤
      sampledCanonicalAccumulatedCharge parameter ftsSecret fuel continuation charge := by
  have hcost (ordinal : Nat) :
      (∑' result, Pr[= result | sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal] * cutQueryCharge charge result) =
      ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' option, Pr[= option | runResolvedFromTable
          { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
          match option with
          | none => 0
          | some result =>
              ∑' final, Pr[= final | runSynchronizedResolved
                (canonicalChronologicalAdversaryImpl parameter result.value.1 table ftsSecret)
                (outerHashQueryCutAt (continuation result.value.1) ordinal) result.context result.remaining table result.value.2] *
                cutQueryCharge charge final := by
    have hdist := evalDist_sampledCanonicalHashCut_eq_original parameter ftsSecret fuel continuation ordinal
    simp_rw [_root_.OracleComp.probOutput_congr rfl hdist]
    simp only [tsum_probOutput_bind_mul]
    apply tsum_congr
    intro table
    congr 1
    apply tsum_congr
    intro option
    cases option <;> simp [cutQueryCharge]
  simp_rw [hcost]
  rw [sampledCanonicalAccumulatedCharge, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [← Finset.mul_sum]
  apply mul_le_mul' le_rfl _
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro option
  rw [← Finset.mul_sum]
  by_cases hsupport : option ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases option with
    | none => simp
    | some result =>
        apply mul_le_mul' le_rfl _
        have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hsupport
        dsimp only
        rw [hcore.1]
        exact sum_expected_hashCut_le_canonicalQueryCharge parameter result.value.1 ftsSecret charge
          (continuation result.value.1) q result.context result.remaining table result.value.2 hcore.2.1 hcore.2.2
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

noncomputable def unresolvedStartOuterCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal
  | .inl (.inr input), context, _, _ =>
      unresolvedStartCandidateCharge context (purePlanProbingHashQuery parameter input context.state).candidate?
  | _, _, _, _ => 0

theorem cutQueryCharge_unresolvedStart
    (parameter : PublicParameter) (result : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache))) :
    cutQueryCharge (unresolvedStartOuterCharge parameter) result = historyUnresolvedStartCharge (hashCutCandidate parameter) result := by
  cases result with
  | none => rfl
  | some result =>
      cases hcut : result.value.1 with
      | done value => simp [cutQueryCharge, historyUnresolvedStartCharge, hashCutCandidate, hcut, OuterQueryCut.input?, unresolvedStartCandidateCharge]
      | query input next =>
          cases input with
          | inl query =>
              cases query <;> simp [cutQueryCharge, historyUnresolvedStartCharge, hashCutCandidate, hcut, OuterQueryCut.input?,
                unresolvedStartOuterCharge, unresolvedStartCandidateCharge]
          | inr message =>
              simp [cutQueryCharge, historyUnresolvedStartCharge, hashCutCandidate, hcut, OuterQueryCut.input?,
                unresolvedStartOuterCharge, unresolvedStartCandidateCharge]

theorem sum_hashCut_unresolvedStart_le_accumulatedCharge
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit (hashCutCandidate parameter) |
      sampledCanonicalHashCut parameter ftsSecret fuel continuation ordinal]) ≤
      sampledCanonicalAccumulatedCharge parameter ftsSecret fuel continuation (unresolvedStartOuterCharge parameter) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hcharge := sum_expected_sampledHashCut_le_accumulatedCharge parameter ftsSecret fuel q continuation
    (unresolvedStartOuterCharge parameter)
  simp_rw [cutQueryCharge_unresolvedStart] at hcharge
  exact (sum_sampledCanonicalHashCut_unresolvedStart_le parameter ftsSecret fuel q continuation hq).trans
    (add_le_add (mul_le_mul' hcharge le_rfl) le_rfl)

end SphincsSecurity.Concrete.OtsProbeSimulation
