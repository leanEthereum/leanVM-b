import SphincsSecurity.Proof.OtsProbeNativeRootHitProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeQueryRejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (entry : CanonicalQuerySelection) : ℝ≥0∞ :=
  Pr[ResolvedQueryRejected | runResolvedFromTable entry.context entry.fuel entry.table
    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret entry.input).run entry.cache)]

noncomputable def nativeTraceRejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (history : List CanonicalQuerySelection) : ℝ≥0∞ :=
  (history.map (nativeQueryRejectionRisk parameter root ftsSecret)).sum

private theorem expected_const_add (computation : ProbComp α) (constant : ℝ≥0∞) (cost : α → ℝ≥0∞) :
    (∑' result, Pr[= result | computation] * (constant + cost result)) =
      constant + ∑' result, Pr[= result | computation] * cost result := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

theorem expectedNativeTraceRejectionRisk_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    (∑' result, Pr[= result | runNativeQueryTrace parameter root ftsSecret
        (OracleSpec.query input >>= next) context fuel table cache] *
      nativeTraceRejectionRisk parameter root ftsSecret result.2) =
      nativeQueryRejectionRisk parameter root ftsSecret ⟨input, context, fuel, table, cache⟩ +
        ∑' step, Pr[= step | runResolvedFromTable context fuel table
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)] *
          match step with
          | none => 0
          | some step => ∑' tail, Pr[= tail | runNativeQueryTrace parameter root ftsSecret
              (next step.value.1) step.context step.remaining step.table step.value.2] *
                nativeTraceRejectionRisk parameter root ftsSecret tail.2 := by
  rw [runNativeQueryTrace_query_bind, if_pos hcomplete, tsum_probOutput_bind_mul]
  rw [← expected_const_add]
  apply tsum_congr
  intro step
  congr 1
  cases step with
  | none => simp [nativeTraceRejectionRisk]
  | some step =>
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
        nativeTraceRejectionRisk, List.map_cons, List.sum_cons]
      exact expected_const_add _ _ _

theorem probEvent_nativeTrace_none_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    Pr[fun result => result.1 = none | runNativeQueryTrace parameter root ftsSecret
      (OracleSpec.query input >>= next) context fuel table cache] =
      ∑' step, Pr[= step | runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)] *
        match step with
        | none => 1
        | some step => Pr[fun result => result.1 = none | runNativeQueryTrace parameter root ftsSecret
            (next step.value.1) step.context step.remaining step.table step.value.2] := by
  rw [runNativeQueryTrace_query_bind, if_pos hcomplete, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro step
  congr 1
  cases step with
  | none => simp
  | some step =>
      simpa only [Function.comp_def] using probEvent_bind_pure_comp
        (mx := runNativeQueryTrace parameter root ftsSecret (next step.value.1)
          step.context step.remaining step.table step.value.2)
        (f := fun result => (result.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: result.2))
        (fun result => result.1 = none)

set_option maxRecDepth 100000 in
theorem probEvent_nativeTrace_none_eq_expected_rejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    Pr[fun result => result.1 = none | runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] =
      ∑' result, Pr[= result | runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] *
        nativeTraceRejectionRisk parameter root ftsSecret result.2 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [runNativeQueryTrace, hcomplete, nativeTraceRejectionRisk]
  | query_bind input next ih =>
      rw [probEvent_nativeTrace_none_query_bind parameter root ftsSecret input next context fuel table cache hcomplete,
        expectedNativeTraceRejectionRisk_query_bind parameter root ftsSecret input next context fuel table cache hcomplete,
        nativeQueryRejectionRisk, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
      apply tsum_congr
      intro step
      cases step with
      | none => simp [ResolvedQueryRejected]
      | some step =>
          dsimp only
          by_cases hnext : DeferredCompletable step.table step.context
          · simp only [ResolvedQueryRejected, hnext, not_true_eq_false, ↓reduceIte, zero_add]
            rw [ih step.value.1 step.context step.remaining step.table step.value.2 hnext]
          · rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret _
              step.context step.remaining step.table step.value.2 hnext]
            simp [ResolvedQueryRejected, hnext, nativeTraceRejectionRisk]

attribute [local irreducible] maskedPublishedTreeRoot

end SphincsSecurity.Concrete.OtsProbeSimulation
