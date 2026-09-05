import SphincsSecurity.Proof.OtsProbeCanonicalStopping

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ResolvedQueryRejected (result : Option (ResolvedRunResult α)) : Prop :=
  match result with
  | none => True
  | some result => ¬DeferredCompletable result.table result.context

noncomputable def canonicalQueryRejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (entry : CanonicalQuerySelection) : ℝ≥0∞ :=
  Pr[ResolvedQueryRejected | canonicalChronologicalAdversaryImpl parameter root entry.table ftsSecret
    entry.input entry.context entry.fuel entry.table entry.cache]

noncomputable def canonicalTraceRejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (history : List CanonicalQuerySelection) : ℝ≥0∞ :=
  (history.map (canonicalQueryRejectionRisk parameter root ftsSecret)).sum

private theorem expected_const_add (computation : ProbComp α) (constant : ℝ≥0∞) (cost : α → ℝ≥0∞) :
    (∑' result, Pr[= result | computation] * (constant + cost result)) =
      constant + ∑' result, Pr[= result | computation] * cost result := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

theorem expectedCanonicalTraceRejectionRisk_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    (∑' result, Pr[= result | runCanonicalQueryTrace parameter root ftsSecret
        (OracleSpec.query input >>= next) context fuel table cache] *
      canonicalTraceRejectionRisk parameter root ftsSecret result.2) =
      canonicalQueryRejectionRisk parameter root ftsSecret ⟨input, context, fuel, table, cache⟩ +
        ∑' step, Pr[= step | canonicalChronologicalAdversaryImpl parameter root table ftsSecret
          input context fuel table cache] *
          match step with
          | none => 0
          | some step => ∑' tail, Pr[= tail | runCanonicalQueryTrace parameter root ftsSecret
              (next step.value.1) step.context step.remaining step.table step.value.2] *
                canonicalTraceRejectionRisk parameter root ftsSecret tail.2 := by
  rw [runCanonicalQueryTrace_query_bind, if_pos hcomplete, tsum_probOutput_bind_mul]
  rw [← expected_const_add]
  apply tsum_congr
  intro step
  congr 1
  cases step with
  | none => simp [canonicalTraceRejectionRisk]
  | some step =>
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
        canonicalTraceRejectionRisk, List.map_cons, List.sum_cons]
      exact expected_const_add _ _ _

theorem probEvent_canonicalTrace_none_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    Pr[fun result => result.1 = none | runCanonicalQueryTrace parameter root ftsSecret
      (OracleSpec.query input >>= next) context fuel table cache] =
      ∑' step, Pr[= step | canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache] *
        match step with
        | none => 1
        | some step => Pr[fun result => result.1 = none | runCanonicalQueryTrace parameter root ftsSecret
            (next step.value.1) step.context step.remaining step.table step.value.2] := by
  rw [runCanonicalQueryTrace_query_bind, if_pos hcomplete, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro step
  congr 1
  cases step with
  | none => simp
  | some step =>
      simpa only [Function.comp_def] using probEvent_bind_pure_comp
        (mx := runCanonicalQueryTrace parameter root ftsSecret (next step.value.1)
          step.context step.remaining step.table step.value.2)
        (f := fun result => (result.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: result.2))
        (fun result => result.1 = none)

set_option maxRecDepth 100000 in
theorem probEvent_canonicalTrace_none_eq_expected_rejectionRisk
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcomplete : DeferredCompletable table context) :
    Pr[fun result => result.1 = none | runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] =
      ∑' result, Pr[= result | runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] *
        canonicalTraceRejectionRisk parameter root ftsSecret result.2 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [runCanonicalQueryTrace, hcomplete, canonicalTraceRejectionRisk]
  | query_bind input next ih =>
      rw [probEvent_canonicalTrace_none_query_bind parameter root ftsSecret input next context fuel table cache hcomplete,
        expectedCanonicalTraceRejectionRisk_query_bind parameter root ftsSecret input next context fuel table cache hcomplete,
        canonicalQueryRejectionRisk, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
      apply tsum_congr
      intro step
      cases step with
      | none => simp [ResolvedQueryRejected]
      | some step =>
          dsimp only
          by_cases hnext : DeferredCompletable step.table step.context
          · simp only [ResolvedQueryRejected, hnext, not_true_eq_false, ↓reduceIte, zero_add]
            rw [ih step.value.1 step.context step.remaining step.table step.value.2 hnext]
          · rw [runCanonicalQueryTrace_of_not_completable parameter root ftsSecret _
              step.context step.remaining step.table step.value.2 hnext]
            simp [ResolvedQueryRejected, hnext, canonicalTraceRejectionRisk]

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def canonicalRetainedRejectionRisk
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' root, Pr[= root | runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match root with
    | none => 0
    | some root => ∑' result, Pr[= result | runCanonicalQueryTrace parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining root.table root.value.2] *
          canonicalTraceRejectionRisk parameter root.value.1 ftsSecret result.2

theorem probEvent_canonicalRetainedTrace_none_eq_rejectionRisk
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun result => result.1 = none | canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel] =
      canonicalRetainedRejectionRisk adversary parameter table ftsSecret fuel := by
  unfold canonicalRetainedQueryTrace canonicalRetainedRejectionRisk
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro option
  by_cases hroot : option ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases option with
    | none => exact False.elim (none_not_mem_resolved_maskedPublishedTreeRoot table fuel hroot)
    | some root =>
        dsimp only
        congr 1
        have hprojection := probEvent_bind_pure_comp
          (runCanonicalQueryTrace parameter root.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
            root.context root.remaining root.table root.value.2)
          (fun rest => (rest.1.map (retainedResultWithRoot root.value.1), rest.2))
          (fun result => result.1 = none)
        have heq := probEvent_canonicalTrace_none_eq_expected_rejectionRisk parameter root.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
          root.context root.remaining root.table root.value.2
          (deferredCompletable_of_mem_resolved_maskedPublishedTreeRoot parameter table fuel root hroot)
        calc
          _ = Pr[fun result => result.1 = none | runCanonicalQueryTrace parameter root.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
              root.context root.remaining root.table root.value.2] := by
            simpa only [Function.comp_def, Option.map_eq_none_iff] using hprojection
          _ = _ := heq
  · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]

open OracleComp.ProgramLogic.Relational in
theorem probEvent_retainedVerifyProbe_le_rejectionRisk
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      canonicalRetainedRejectionRisk adversary parameter table ftsSecret fuel := by
  rw [← prehitRetainedQueryTrace_cache_projection, probEvent_map,
    ← probEvent_canonicalRetainedTrace_none_eq_rejectionRisk]
  exact probEvent_le_of_relTriple
    (relTriple_symm (relTriple_canonicalRetainedQueryTrace_prehit_witness adversary parameter table ftsSecret fuel))
    (fun _ _ hrelation hwitness => hrelation.2 hwitness)

end SphincsSecurity.Concrete.OtsProbeSimulation
