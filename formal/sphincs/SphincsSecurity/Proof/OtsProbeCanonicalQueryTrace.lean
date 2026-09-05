import SphincsSecurity.Proof.OtsProbeCanonicalSelectionSampled

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable

noncomputable def runCanonicalQueryTrace
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :=
  OracleComp.construct
    (fun value context fuel table cache =>
      if DeferredCompletable table context then pure (some ⟨context, fuel, (value, cache), table⟩, [])
      else pure (none, []))
    (fun input _ next context fuel table cache =>
      if DeferredCompletable table context then do
        let result ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
        let tail ← match result with
          | none => pure (none, [])
          | some result => next result.value.1 result.context result.remaining result.table result.value.2
        pure (tail.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: tail.2)
      else pure (none, [])) computation

theorem runCanonicalQueryTrace_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runCanonicalQueryTrace parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache =
      if DeferredCompletable table context then do
        let result ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
        let tail ← match result with
          | none => pure (none, [])
          | some result =>
              runCanonicalQueryTrace parameter root ftsSecret (next result.value.1)
                result.context result.remaining result.table result.value.2
        pure (tail.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: tail.2)
      else pure (none, []) := rfl

theorem runCanonicalQueryTrace_of_not_completable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnot : ¬DeferredCompletable table context) :
    runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache = pure (none, []) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [runCanonicalQueryTrace, OracleComp.construct_pure, hnot, ↓reduceIte]
  | query_bind input next _ => rw [runCanonicalQueryTrace_query_bind, if_neg hnot]

set_option maxRecDepth 100000 in
theorem runCanonicalQueryTrace_selection_projection
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (ordinal : Nat) :
    evalDist ((fun result => result.2[ordinal]?) <$>
      runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache) =
      evalDist (canonicalQuerySelection parameter root ftsSecret computation ordinal context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache ordinal with
  | pure value =>
      simp only [runCanonicalQueryTrace, OracleComp.construct_pure, canonicalQuerySelection_pure]
      split_ifs <;> simp
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind, canonicalQuerySelection_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [hcomplete, ↓reduceIte, map_bind]
        cases ordinal with
        | zero =>
            calc
              _ = evalDist (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
                  input context fuel table cache >>= fun _ =>
                    pure (some (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection))) := by
                apply evalDist_bind_congr_left
                intro result
                cases result with
                | none => simp
                | some result =>
                    simp only [map_bind, map_pure, List.getElem?_cons_zero]
                    exact evalDist_bind_const_neverFails _ (by simp) _
              _ = _ := evalDist_bind_const_neverFails _ (by simp) _
        | succ ordinal =>
            apply evalDist_bind_congr_left
            intro result
            cases result with
            | none => simp
            | some result =>
                simp only [map_bind, map_pure, List.getElem?_cons_succ]
                simpa only [map_eq_bind_pure_comp, Function.comp_def] using
                  ih result.value.1 result.context result.remaining result.table result.value.2 ordinal
      · simp [hcomplete]

noncomputable def canonicalTraceCharge
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (history : List CanonicalQuerySelection) : ℝ≥0∞ :=
  (history.map fun selection => CanonicalQuerySelection.charge charge (some selection)).sum

theorem canonicalTraceCharge_eq_tsum_selection
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (history : List CanonicalQuerySelection) :
    canonicalTraceCharge charge history = ∑' ordinal : Nat, CanonicalQuerySelection.charge charge (history[ordinal]?) := by
  induction history with
  | nil => simp [canonicalTraceCharge, CanonicalQuerySelection.charge]
  | cons head tail ih =>
      rw [tsum_eq_zero_add' ENNReal.summable]
      simpa only [canonicalTraceCharge, List.map_cons, List.sum_cons, List.getElem?_cons_zero,
        List.getElem?_cons_succ] using congrArg (CanonicalQuerySelection.charge charge (some head) + ·) ih

theorem expectedCanonicalTraceCharge_eq
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' result, Pr[= result | runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] *
      canonicalTraceCharge charge result.2) =
      expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache := by
  simp_rw [canonicalTraceCharge_eq_tsum_selection, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ← tsum_canonicalQuerySelection_charge]
  apply tsum_congr
  intro ordinal
  calc
    _ = ∑' selection, Pr[= selection | (fun result => result.2[ordinal]?) <$>
        runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] *
          CanonicalQuerySelection.charge charge selection := (tsum_probOutput_map_mul _ _ _).symm
    _ = _ := tsum_congr fun selection => congrArg (· * CanonicalQuerySelection.charge charge selection)
      (_root_.OracleComp.probOutput_congr rfl (runCanonicalQueryTrace_selection_projection
        parameter root ftsSecret computation context fuel table cache ordinal))


set_option maxRecDepth 100000 in
theorem expectedCanonicalJointTraceCharge_le_actualReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    (∑' result, Pr[= result | runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache] *
      canonicalTraceCharge (canonicalJointOuterCharge parameter) result.2) ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve secretKey)
        (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache := by
  dsimp only
  rw [expectedCanonicalTraceCharge_eq]
  exact expectedCanonicalJointCharge_le_actualReserve parameter root table ftsSecret computation
    context fuel cache actualCache hinvariant hvisible hpublished hcomputed

end SphincsSecurity.Concrete.OtsProbeSimulation
