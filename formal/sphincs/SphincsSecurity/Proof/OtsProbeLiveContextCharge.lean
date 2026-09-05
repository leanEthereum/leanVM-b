import SphincsSecurity.Proof.OtsProbeNativeRootQueryCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedLiveNativeContextCharge
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next context fuel table cache =>
      if DeferredCompletable table context then
        charge input context fuel cache + ∑' result, Pr[= result | runResolvedFromTable context fuel table ((impl input).run cache)] *
          match result with
          | none => 0
          | some result => next result.value.1 result.context result.remaining result.table result.value.2
      else 0) computation

theorem expectedLiveNativeContextCharge_query_bind
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveNativeContextCharge impl charge (OracleSpec.query input >>= next) context fuel table cache =
      (if DeferredCompletable table context then
        charge input context fuel cache + ∑' result, Pr[= result | runResolvedFromTable context fuel table ((impl input).run cache)] *
          match result with
          | none => 0
          | some result => expectedLiveNativeContextCharge impl charge (next result.value.1)
              result.context result.remaining result.table result.value.2
      else 0) := rfl

theorem expectedLiveNativeContextCharge_eq_zero_of_not_completable
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : ¬DeferredCompletable table context) :
    expectedLiveNativeContextCharge impl charge computation context fuel table cache = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [expectedLiveNativeContextCharge_query_bind, if_neg hdoomed]

theorem expectedLiveNativeContextCharge_le_actualOuterCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (actualCharge : QueryCache HashSpec → HashInput → ENNReal)
    (himpl : ∀ input, ReachableResolvedCouples parameter table (impl input)
      (unloggedMappedAdversaryImpl
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey) input))
    (hcharge : ∀ input context fuel cache actualCache,
      ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache →
      DeferredComputationsClosed context →
      charge input context fuel cache ≤ outerHashQueryCharge actualCharge input actualCache)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedLiveNativeContextCharge impl charge computation context fuel table cache ≤
      expectedOuterQueryCharge
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)
        actualCharge computation actualCache := by
  let secretKey : SecretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx =>
    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  change _ ≤ expectedOuterQueryCharge secretKey actualCharge computation actualCache
  induction computation using OracleComp.inductionOn generalizing context fuel cache actualCache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedLiveNativeContextCharge_query_bind, if_pos hinvariant.2.2.2.1, expectedOuterQueryCharge_query_bind]
      apply add_le_add (hcharge input context fuel cache actualCache hinvariant hcomputed)
      have hstep := FtsProbeSimulation.relTriple_and_left_support
        (himpl input context fuel cache actualCache hinvariant hvisible hpublished)
        (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
          intro left hleft result heq
          subst left
          exact hcomputed.of_mem_runResolved ((impl input).run cache) context fuel table result hleft)
      have hcost := expected_cost_le_of_relTriple hstep
        (fun left => match left with
          | none => 0
          | some result => expectedLiveNativeContextCharge impl charge (next result.value.1)
              result.context result.remaining result.table result.value.2)
        (fun right => expectedOuterQueryCharge secretKey actualCharge (next right.1) right.2)
        (fun _ => 0) (by
          intro left right hrelation
          simp only [add_zero]
          cases left with
          | none => exact bot_le
          | some result =>
              dsimp only
              rcases hrelation.1 with hclean | hdoomed
              · rw [hclean.1, ← hclean.2.1]
                exact ih result.value.1 result.context result.remaining result.value.2 right.2
                  hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 (hrelation.2 result rfl)
              · rw [expectedLiveNativeContextCharge_eq_zero_of_not_completable impl charge
                  (next result.value.1) result.context result.remaining result.table result.value.2 (by
                    rw [hdoomed.1]
                    exact hdoomed.2.2.2)]
                exact bot_le)
      simpa only [mul_zero, tsum_zero, add_zero] using hcost

/-- Select before executing a query. Ordinals count outer hashing, uniform sampling and signing requests. -/
noncomputable def liveNativeQuerySelection
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option CanonicalQuerySelection) :=
  OracleComp.construct (fun _ _ _ _ _ _ => pure none)
    (fun input _ next ordinal context fuel table cache =>
      if DeferredCompletable table context then
        match ordinal with
        | 0 => pure (some ⟨input, context, fuel, table, cache⟩)
        | ordinal + 1 => do
            let result ← runResolvedFromTable context fuel table ((impl input).run cache)
            match result with
            | none => pure none
            | some result => next result.value.1 ordinal result.context result.remaining result.table result.value.2
      else pure none) computation

theorem liveNativeQuerySelection_pure
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) (value : α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    liveNativeQuerySelection impl (pure value) ordinal context fuel table cache = pure none := rfl

theorem liveNativeQuerySelection_query_bind
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    liveNativeQuerySelection impl (OracleSpec.query input >>= next) ordinal context fuel table cache =
      if DeferredCompletable table context then
        match ordinal with
        | 0 => pure (some ⟨input, context, fuel, table, cache⟩)
        | ordinal + 1 => do
            let result ← runResolvedFromTable context fuel table ((impl input).run cache)
            match result with
            | none => pure none
            | some result =>
                liveNativeQuerySelection impl (next result.value.1)
                  ordinal result.context result.remaining result.table result.value.2
      else pure none := rfl

set_option maxRecDepth 100000 in
theorem tsum_liveNativeQuerySelection_charge
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' ordinal, ∑' selection,
      Pr[= selection | liveNativeQuerySelection impl computation ordinal context fuel table cache] *
        CanonicalQuerySelection.charge charge selection) =
      expectedLiveNativeContextCharge impl charge computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [liveNativeQuerySelection_pure, tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]
      rfl
  | query_bind input next ih =>
      rw [expectedLiveNativeContextCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, tsum_eq_zero_add' ENNReal.summable]
        simp only [liveNativeQuerySelection_query_bind, hcomplete, ↓reduceIte,
          tsum_probOutput_pure_mul, CanonicalQuerySelection.charge]
        congr 1
        simp only [tsum_probOutput_bind_mul]
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro result
        rw [ENNReal.tsum_mul_left]
        congr 1
        cases result with
        | none => simp only [tsum_probOutput_pure_mul, tsum_zero]
        | some result => exact ih result.value.1 result.context result.remaining result.table result.value.2
      · simp only [liveNativeQuerySelection_query_bind, hcomplete, ↓reduceIte,
          tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]

end SphincsSecurity.Concrete.OtsProbeSimulation
