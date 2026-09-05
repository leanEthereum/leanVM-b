import SphincsSecurity.Proof.OtsProbeLiveKnownRootCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveNativeHashQuerySelection
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option CanonicalQuerySelection) :=
  OracleComp.construct (fun _ _ _ _ _ _ => pure none)
    (fun input _ next ordinal context fuel table cache =>
      if DeferredCompletable table context then
        if IsOuterHash input ∧ ordinal = 0 then pure (some ⟨input, context, fuel, table, cache⟩)
        else do
          let result ← runResolvedFromTable context fuel table ((impl input).run cache)
          match result with
          | none => pure none
          | some result =>
              next result.value.1 (if IsOuterHash input then ordinal - 1 else ordinal)
                result.context result.remaining result.table result.value.2
      else pure none) computation

theorem liveNativeHashQuerySelection_pure
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (value : α) (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    liveNativeHashQuerySelection impl (pure value) ordinal context fuel table cache = pure none := rfl

theorem liveNativeHashQuerySelection_query_bind
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    liveNativeHashQuerySelection impl (OracleSpec.query input >>= next) ordinal context fuel table cache =
      if DeferredCompletable table context then
        if IsOuterHash input ∧ ordinal = 0 then pure (some ⟨input, context, fuel, table, cache⟩)
        else do
          let result ← runResolvedFromTable context fuel table ((impl input).run cache)
          match result with
          | none => pure none
          | some result =>
              liveNativeHashQuerySelection impl (next result.value.1)
                (if IsOuterHash input then ordinal - 1 else ordinal) result.context result.remaining result.table result.value.2
      else pure none := rfl

theorem tsum_liveNativeHashQuerySelection_charge
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (hzero : ∀ input context fuel cache, ¬IsOuterHash input → charge input context fuel cache = 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' ordinal, ∑' selection,
      Pr[= selection | liveNativeHashQuerySelection impl computation ordinal context fuel table cache] *
        CanonicalQuerySelection.charge charge selection) =
      expectedLiveNativeContextCharge impl charge computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [liveNativeHashQuerySelection_pure, tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]
      rfl
  | query_bind input next ih =>
      rw [expectedLiveNativeContextCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        by_cases hhash : IsOuterHash input
        · rw [tsum_eq_zero_add' ENNReal.summable]
          simp only [liveNativeHashQuerySelection_query_bind, hcomplete, hhash, true_and, ↓reduceIte,
            Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Nat.add_sub_cancel,
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
        · rw [hzero input context fuel cache hhash, zero_add]
          simp only [liveNativeHashQuerySelection_query_bind, hcomplete, hhash, false_and, ↓reduceIte,
            tsum_probOutput_bind_mul]
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro result
          rw [ENNReal.tsum_mul_left]
          congr 1
          cases result with
          | none => simp only [tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]
          | some result => exact ih result.value.1 result.context result.remaining result.table result.value.2
      · simp only [liveNativeHashQuerySelection_query_bind, hcomplete, ↓reduceIte,
          tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]

theorem knownEncodingRootOuterCharge_eq_zero_of_not_hash
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (hnot : ¬IsOuterHash input) :
    knownEncodingRootOuterCharge parameter input context fuel cache = 0 := by
  cases input with
  | inl input => cases input <;> simp_all [IsOuterHash, knownEncodingRootOuterCharge]
  | inr message => rfl

theorem tsum_knownEncodingRootHashSelection_probability_eq_charge
    (parameter : PublicParameter)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' ordinal, Pr[KnownHiddenEncodingRootSelection parameter |
      liveNativeHashQuerySelection impl computation ordinal context fuel table cache]) * (4 / 3 : ENNReal) =
      expectedLiveNativeContextCharge impl (knownEncodingRootOuterCharge parameter) computation context fuel table cache := by
  rw [← tsum_liveNativeHashQuerySelection_charge impl _ (knownEncodingRootOuterCharge_eq_zero_of_not_hash parameter),
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro ordinal
  exact (expected_knownEncodingRootSelection_charge_eq_probability parameter _).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
