import SphincsSecurity.Proof.OtsProbeCanonicalChargeSampled

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

structure CanonicalQuerySelection where
  input : (OracleWorld + SigningSpec).Domain
  context : DeferredContext
  fuel : Nat
  table : OtsSecretIndex → HashOutput
  cache : SplitHashCache

/-- Select before executing a query. Ordinals count outer hashing, uniform sampling and signing requests. -/
noncomputable def canonicalQuerySelection
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option CanonicalQuerySelection) :=
  OracleComp.construct (fun _ _ _ _ _ _ => pure none)
    (fun input _ next ordinal context fuel table cache =>
      if DeferredCompletable table context then
        match ordinal with
        | 0 => pure (some ⟨input, context, fuel, table, cache⟩)
        | ordinal + 1 => do
            let result ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret
              input context fuel table cache
            match result with
            | none => pure none
            | some result => next result.value.1 ordinal result.context result.remaining result.table result.value.2
      else pure none) computation

noncomputable def CanonicalQuerySelection.charge
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞) :
    Option CanonicalQuerySelection → ℝ≥0∞
  | none => 0
  | some selection => charge selection.input selection.context selection.fuel selection.cache

theorem canonicalQuerySelection_pure
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (value : α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    canonicalQuerySelection parameter root ftsSecret (pure value) ordinal context fuel table cache = pure none := rfl

theorem canonicalQuerySelection_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    canonicalQuerySelection parameter root ftsSecret (OracleSpec.query input >>= next) ordinal context fuel table cache =
      if DeferredCompletable table context then
        match ordinal with
        | 0 => pure (some ⟨input, context, fuel, table, cache⟩)
        | ordinal + 1 => do
            let result ← canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache
            match result with
            | none => pure none
            | some result =>
                canonicalQuerySelection parameter root ftsSecret (next result.value.1)
                  ordinal result.context result.remaining result.table result.value.2
      else pure none := rfl

set_option maxRecDepth 100000 in
theorem tsum_canonicalQuerySelection_charge
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' ordinal, ∑' selection,
      Pr[= selection | canonicalQuerySelection parameter root ftsSecret computation ordinal context fuel table cache] *
        CanonicalQuerySelection.charge charge selection) =
      expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [canonicalQuerySelection_pure, tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]
      rfl
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, tsum_eq_zero_add' ENNReal.summable]
        simp only [canonicalQuerySelection_query_bind, hcomplete, ↓reduceIte,
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
      · simp only [canonicalQuerySelection_query_bind, hcomplete, ↓reduceIte,
          tsum_probOutput_pure_mul, CanonicalQuerySelection.charge, tsum_zero]

end SphincsSecurity.Concrete.OtsProbeSimulation
