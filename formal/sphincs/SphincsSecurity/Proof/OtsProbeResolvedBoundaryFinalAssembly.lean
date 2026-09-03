import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionOrdinal

/-!
# Final resolved-boundary assembly

The canonical private endpoint is impossible. Keeping that exact zero in the final accounting
leaves seven units for the granular private endpoint and two for the ordinary endpoints.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledMaterializedCanonicalPrivateRetained_le_zero
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    Pr[= true |
        sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret q] ≤ 0 := by
  unfold sampledMaterializedCanonicalPrivateRetained
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  rw [probEvent_eq_eq_probOutput]
  exact probEvent_materializedCanonicalPrivateRetained_le_zero adversary parameter table
    ftsSecret q

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_failed_sampledAllDirectBoundaryDetailedRetainedOutcome_le_nine_mul_of_granular
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hdomination :
      Pr[fun outcome => outcome.failed = true |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
        Pr[= true |
            sampledFlatDetailedOrdinaryRetained adversary parameter ftsSecret q] +
          Pr[= true |
            sampledMaterializedGuardedSafeOrdinaryRetained adversary parameter ftsSecret q] +
          Pr[= true |
            sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret q] +
          Pr[= true |
            sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
              ftsSecret q])
    (hgranular :
      Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] ≤
        ((7 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun outcome => outcome.failed = true |
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
      ((9 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[= true |
          sampledFlatDetailedOrdinaryRetained adversary parameter ftsSecret q] +
        Pr[= true |
          sampledMaterializedGuardedSafeOrdinaryRetained adversary parameter ftsSecret q] +
        Pr[= true |
          sampledMaterializedCanonicalPrivateRetained adversary parameter ftsSecret q] +
        Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] := hdomination
    _ ≤ ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + 0 +
          ((7 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact add_le_add
        (add_le_add
          (probEvent_sampledFlat_add_materializedGuardedOrdinaryRetained_le_two_mul
            adversary parameter ftsSecret q)
          (probEvent_sampledMaterializedCanonicalPrivateRetained_le_zero adversary parameter
            ftsSecret q))
        hgranular
    _ = _ := by
      push_cast
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation
