import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivate

/-!
# Boundary failure probability composition

The canonical deferred failure is the union of the ordinary direct failure and the first hit
against a privately retained structural value. This file keeps the final probability and security
composition separate from the two endpoint bounds.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonicalDeferredFinishIsNone_le_boundary_causes
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= true | sampledCanonicalDeferredFinishIsNone adversary parameter ftsSecret fuel] ≤
      Pr[= .ordinaryFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] +
        Pr[= .privateStructuralFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[= true |
        sampledAllDirectBoundaryFinishIsNone adversary parameter ftsSecret fuel] :=
      OracleComp.probOutput_congr rfl
        (evalDist_sampledCanonicalDeferredFinishIsNone_eq_allDirect adversary parameter
          ftsSecret fuel)
    _ = Pr[= true | DirectBoundaryOutcome.failed <$>
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] :=
      OracleComp.probOutput_congr rfl
        (evalDist_failed_sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel).symm
    _ = Pr[fun hit : Bool => hit = true | DirectBoundaryOutcome.failed <$>
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] :=
      (probEvent_eq_eq_probOutput _ true).symm
    _ = Pr[fun outcome => outcome.failed = true |
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] := by
      rw [probEvent_map]
      rfl
    _ ≤ _ := probEvent_failed_le_ordinary_add_private
      (sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_boundary_causes
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      Pr[= .ordinaryFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] +
        Pr[= .privateStructuralFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel] :=
  (probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_canonicalDeferred adversary
      parameter ftsSecret fuel).trans
    (probEvent_sampledCanonicalDeferredFinishIsNone_le_boundary_causes adversary parameter
      ftsSecret fuel)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_two_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinary :
      Pr[= .ordinaryFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (hprivate :
      Pr[= .privateStructuralFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      ((2 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[= .ordinaryFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] +
        Pr[= .privateStructuralFailure |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] :=
      probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_boundary_causes adversary
        parameter ftsSecret q
    _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add hordinary hprivate
    _ = _ := by
      push_cast
      ring

theorem security_of_sampledAllDirectBoundaryDetailedRetained_causes_le
    (hordinary : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[= .ordinaryFailure |
            sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
          (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (hprivate : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[= .privateStructuralFailure |
            sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
          (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    SphincsSecurityStatement := by
  apply security_of_sampledWinningRetainedVerifyProbe_le_mul 2 (by omega)
  intro q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  exact probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_two_mul adversary parameter
    ftsSecret q
      (hordinary q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts)
      (hprivate q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts)

end SphincsSecurity.Concrete.OtsProbeSimulation
