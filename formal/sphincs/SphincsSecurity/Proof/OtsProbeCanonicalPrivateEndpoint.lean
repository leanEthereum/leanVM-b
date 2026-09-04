import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceAssembly
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryFinalAssembly
import SphincsSecurity.Proof.OtsProbeGroupedTerminal

/-!
# Canonical private-witness endpoint

The canonical source bound is proved on a snapshot-rich output. This file erases those snapshots
and packages the same eight-unit estimate on the witness-plan output used by the boundary bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def sampledGranularAllCanonicalPrivateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessPlanOutput := do
  let table ← sampleOtsHashTable
  granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel

set_option maxRecDepth 100000 in
theorem map_erase_sampledGranularAllCanonicalPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    erasePrivateWitnessSnapshotOutput <$>
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel =
      sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret fuel := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
    sampledGranularAllCanonicalPrivateWitnessPlan
  rw [map_bind]
  apply bind_congr
  intro table
  exact map_erase_granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
    ftsSecret fuel

set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_privateWitnessPlan_eq_snapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => output.1.isSome = true |
        sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret fuel] =
      Pr[fun output => output.1.isSome = true |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[fun output => output.1.isSome = true |
        erasePrivateWitnessSnapshotOutput <$>
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret
            fuel] := by
      rw [map_erase_sampledGranularAllCanonicalPrivateWitnessSnapshot]
    _ = _ := by
      rw [probEvent_map]
      rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledCanonical_privateWitnessPlan_le_eight_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun output => output.1.isSome = true |
        sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q] ≤
      ((8 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledCanonical_privateWitnessPlan_eq_snapshot]
  exact probEvent_sampledCanonical_privateWitness_le_eight_mul adversary parameter ftsSecret q
    hexpanded hq

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledActualRetained_verifyProbe_le_ten_mul_of_canonical_boundary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hqMax : q ≤ 2 ^ securityBits)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hboundaryBridge :
      Pr[fun outcome => outcome.failed = true |
          sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
        ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          Pr[fun output => output.1.isSome = true |
            sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q]) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      ((10 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun outcome => outcome.failed = true |
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] :=
      probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_boundary_failed adversary
        parameter ftsSecret q
    _ ≤ ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[fun output => output.1.isSome = true |
          sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q] :=
      hboundaryBridge
    _ ≤ ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        ((8 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact add_le_add (le_refl _)
        (probEvent_sampledCanonical_privateWitnessPlan_le_eight_mul adversary parameter
          ftsSecret q hexpanded hqMax)
    _ = _ := by
      push_cast
      ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledActualRetained_verifyProbe_le_ten_mul_of_canonical
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hqMax : q ≤ 2 ^ securityBits)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hprivateBridge :
      Pr[= true |
          sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
            ftsSecret q] ≤
        Pr[fun output => output.1.isSome = true |
          sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q])
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
              ftsSecret q]) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      ((10 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun outcome => outcome.failed = true |
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] :=
      probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_boundary_failed adversary
        parameter ftsSecret q
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
        ((8 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact add_le_add
        (add_le_add
          (probEvent_sampledFlat_add_materializedGuardedOrdinaryRetained_le_two_mul
            adversary parameter ftsSecret q)
          (probEvent_sampledMaterializedCanonicalPrivateRetained_le_zero adversary parameter
            ftsSecret q))
        (hprivateBridge.trans
          (probEvent_sampledCanonical_privateWitnessPlan_le_eight_mul adversary parameter
            ftsSecret q hexpanded hqMax))
    _ = _ := by
      push_cast
      ring

theorem security_of_canonical_private_bridge_and_boundary_domination
    (hprivateBridge : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[= true |
            sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
              ftsSecret q] ≤
          Pr[fun output => output.1.isSome = true |
            sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q])
    (hdomination : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
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
                ftsSecret q]) :
    SphincsSecurityStatement := by
  apply security_of_sampledWinningRetainedVerifyProbe_grouped_le_mul 10 (by omega)
  intro q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  exact probEvent_sampledActualRetained_verifyProbe_le_ten_mul_of_canonical adversary parameter
    ftsSecret q hqMax
      (fun table root =>
        isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter
          table ftsSecret hfts root)
      (hprivateBridge q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts)
      (hdomination q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts)

theorem security_of_canonical_boundary_bridge
    (hboundaryBridge : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun outcome => outcome.failed = true |
            sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q] ≤
          ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
            Pr[fun output => output.1.isSome = true |
              sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q]) :
    SphincsSecurityStatement := by
  apply security_of_sampledWinningRetainedVerifyProbe_grouped_le_mul 10 (by omega)
  intro q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  exact probEvent_sampledActualRetained_verifyProbe_le_ten_mul_of_canonical_boundary
    adversary parameter ftsSecret q hqMax
      (fun table root =>
        isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter
          table ftsSecret hfts root)
      (hboundaryBridge q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts)

end SphincsSecurity.Concrete.OtsProbeSimulation
