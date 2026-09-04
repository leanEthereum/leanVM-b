import SphincsSecurity.Proof.OtsProbeJointClassification

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

attribute [local irreducible] maskedPublishedTreeRoot
  sampledGranularAllCanonicalBoundaryWitnessSnapshot
  sampledGranularAllCanonicalPrivateWitnessSnapshot sampledObservedMaterializedDiagnostic

set_option maxRecDepth 100000 in
theorem probEvent_jointResidual_eq_snapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[JointSnapshotResidual |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel] =
      Pr[fun output => WitnessFirstUsesSomeDelayedLayerRootSnapshot output ∨
          WitnessFirstUsesSomeNonLayerRoot (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[fun output => WitnessFirstUsesSomeDelayedLayerRootSnapshot output ∨
          WitnessFirstUsesSomeNonLayerRoot (erasePrivateWitnessSnapshotOutput output) |
        BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel] := by
      rw [probEvent_map]
      rfl
    _ = _ := OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_witnessSnapshot_sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary
        parameter ftsSecret fuel)

set_option maxRecDepth 100000 in
theorem probEvent_jointResidual_le_fifteen_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[JointSnapshotResidual |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_jointResidual_eq_snapshot]
  apply (probEvent_or_le _ _ _).trans
  calc
    _ ≤ ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      add_le_add
        (probEvent_sampledCanonical_delayed_le_eight_sevenths_mul_closed adversary parameter
          ftsSecret q hbound hq)
        (probEvent_sampledCanonical_nonRoot_le_mul adversary parameter ftsSecret q hbound)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      ring

set_option maxRecDepth 100000 in
theorem probEvent_jointBoundary_failed_le_thirty_seven_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((37 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hfuel : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [digestBits] at hq ⊢
    omega
  apply (probEvent_sampledJointSnapshot_failed_le_diagnostic_add_residual adversary parameter
    ftsSecret q hbound).trans
  calc
    _ ≤ ((22 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      add_le_add
        (probEvent_sampledDiagnostic_bad_le_twenty_two_sevenths_mul adversary parameter
          ftsSecret q hfuel hbound hq)
        (probEvent_jointResidual_le_fifteen_sevenths_mul adversary parameter ftsSecret q hbound hq)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      ring

set_option maxRecDepth 100000 in
theorem probEvent_sampledActualRetained_verifyProbe_le_thirty_seven_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      ((37 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter
    ftsSecret q).trans
      (probEvent_jointBoundary_failed_le_thirty_seven_sevenths_mul adversary parameter
        ftsSecret q hbound hq)

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
