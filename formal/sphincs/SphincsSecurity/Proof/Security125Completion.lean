import SphincsSecurity.Proof.OtsProbeDiagnosticJoint125
import SphincsSecurity.Proof.Security125Endpoint

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem probEvent_jointBoundary_failed_le_twenty_three_sevenths_mul
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
      ((23 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hfuel : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [digestBits] at hq ⊢
    omega
  apply (probEvent_sampledJointSnapshot_failed_le_diagnostic_add_residual adversary parameter
    ftsSecret q hbound).trans
  calc
    _ ≤ ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      add_le_add
        (probEvent_sampledDiagnostic_bad_le_fifteen_sevenths_mul adversary parameter
          ftsSecret q hfuel hbound hq)
        (probEvent_jointResidual_le_eight_sevenths_mul adversary parameter ftsSecret q hbound hq)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      ring

set_option maxRecDepth 100000 in
theorem probEvent_sampledActualRetained_verifyProbe_le_twenty_three_sevenths_mul
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
      ((23 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter
    ftsSecret q).trans
      (probEvent_jointBoundary_failed_le_twenty_three_sevenths_mul adversary parameter
        ftsSecret q hbound hq)

set_option maxRecDepth 100000 in
theorem security125_of_completed_joint_boundary : HasClassicalSecurityBits Concrete.scheme 125 := by
  apply security125_of_sampledVerifyProbe_le_seven_mul_inv129
  intro q _hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  have hbound := probEvent_sampledActualRetained_verifyProbe_le_twenty_three_sevenths_mul
    adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq
      parameter hparameter table ftsSecret hfts root) hqMax
  apply hbound.trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  norm_num [digestBits]
  have hnonnegative : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  linarith

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
