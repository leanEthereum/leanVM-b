import SphincsSecurity.Proof.OtsProbeHiddenSelectionCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def combinedOtsProbeCharge (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ℝ≥0∞ :=
  materializedRetainedCharge adversary parameter ftsSecret (2 * q) +
    sampledHiddenSelectionCharge adversary parameter ftsSecret q +
    sampledResidualSelectionCharge adversary parameter ftsSecret q

theorem probEvent_sampledActualRetained_verifyProbe_le_combinedCharge126
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      combinedOtsProbeCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampledActualRetained_verifyProbe_le_charge_add_hiddenFailures adversary parameter ftsSecret q hbound).trans
  apply (add_le_add
    (add_le_add le_rfl (probEvent_sampledDiagnostic_successfulDoomed_le_selectionCharge126 adversary parameter ftsSecret q hbound hq))
    (probEvent_jointResidual_le_selectionCharge126 adversary parameter ftsSecret q hbound hq)).trans_eq
  rw [← add_mul, ← add_mul]
  rfl

theorem probEvent_sampledActualRetained_verifyProbe_le_combinedCharge126_of_hashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      combinedOtsProbeCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledActualRetained_verifyProbe_le_combinedCharge126 adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root) hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
