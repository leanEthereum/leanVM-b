import SphincsSecurity.Proof.SigningStoppedOuterBudget
import SphincsSecurity.Proof.SecurityStoppedParentEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation (retainedGameRestComputation)
attribute [local instance] Classical.propDecidable

noncomputable def sampledPreParentRestHashCharge (adversary : Adversary) : ENNReal :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    ∑' result, Pr[= result | (simulateQ romImpl
      (liftM (treeRoot secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest)).run ∅] *
      expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret) (fun _ _ => 1)
        (simulateQ (expandedAdversaryImpl ⟨secrets.parameter, result.1, secrets.otsSecret, secrets.ftsSecret⟩)
          (retainedGameRestComputation adversary ⟨result.1, secrets.parameter⟩)) result.2 false

noncomputable def sampledPreParentOuterNonSecretCharge (adversary : Adversary) : ENNReal :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    ∑' result, Pr[= result | (simulateQ romImpl
      (liftM (treeRoot secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest)).run ∅] *
      expectedPreExceptionOuterCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
        ⟨secrets.parameter, result.1, secrets.otsSecret, secrets.ftsSecret⟩
        (fun _ input => if FtsProbeSimulation.NonSecretHashInput secrets.parameter input then 1 else 0)
        (retainedGameRestComputation adversary ⟨result.1, secrets.parameter⟩) result.2 false

theorem sampledPreParentStructuralCharge_le_restHash_add_outerNonSecret (adversary : Adversary) :
    sampledPreParentQueryCharge signingStructuralCharge adversary ≤
      sampledPreParentRestHashCharge adversary + sampledPreParentOuterNonSecretCharge adversary := by
  change sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
    ftsParentQueryCharge secretKey cache input) adversary ≤ _
  rw [sampledPreParentStructuralCharge_eq_afterRoot]
  unfold sampledPreParentRestHashCharge sampledPreParentOuterNonSecretCharge
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro secrets
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  exact expectedPreStructuralCharge_expanded_le_preHashQueries_add_preOuterNonSecret
    (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    ⟨secrets.parameter, result.1, secrets.otsSecret, secrets.ftsSecret⟩ _ result.2 false

theorem sampledPreParentRestHashCharge_le_fullHashCharge (adversary : Adversary) :
    sampledPreParentRestHashCharge adversary ≤ sampledQueryCharge (fun _ _ _ => 1) adversary := by
  unfold sampledPreParentRestHashCharge sampledQueryCharge
  apply ENNReal.tsum_le_tsum
  intro secrets
  apply mul_le_mul' le_rfl
  rw [gameAfterSecrets, expectedQueryCharge_bind]
  apply le_trans _ (le_add_left le_rfl)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  rw [← OtsProbeSimulation.expectedQueryCharge_retained_eq_gameRest]
  exact expectedPreExceptionCharge_le_queryCharge _ _ _ _ _

theorem sampledPreParentRestHashCharge_le_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledPreParentRestHashCharge adversary ≤ q := by
  apply (sampledPreParentRestHashCharge_le_fullHashCharge adversary).trans
  simpa only [one_mul] using sampledQueryCharge_le_const (fun _ _ _ => 1) 1 (fun _ _ _ => le_rfl) adversary q hq

theorem forgeAdvantage_add_sharedNonSecret_le_stoppedRestBudget
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledPreParentRestHashCharge adversary + sampledPreParentOuterNonSecretCharge adversary) * (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_add_nonSecret_reserve_le_preParent_remaining127 adversary q hqPos hq hqMax).trans
  exact add_le_add (add_le_add
    (mul_le_mul' (sampledPreParentStructuralCharge_le_restHash_add_outerNonSecret adversary) le_rfl) le_rfl) le_rfl

end SphincsSecurity.Concrete
