import SphincsSecurity.Proof.AnswerEncodingStoppedBound
import SphincsSecurity.Proof.ParentReserveStoppedBound
import SphincsSecurity.Proof.RetainedJointSecretProjection

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def sampledPreParentQueryCharge
    (charge : SecretKey → QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) : ENNReal :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
      (charge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false

theorem sampledPreParentQueryCharge_add
    (left right : SecretKey → QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) :
    sampledPreParentQueryCharge (fun secretKey cache input => left secretKey cache input + right secretKey cache input) adversary =
      sampledPreParentQueryCharge left adversary + sampledPreParentQueryCharge right adversary := by
  unfold sampledPreParentQueryCharge
  simp_rw [expectedPreExceptionCharge_add, mul_add, ENNReal.tsum_add]

theorem sampledPreParentQueryCharge_le_queryCharge
    (charge : SecretKey → QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) :
    sampledPreParentQueryCharge charge adversary ≤ sampledQueryCharge charge adversary := by
  unfold sampledPreParentQueryCharge sampledQueryCharge
  exact ENNReal.tsum_le_tsum fun secrets => mul_le_mul' le_rfl (expectedPreExceptionCharge_le_queryCharge _ _ _ _ _)

theorem sampledPreParentQueryCharge_eq_retained
    (charge : SecretKey → QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) :
    sampledPreParentQueryCharge charge adversary =
      ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
          (charge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
          (retainedAfterSecretsComputation adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false := by
  unfold sampledPreParentQueryCharge
  apply tsum_congr
  intro secrets
  rw [← retainedAfterSecretsComputation_verdict, expectedPreExceptionCharge_map]

theorem probEvent_sampledFirstFtsParentRecord_le_preParentQueryCharge (adversary : Adversary) :
    Pr[SampledFirstFtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      sampledPreParentQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [sampledFirstParentSettlementGame, probEvent_bind_eq_tsum, sampledPreParentQueryCharge, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro secrets
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, SampledFirstFtsParentRecord]
  unfold ftsParentQueryCharge
  exact probEvent_firstEligibleParentRecord_le_preExceptionCharge secrets.parameter secrets.otsSecret secrets.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)

theorem probEvent_firstParentEncodingResidual_le_secret_allowance_add_preParentCharge
    (adversary : Adversary) (allowance : ENNReal)
    (hsecrets : Pr[OtsProbeSimulation.SampledFirstParentOrSecretWitness | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] ≤
      allowance + (sampledPreParentQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary]) := by
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  apply (probEvent_mono
    (q := fun result => OtsProbeSimulation.SampledFirstParentOrSecretWitness result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedNonSecretResidual result)
    (fun result hresult hresidual => by
      rcases firstParentEncodingResidual_ots_or_fts_or_remaining adversary hresult hresidual with hots | hfts | hother
      · exact Or.inl (Or.inl hots)
      · exact Or.inr (Or.inl hfts)
      · by_cases hfts : RetainedFtsSecretWitness result
        · exact Or.inl (Or.inr hfts)
        · exact Or.inr (Or.inr ⟨hother, hfts⟩))).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add hsecrets
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add _ (probEvent_retainedNonSecretResidual_le_viewed adversary)
  have hfts := probEvent_sampledFirstFtsParentRecord_le_preParentQueryCharge adversary
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map] at hfts
  exact hfts

theorem forgeAdvantage_le_preParentQueryCharge_add_secret_allowance
    (adversary : Adversary) (allowance : ENNReal)
    (hsecrets : Pr[OtsProbeSimulation.SampledFirstParentOrSecretWitness | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      allowance + Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary] := by
  apply (forgeAdvantage_le_preParentEncodingCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl
    (probEvent_firstParentEncodingResidual_le_secret_allowance_add_preParentCharge adversary allowance hsecrets)).trans_eq
  rw [show sampledPreParentEncodingCharge adversary =
    sampledPreParentQueryCharge parentStoppedEncodingQueryCharge adversary from rfl, sampledPreParentQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
  ring

end SphincsSecurity.Concrete
