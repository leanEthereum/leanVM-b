import SphincsSecurity.Proof.JointProbeOriginalSampledSecretBound
import SphincsSecurity.Proof.SecurityStoppedParentEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation
open FtsProbeSimulation.JointOriginal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem firstParentEncodingResidual_firstOtsOrCleanSecret_or_remaining
    (adversary : Adversary)
    {result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentRetainedGame adversary))
    (hresidual : firstParentEncodingResidual (result.1, firstParentRetainedVerdictProjection result.2)) :
    SampledFirstOtsOrCleanSecret result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedNonSecretResidual result := by
  cases hs : result.2.2 with
  | some record =>
      have hp : (result.1, firstParentRetainedVerdictProjection result.2) ∈ support (sampledFirstParentSettlementGame adversary) := by
        rw [← sampledFirstParentRetainedGame_verdict_projection, support_map]
        exact ⟨result, hresult, rfl⟩
      rcases sampledFirstParentRecord_ots_or_fts adversary hp (by simp only [firstParentRetainedVerdictProjection, hs, Option.isSome_some]) with ho | hf
      · exact Or.inl (Or.inl ho)
      · exact Or.inr (Or.inl hf)
  | none =>
      obtain ⟨hwin, hparent | hclean⟩ := hresidual
      · simp [firstParentRetainedVerdictProjection, hs] at hparent
      · by_cases ho : WinningRetainedVerifyProbeAfterOtsSecret result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1
        · exact Or.inl (Or.inr ⟨hs, Or.inl ho⟩)
        · by_cases hf : RetainedFtsSecretWitness result
          · exact Or.inl (Or.inr ⟨hs, Or.inr hf⟩)
          · exact Or.inr (Or.inr ⟨⟨⟨hwin, fun h => hclean (Or.inl h), ho⟩, fun h => hclean (Or.inr h)⟩, hf⟩)

theorem probEvent_firstParentEncodingResidual_le_clean_secret_allowance
    (adversary : Adversary) (allowance : ENNReal)
    (hsecrets : Pr[SampledFirstOtsOrCleanSecret | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] ≤
      allowance + (sampledPreParentQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary]) := by
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  apply (probEvent_mono
    (q := fun result => SampledFirstOtsOrCleanSecret result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedNonSecretResidual result)
    (fun _ hr he => firstParentEncodingResidual_firstOtsOrCleanSecret_or_remaining adversary hr he)).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add hsecrets
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add _ (probEvent_retainedNonSecretResidual_le_viewed adversary)
  have hfts := probEvent_sampledFirstFtsParentRecord_le_preParentQueryCharge adversary
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map] at hfts
  exact hfts

theorem forgeAdvantage_le_preParent_add_clean_secret_allowance
    (adversary : Adversary) (allowance : ENNReal)
    (hsecrets : Pr[SampledFirstOtsOrCleanSecret | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      allowance + Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary] := by
  apply (forgeAdvantage_le_preParentEncodingCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl
    (probEvent_firstParentEncodingResidual_le_clean_secret_allowance adversary allowance hsecrets)).trans_eq
  rw [show sampledPreParentEncodingCharge adversary =
    sampledPreParentQueryCharge parentStoppedEncodingQueryCharge adversary from rfl, sampledPreParentQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
  ring

theorem forgeAdvantage_le_preParent_add_originalSharedFailure_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledParentSharedFailureRisk adversary q fuel +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_preParent_add_clean_secret_allowance adversary _
    (probEvent_sampledFirstOtsOrCleanSecret_le_sharedFailure adversary q hq fuel)).trans
      (add_le_add le_rfl (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax))

end SphincsSecurity.Concrete
