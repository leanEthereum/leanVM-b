import SphincsSecurity.Proof.FirstParentOtsGame
import SphincsSecurity.Proof.FirstFtsParentGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

def retainedNonOtsResidual
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  retainedRestVerdict result.2.1.1.2 = true ∧
    ¬ Bad result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 ∧
    ¬ WinningRetainedVerifyProbeAfterOtsSecret result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1

theorem firstParentResidual_ots_or_fts_or_remaining (adversary : Adversary)
    {result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentRetainedGame adversary))
    (hresidual : firstParentSettlementResidual (result.1, firstParentRetainedVerdictProjection result.2)) :
    SampledFirstParentOrOtsWitness result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedNonOtsResidual result := by
  classical
  have hproject : (result.1, firstParentRetainedVerdictProjection result.2) ∈
      support (sampledFirstParentSettlementGame adversary) := by
    rw [← sampledFirstParentRetainedGame_verdict_projection, support_map]
    exact ⟨result, hresult, rfl⟩
  rcases hresidual with ⟨hwin, hparent | hclean⟩
  · rcases sampledFirstParentRecord_ots_or_fts adversary hproject hparent with hots | hfts
    · exact Or.inl (Or.inl hots)
    · exact Or.inr (Or.inl hfts)
  · by_cases hwitness : WinningRetainedVerifyProbeAfterOtsSecret result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1
    · exact Or.inl (Or.inr hwitness)
    · exact Or.inr (Or.inr ⟨hwin, hclean, hwitness⟩)

theorem probEvent_firstParentResidual_le_jointOts_add_fts_add_remaining (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[firstParentSettlementResidual | sampledFirstParentSettlementGame adversary] ≤
      (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      (sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[retainedNonOtsResidual | sampledFirstParentRetainedGame adversary]) := by
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  apply (probEvent_mono
    (q := fun result => SampledFirstParentOrOtsWitness result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedNonOtsResidual result)
    (fun _ hresult hresidual => firstParentResidual_ots_or_fts_or_remaining adversary hresult hresidual)).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add (probEvent_sampledFirstParentOrOtsWitness_le_actualOtsCount_rate_add_erasure adversary q hq hqSpace)
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add _ le_rfl
  have hfts := probEvent_sampledFirstFtsParentRecord_le_queryCharge adversary
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map] at hfts
  exact hfts

theorem forgeAdvantage_le_answer_jointOts_fts_parent_remaining (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    forgeAdvantage scheme adversary ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
      ((sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      (sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[retainedNonOtsResidual | sampledFirstParentRetainedGame adversary])) :=
  (forgeAdvantage_le_answer_add_first_parent_residual adversary q hq).trans
    (add_le_add le_rfl (probEvent_firstParentResidual_le_jointOts_add_fts_add_remaining adversary q hq hqSpace))

end SphincsSecurity.Concrete
