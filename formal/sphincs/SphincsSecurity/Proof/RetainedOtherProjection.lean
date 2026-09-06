import SphincsSecurity.Proof.AnswerEncodingGame
import SphincsSecurity.Proof.RetainedNonOtsProjection

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation

def retainedOtherResidual
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  retainedNonOtsResidual result ∧
    ¬ EncodingBad result.2.1.2 (primitiveAccountingKey result.1.parameter result.1.otsSecret result.1.ftsSecret)

def otherViewedTerminalEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  cleanUncoveredEvent parameter otsSecret ftsSecret result ∨
    cleanMessageEvent parameter otsSecret ftsSecret result ∨
      ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result

theorem firstParentEncodingResidual_ots_or_fts_or_remaining (adversary : Adversary)
    {result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentRetainedGame adversary))
    (hresidual : firstParentEncodingResidual (result.1, firstParentRetainedVerdictProjection result.2)) :
    SampledFirstParentOrOtsWitness result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedOtherResidual result := by
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
    · exact Or.inr (Or.inr ⟨⟨hwin, fun h => hclean (Or.inl h), hwitness⟩, fun h => hclean (Or.inr h)⟩)

theorem otherViewedTerminalEvent_of_retained_log (adversary : Adversary) (secrets : SampledSecrets)
    (left : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)
    (right : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hlog : retainedGameLogProjection left.1 = OtsProbeSimulation.viewedGameLogProjection right)
    (hright : right ∈ support (gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
    (hleft : retainedOtherResidual (secrets, left)) :
    otherViewedTerminalEvent secrets.parameter secrets.otsSecret secrets.ftsSecret right := by
  have hterminal := nonOtsViewedTerminalEvent_of_retained_log adversary secrets left right hlog hright hleft.1
  rcases hterminal with hencoding | hother
  · exfalso
    apply hleft.2
    have hcache := congrArg (fun result : RetainedGameLogResult => result.2.1) hlog
    change left.1.2 = right.2.cache at hcache
    rw [hcache]
    exact (encodingBad_mk_root_iff secrets.parameter secrets.otsSecret secrets.ftsSecret right.2.cache
      right.1.1 default).mp hencoding.encodingBad
  · exact hother

theorem probEvent_retainedOtherResidual_le_viewed (adversary : Adversary) :
    Pr[retainedOtherResidual | sampledFirstParentRetainedGame adversary] ≤
      Pr[SampledViewedEvent otherViewedTerminalEvent | sampledViewedGame adversary] := by
  rw [sampledFirstParentRetainedGame, probEvent_bind_eq_tsum, probEvent_sampledViewedGame_eq_weighted]
  apply ENNReal.tsum_le_tsum
  intro secrets
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  apply probEvent_le_of_relTriple (FtsProbeSimulation.relTriple_and_right_support
    (relTriple_firstParentRetained_viewed_log adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
  intro left right hrel hleft
  exact otherViewedTerminalEvent_of_retained_log adversary secrets left right hrel.1 hrel.2 hleft

theorem probEvent_firstParentEncodingResidual_le_ots_allowance (adversary : Adversary) (allowance : ENNReal)
    (hots : Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] ≤
      allowance + (sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[SampledViewedEvent otherViewedTerminalEvent | sampledViewedGame adversary]) := by
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  apply (probEvent_mono
    (q := fun result => SampledFirstParentOrOtsWitness result ∨
      SampledFirstFtsParentRecord (result.1, firstParentRetainedVerdictProjection result.2) ∨ retainedOtherResidual result)
    (fun _ hresult hresidual => firstParentEncodingResidual_ots_or_fts_or_remaining adversary hresult hresidual)).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add hots
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add _ (probEvent_retainedOtherResidual_le_viewed adversary)
  have hfts := probEvent_sampledFirstFtsParentRecord_le_queryCharge adversary
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map] at hfts
  exact hfts

theorem probEvent_firstParentEncodingResidual_le_jointOts_add_fts_add_remaining (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] ≤
      (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      (sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[SampledViewedEvent otherViewedTerminalEvent | sampledViewedGame adversary]) :=
  probEvent_firstParentEncodingResidual_le_ots_allowance adversary _
    (probEvent_sampledFirstParentOrOtsWitness_le_actualOtsCount_rate_add_erasure adversary q hq hqSpace)

end SphincsSecurity.Concrete
