import SphincsSecurity.Proof.RetainedOtherProjection
import SphincsSecurity.Proof.FirstParentJointSecrets

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def RetainedFtsSecretWitness
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  FtsProbeSimulation.RetainedUncoveredFtsSecretWitness result.1.parameter result.1.otsSecret
    (fun coordinate => result.1.ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) result.2.1

def retainedNonSecretResidual
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  retainedOtherResidual result ∧ ¬RetainedFtsSecretWitness result

def messageOrForestEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  cleanMessageEvent parameter otsSecret ftsSecret result ∨
    ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result

theorem messageOrForestEvent_of_retained_log (adversary : Adversary) (secrets : SampledSecrets)
    (left : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)
    (right : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hlog : retainedGameLogProjection left.1 = OtsProbeSimulation.viewedGameLogProjection right)
    (hright : right ∈ support (gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
    (hleft : retainedNonSecretResidual (secrets, left)) :
    messageOrForestEvent secrets.parameter secrets.otsSecret secrets.ftsSecret right := by
  rcases otherViewedTerminalEvent_of_retained_log adversary secrets left right hlog hright hleft.1 with hfts | hrest
  · exfalso
    apply hleft.2
    apply FtsProbeSimulation.logProjection_uncovered_imp_retained
    change FtsProbeSimulation.RetainedLogUncoveredFtsSecretWitness secrets.parameter secrets.otsSecret
      (fun coordinate => secrets.ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2)
      (retainedGameLogProjection left.1)
    rw [hlog]
    exact hfts.2
  · exact hrest

theorem probEvent_retainedNonSecretResidual_le_viewed (adversary : Adversary) :
    Pr[retainedNonSecretResidual | sampledFirstParentRetainedGame adversary] ≤
      Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary] := by
  rw [sampledFirstParentRetainedGame, probEvent_bind_eq_tsum, probEvent_sampledViewedGame_eq_weighted]
  apply ENNReal.tsum_le_tsum
  intro secrets
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  apply probEvent_le_of_relTriple (FtsProbeSimulation.relTriple_and_right_support
    (relTriple_firstParentRetained_viewed_log adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
  intro left right hrel hleft
  exact messageOrForestEvent_of_retained_log adversary secrets left right hrel.1 hrel.2 hleft

theorem probEvent_firstParentEncodingResidual_le_secret_allowance (adversary : Adversary) (allowance : ENNReal)
    (hsecrets : Pr[SampledFirstParentOrSecretWitness | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    Pr[firstParentEncodingResidual | sampledFirstParentSettlementGame adversary] ≤
      allowance + (sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary]) := by
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  apply (probEvent_mono
    (q := fun result => SampledFirstParentOrSecretWitness result ∨
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
  have hfts := probEvent_sampledFirstFtsParentRecord_le_queryCharge adversary
  rw [← sampledFirstParentRetainedGame_verdict_projection, probEvent_map] at hfts
  exact hfts

end SphincsSecurity.Concrete
