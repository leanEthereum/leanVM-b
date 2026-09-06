import SphincsSecurity.Proof.JointProbeNonSecretBudget
import SphincsSecurity.Proof.AnswerEncodingQueryBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (IsOtsPosition)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition

theorem FtsProbeSimulation.NonSecretHashInput.of_atEncoding
    {parameter : PublicParameter} {input : HashInput} {position : EncodingPosition}
    (hat : AtEncodingPosition parameter input position) : NonSecretHashInput parameter input := by
  refine ⟨?_, ?_⟩
  · rintro ⟨candidate, _, hc⟩
    exact hat.not_atPosition candidate hc
  · rw [decodeProbe?_eq_none_iff]
    intro probe heq
    apply hat.not_atPosition (.ftsLeaf probe.index probe.tree probe.leafIdx)
    rw [← heq]
    exact ⟨digestBytes probe.candidate, rfl⟩

theorem parentStoppedEncoding_add_ftsParent_le_one_of_secret_input
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hsecret : ¬ FtsProbeSimulation.NonSecretHashInput secretKey.parameter input) :
    parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input ≤ 1 := by
  have hnotEncoding : ¬ ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position := by
    rintro ⟨position, hat⟩
    exact hsecret (FtsProbeSimulation.NonSecretHashInput.of_atEncoding hat)
  have hparent : ftsParentQueryCharge secretKey cache input = 0 := by
    have hnotParent : ¬ ∃ position : Position, AtPosition secretKey.parameter input position ∧ ¬ IsOtsPosition position ∧
        ¬ ∀ child ∈ position.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child := by
      rintro ⟨position, hat, hnotOts, hchildren⟩
      have hnoOts : ¬ ∃ candidate : Position, IsOtsPosition candidate ∧ AtPosition secretKey.parameter input candidate := by
        rintro ⟨candidate, hc, hcat⟩
        exact hnotOts (atPosition_unique secretKey.parameter hcat hat ▸ hc)
      have hdecode : FtsProbeSimulation.decodeProbe? secretKey.parameter input ≠ none := fun h => hsecret ⟨hnoOts, h⟩
      obtain ⟨probe, hprobe⟩ := Option.ne_none_iff_exists'.mp hdecode
      have hp : AtPosition secretKey.parameter input (.ftsLeaf probe.index probe.tree probe.leafIdx) := by
        rw [← (FtsProbeSimulation.decodeProbe?_eq_some_iff secretKey.parameter input probe).mp hprobe]
        exact ⟨digestBytes probe.candidate, rfl⟩
      have heq := atPosition_unique secretKey.parameter hat hp
      subst position
      exact hchildren (by simp [Position.children])
    simp only [ftsParentQueryCharge, parentReserveCharge, if_neg hnotParent, Nat.cast_zero]
  rw [hparent, add_zero]
  exact parentStoppedEncodingQueryCharge_le_one_of_not_encoding secretKey cache input hnotEncoding

theorem parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input ≤
      1 + if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0 := by
  by_cases hnon : FtsProbeSimulation.NonSecretHashInput secretKey.parameter input
  · rw [if_pos hnon, show (1 : ENNReal) + 1 = 2 by norm_num]
    exact le_self_add.trans (answerEncoding_parent_ots_fts_queryCharge_le_two secretKey cache input)
  · rw [if_neg hnon, add_zero]
    exact parentStoppedEncoding_add_ftsParent_le_one_of_secret_input secretKey cache input hnon

theorem parentStoppedEncoding_ftsParent_jointProbe_queryCharge_le_two
    (secretKey : SecretKey) (actualCache : QueryCache HashSpec) (input : HashInput)
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache)
    (state : AdaptiveRevealProbe.State FtsProbeSimulation.Coordinate) (ftsCache : FtsProbeSimulation.SplitHashCache) :
    (parentStoppedEncodingQueryCharge secretKey actualCache input + ftsParentQueryCharge secretKey actualCache input) +
      (FtsProbeSimulation.jointOtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache +
        FtsProbeSimulation.jointFtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache) ≤ 2 := by
  have hstep := FtsProbeSimulation.jointOts_add_fts_add_nonSecret_queryCharge_le_one
    secretKey.parameter (.inl (.inr input)) context cache state ftsCache
  simp only [FtsProbeSimulation.jointNonSecretQueryCharge, OtsProbeSimulation.IsOuterHash, if_true] at hstep
  calc
    _ ≤ (1 + if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0) +
        (FtsProbeSimulation.jointOtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache +
          FtsProbeSimulation.jointFtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache) :=
      add_le_add (parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret secretKey actualCache input) le_rfl
    _ = 1 + ((FtsProbeSimulation.jointOtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache +
          FtsProbeSimulation.jointFtsQueryCharge secretKey.parameter (.inl (.inr input)) context cache state ftsCache) +
        if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0) := by ac_rfl
    _ ≤ 1 + 1 := add_le_add le_rfl hstep
    _ = 2 := by norm_num

end SphincsSecurity.Concrete
