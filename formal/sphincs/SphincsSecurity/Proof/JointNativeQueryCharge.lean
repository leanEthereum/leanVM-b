import SphincsSecurity.Proof.OtsProbeNativeDirectBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointNativeQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  (TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input + ftsOpeningQueryReserve secretKey cache input) +
    OtsProbeSimulation.directOtsQueryCharge secretKey.parameter cache input

theorem jointNativeQueryCharge_le_ten_thirds
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    jointNativeQueryCharge secretKey cache input ≤ 10 / 3 := by
  unfold jointNativeQueryCharge
  apply (add_le_add le_rfl (OtsProbeSimulation.directOtsQueryCharge_le_refinedReserve secretKey cache input)).trans_eq
  exact structural_add_refined_openingQueryReserve secretKey cache input

theorem jointNativeQueryCharge_eq_of_not_ots
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hnot : ¬∃ position : Position, OtsProbeSimulation.IsOtsPosition position ∧ AtPosition secretKey.parameter input position) :
    jointNativeQueryCharge secretKey cache input =
      TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input + ftsOpeningQueryReserve secretKey cache input := by
  simp [jointNativeQueryCharge, OtsProbeSimulation.directOtsQueryCharge, OtsProbeSimulation.otsHashInputCharge, hnot]

theorem jointNativeQueryCharge_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : EncodingPosition)
    (hat : AtEncodingPosition secretKey.parameter input position) :
    jointNativeQueryCharge secretKey cache input = TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input := by
  have hnot : ¬∃ target : Position, OtsProbeSimulation.IsOtsPosition target ∧ AtPosition secretKey.parameter input target := by
    rintro ⟨target, _, htarget⟩
    exact hat.not_atPosition target htarget
  have hfts : ¬∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
    rintro ⟨probe, hinput⟩
    apply hat.not_atPosition (.ftsLeaf probe.index probe.tree probe.leafIdx)
    rw [← hinput]
    exact ⟨digestBytes probe.candidate, rfl⟩
  rw [jointNativeQueryCharge_eq_of_not_ots secretKey cache input hnot]
  simp only [ftsOpeningQueryReserve, FtsProbeSimulation.ftsHashQueryCharge, if_neg hfts, zero_mul, add_zero]

theorem jointNativeQueryCharge_le_three_atEncodingPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : EncodingPosition)
    (hat : AtEncodingPosition secretKey.parameter input position) :
    jointNativeQueryCharge secretKey cache input ≤ 3 := by
  rw [jointNativeQueryCharge_atEncodingPosition secretKey cache input position hat]
  exact TightEncoding.refinedStructuralEncodingQueryCharge_le_three secretKey cache input

theorem probEvent_sampled_jointPrimitive_le_nativeQueryCharge_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge jointNativeQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hfts := FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryCharge126 adversary q hq hqMax
  rw [← sampled_ftsOpeningQueryReserve_eq] at hfts
  apply (probEvent_sampled_jointPrimitive_le_prehit_charge_add_openings adversary).trans
  apply (add_le_add le_rfl (add_le_add
    (OtsProbeSimulation.probEvent_sampled_prehitFree_residual_le_directCharge_add_erasure adversary q hq hqMax) hfts)).trans_eq
  unfold jointNativeQueryCharge
  simp only [sampledQueryCharge_add]
  ring

theorem forgeAdvantage_le_nativeQueryCharge_add_remaining126
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge jointNativeQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((19 * q : Nat) : ENNReal) * ((2 ^ 133 : Nat) : ENNReal)⁻¹) :=
  (forgeAdvantage_le_sampled_jointPrimitive_add_refined_remaining126 adversary q hqPos hq hqMax).trans
    (add_le_add (probEvent_sampled_jointPrimitive_le_nativeQueryCharge_add_erasure adversary q hq hqMax) le_rfl)

end SphincsSecurity.Concrete
