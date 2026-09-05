import SphincsSecurity.Proof.TightEncodingSettledCharge
import SphincsSecurity.Proof.TightEncodingQueryBound
import SphincsSecurity.Proof.EncodingTerminalView

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

namespace TightEncoding

theorem expected_encodingSelectionAdaptivePotential_le_refined_queryCharge
    {α : Type} (computation : OracleComp OracleWorld α)
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
        encodingSelectionAdaptivePotential result.2 secretKey) ≤
      encodingSelectionAdaptivePotential cache secretKey +
        expectedQueryCharge (refinedStructuralEncodingQueryCharge secretKey)
          computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  refine expected_potential_simulateQ_le_queryCharge
    (fun cache => encodingSelectionAdaptivePotential cache secretKey) _ ?_
    computation cache hfinite
  apply expected_potential_romImpl_le_charge
  intro before hbefore input hfresh
  simp_rw [encodingSelectionAdaptivePotential_eq (finite_cacheQuery hbefore input _)]
  rw [encodingSelectionAdaptivePotential_eq hbefore]
  exact uniform_encodingSelectionTotalPotential_cacheQuery_le_refined_charge hbefore hfresh

theorem probEvent_bad_or_encodingBad_le_refined_queryCharge
    {α : Type} (computation : OracleComp OracleWorld α) (secretKey : SecretKey) :
    Pr[fun result => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∨
        EncodingBad result.2 secretKey | (simulateQ romImpl computation).run ∅] ≤
      expectedQueryCharge (refinedStructuralEncodingQueryCharge secretKey)
        computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  exact (probEvent_bad_or_encodingBad_le_expectedPotential computation secretKey).trans
    ((expected_encodingSelectionAdaptivePotential_le_refined_queryCharge computation secretKey ∅
      finite_empty).trans_eq (by rw [encodingSelectionAdaptivePotential_empty, zero_add]))

end TightEncoding

def primitiveAccountingKey (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : SecretKey :=
  ⟨parameter, default, otsSecret, ftsSecret⟩

theorem probEvent_bad_or_viewedEncodingCollision_le_refined_queryCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      expectedQueryCharge
        (TightEncoding.refinedStructuralEncodingQueryCharge (primitiveAccountingKey parameter otsSecret ftsSecret))
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  calc
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
          EncodingBad result.2.cache accountingKey |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      apply probEvent_mono
      intro result _ hevent
      rcases hevent with hbad | hencoding
      · exact Or.inl hbad
      · exact Or.inr ((encodingBad_mk_root_iff parameter otsSecret ftsSecret result.2.cache
          result.1.1 default).mp hencoding.encodingBad)
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          Bad parameter otsSecret ftsSecret result.2 ∨ EncodingBad result.2 accountingKey |
        (fun result => (result.1.2.2, result.2.cache)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          Bad parameter otsSecret ftsSecret result.2 ∨ EncodingBad result.2 accountingKey |
        (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [gameAfterSecretsWithViewTrace_verdictCache_projection]
    _ ≤ _ := TightEncoding.probEvent_bad_or_encodingBad_le_refined_queryCharge
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) accountingKey

end SphincsSecurity.Concrete
