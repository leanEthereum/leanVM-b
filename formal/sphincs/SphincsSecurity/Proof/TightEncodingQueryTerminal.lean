import SphincsSecurity.Proof.TightEncodingQueryBound
import SphincsSecurity.Proof.EncodingTerminalView

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_bad_or_viewedEncodingCollision_le_queryCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      expectedQueryCharge (TightEncoding.freshStructuralEncodingQueryCharge parameter)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let accountingKey : SecretKey := ⟨parameter, default, otsSecret, ftsSecret⟩
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
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [gameAfterSecretsWithViewTrace_verdictCache_projection]
    _ ≤ _ := TightEncoding.probEvent_bad_or_encodingBad_le_queryCharge
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) accountingKey

end SphincsSecurity.Concrete
