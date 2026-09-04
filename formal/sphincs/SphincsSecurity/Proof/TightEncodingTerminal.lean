import SphincsSecurity.Proof.TightEncodingSelectionLift
import SphincsSecurity.Proof.EncodingTerminalView

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_clean_viewedEncodingCollision_le_three_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (3 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let accountingKey : SecretKey := ⟨parameter, default, otsSecret, ftsSecret⟩
  calc
    _ ≤ Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          EncodingBad result.2.cache accountingKey |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      apply probEvent_mono
      intro result _ hevent
      refine ⟨hevent.1, ?_⟩
      exact (encodingBad_mk_root_iff parameter otsSecret ftsSecret result.2.cache
        result.1.1 default).mp hevent.2.encodingBad
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          ¬Bad parameter otsSecret ftsSecret result.2 ∧ EncodingBad result.2 accountingKey |
        (fun result => (result.1.2.2, result.2.cache)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          ¬Bad parameter otsSecret ftsSecret result.2 ∧ EncodingBad result.2 accountingKey |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [gameAfterSecretsWithViewTrace_verdictCache_projection]
    _ ≤ _ := TightEncoding.probEvent_clean_encodingBad_simulateQ_le
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) q hq accountingKey


theorem probEvent_bad_or_viewedEncodingCollision_le_three_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (3 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
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
    _ ≤ _ := TightEncoding.probEvent_bad_or_encodingBad_simulateQ_le
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) q hq accountingKey


end SphincsSecurity.Concrete
