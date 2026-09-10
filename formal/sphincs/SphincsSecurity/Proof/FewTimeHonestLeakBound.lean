import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeRawTargetFresh

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * rawTargetOriginUnionBound signatureLimit q +
        ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q := by
  classical
  calc
    _ ≤ Pr[fun result =>
        (ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result) ∨
        (ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result) |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
        apply probEvent_mono
        intro result _ hproper
        by_cases hfresh : VerifierFreshTarget parameter result
        · exact Or.inr ⟨hproper, hfresh⟩
        · exact Or.inl ⟨hproper, hfresh⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_gameAfterSecretsWithViewTrace_nonfresh_honest_leak_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts)
      (probEvent_gameAfterSecretsWithViewTrace_fresh_honest_leak_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts))

theorem viewedWinningHonestLeakTerminalWitness_cases (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hwitness : ViewedWinningTerminalWitnessFor parameter otsSecret ftsSecret HonestLeakTerminalForgeryEvent result) :
    ViewedWinningFreshLayerOpeningWitness parameter otsSecret ftsSecret result
      ∨ ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
      ∨ ViewedWinningBackwardChainOpeningWitness parameter otsSecret ftsSecret result
      ∨ ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result
      ∨ ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
      ∨ ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hverified,
    hterminal⟩ := hwitness
  rcases hterminal with hfresh | hencoding | hbackward | hmessage | hfewTime | huncovered
  · exact Or.inl ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hverified, hfresh⟩
  · exact Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hencoding⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hverified, hbackward⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hmessage⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfewTime⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, huncovered⟩))))

end SphincsSecurity.Concrete
