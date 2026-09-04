import SphincsSecurity.Proof.FewTimeRawTargetFresh
import SphincsSecurity.Proof.OtsProbeGroupedTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
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

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_three_mul_inv131
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ q * rawTargetOriginUnionBound signatureLimit q +
        ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q :=
      probEvent_gameAfterSecretsWithViewTrace_honest_leak_le adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q := by
      push_cast
      ring
    _ ≤ _ := by
      apply mul_le_mul'
      · exact_mod_cast (show 2 * q + 1 ≤ 3 * q by omega)
      · exact rawTargetOriginUnionBound_le_inv131 le_rfl hqMax

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

theorem probEvent_win_le_grouped_honestLeak_terminal_cases (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
      (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
        Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run])))) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let opening := cleanOtsOpeningEvent parameter otsSecret ftsSecret
  let encoding := cleanEncodingEvent parameter otsSecret ftsSecret
  let message := cleanMessageEvent parameter otsSecret ftsSecret
  let proper := fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
  let uncovered := cleanUncoveredEvent parameter otsSecret ftsSecret
  calc
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] =
        Pr[fun result => result.1.2.2 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput,
        ← gameAfterSecretsWithViewTrace_verdictCache_projection adversary parameter otsSecret
          ftsSecret, probEvent_map]
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
          opening result ∨ encoding result ∨ message result ∨ proper result ∨
            uncovered result | run] := by
      apply probEvent_mono
      intro result hresult hwin
      rcases gameAfterSecretsWithViewTrace_winning_honestLeakTerminal_classify adversary parameter
          otsSecret ftsSecret result hresult hwin with hbad | hterminal
      · exact Or.inl hbad
      · by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
        · exact Or.inl hbad
        · rcases viewedWinningHonestLeakTerminalWitness_cases parameter otsSecret ftsSecret result
            hterminal with hfresh | hencoding | hbackward | hmessage | hproper | huncovered
          · exact Or.inr (Or.inl (Or.inl ⟨⟨hbad, hwin⟩, hfresh⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hbad, hencoding⟩))
          · exact Or.inr (Or.inl (Or.inr ⟨⟨hbad, hwin⟩, hbackward⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hmessage⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hproper⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbad, huncovered⟩))))
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        Pr[fun result => opening result ∨ encoding result ∨ message result ∨
          proper result ∨ uncovered result | run] := probEvent_or_le _ _ _
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        (Pr[opening | run] +
        (Pr[encoding | run] +
        (Pr[message | run] +
        (Pr[proper | run] + Pr[uncovered | run])))) := by
      gcongr
      calc
        _ ≤ Pr[opening | run] +
            Pr[fun result => encoding result ∨ message result ∨ proper result ∨
              uncovered result | run] := probEvent_or_le _ _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ Pr[encoding | run] +
                Pr[fun result => message result ∨ proper result ∨ uncovered result | run] :=
              probEvent_or_le _ _ _
            _ ≤ _ := by
              gcongr
              calc
                _ ≤ Pr[message | run] +
                    Pr[fun result => proper result ∨ uncovered result | run] :=
                  probEvent_or_le _ _ _
                _ ≤ _ := by
                  gcongr
                  exact probEvent_or_le _ _ _
    _ = _ := by
      rfl

end SphincsSecurity.Concrete
