import SphincsSecurity.Proof.TightEncodingTerminal
import SphincsSecurity.Proof.FewTimeHonestLeakBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def jointStructuralEncodingEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  Bad parameter otsSecret ftsSecret result.2.cache ∨
    ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result

theorem probEvent_win_le_joint_terminal_cases (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[jointStructuralEncodingEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
      (Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret | run] +
        Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run]))) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let joint := jointStructuralEncodingEvent parameter otsSecret ftsSecret
  let opening := cleanOtsOpeningEvent parameter otsSecret ftsSecret
  let message := cleanMessageEvent parameter otsSecret ftsSecret
  let proper := ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret
  let uncovered := cleanUncoveredEvent parameter otsSecret ftsSecret
  calc
    _ = Pr[fun result => result.1.2.2 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput,
        ← gameAfterSecretsWithViewTrace_verdictCache_projection adversary parameter otsSecret
          ftsSecret, probEvent_map]
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => joint result ∨ opening result ∨ message result ∨ proper result ∨
        uncovered result | run] := by
      apply probEvent_mono
      intro result hresult hwin
      rcases gameAfterSecretsWithViewTrace_winning_honestLeakTerminal_classify adversary
          parameter otsSecret ftsSecret result hresult hwin with hbad | hterminal
      · exact Or.inl (Or.inl hbad)
      · by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
        · exact Or.inl (Or.inl hbad)
        · rcases viewedWinningHonestLeakTerminalWitness_cases parameter otsSecret ftsSecret
            result hterminal with hfresh | hencoding | hbackward | hmessage | hproper | huncovered
          · exact Or.inr (Or.inl (Or.inl ⟨⟨hbad, hwin⟩, hfresh⟩))
          · exact Or.inl (Or.inr hencoding)
          · exact Or.inr (Or.inl (Or.inr ⟨⟨hbad, hwin⟩, hbackward⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hbad, hmessage⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hproper)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hbad, huncovered⟩)))
    _ ≤ Pr[joint | run] +
        Pr[fun result => opening result ∨ message result ∨ proper result ∨ uncovered result |
          run] := probEvent_or_le _ _ _
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ Pr[opening | run] +
            Pr[fun result => message result ∨ proper result ∨ uncovered result | run] :=
          probEvent_or_le _ _ _
        _ ≤ _ := by
          apply add_le_add le_rfl
          calc
            _ ≤ Pr[message | run] +
                Pr[fun result => proper result ∨ uncovered result | run] := probEvent_or_le _ _ _
            _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)

theorem probEvent_win_le_joint_reserved_add_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
        Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run])) := by
  dsimp only
  have hjoint := probEvent_bad_or_viewedEncodingCollision_le_three_mul adversary parameter
    otsSecret ftsSecret q (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts)
  have hforest := probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_three_mul_inv131
    adversary q hqPos hq hqMax parameter hparameter otsSecret hots ftsSecret hfts
  have hcard : Fintype.card Digest = 2 ^ 128 := by
    simpa only [digestBits] using (show Fintype.card Digest = 2 ^ digestBits by simp)
  rw [hcard] at hjoint
  have hcast : (3 * q : ℝ≥0∞) = ((3 * q : Nat) : ℝ≥0∞) := by push_cast; rfl
  rw [hcast] at hjoint
  refine (probEvent_win_le_joint_terminal_cases adversary parameter otsSecret ftsSecret).trans ?_
  calc
    _ ≤ ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
        (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret |
            gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] +
        (Pr[cleanMessageEvent parameter otsSecret ftsSecret |
            gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] +
        (((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
          Pr[cleanUncoveredEvent parameter otsSecret ftsSecret |
            gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret]))) :=
      add_le_add hjoint (add_le_add le_rfl (add_le_add le_rfl (add_le_add hforest le_rfl)))
    _ = _ := by ac_rfl

end SphincsSecurity.Concrete
