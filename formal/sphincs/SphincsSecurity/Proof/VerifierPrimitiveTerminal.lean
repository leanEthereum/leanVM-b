import SphincsSecurity.Proof.VerifierStructuralCollision
import SphincsSecurity.Proof.JointPrimitiveTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def verifierPrimitiveEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧
    (ViewedVerifierStructuralCollision parameter otsSecret ftsSecret result ∨
      ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∨
      ViewedWinningFreshLayerOpeningWitness parameter otsSecret ftsSecret result ∨
      ViewedWinningBackwardChainOpeningWitness parameter otsSecret ftsSecret result ∨
      ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result)

theorem verifierPrimitiveEvent_implies_jointPrimitiveEvent
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hprimitive : verifierPrimitiveEvent parameter otsSecret ftsSecret result) :
    jointPrimitiveEvent parameter otsSecret ftsSecret result := by
  obtain ⟨hwin, hevent⟩ := hprimitive
  refine ⟨hwin, ?_⟩
  by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
  · exact Or.inl hbad
  rcases hevent with hcollision | hencoding | hfresh | hbackward | huncovered
  · exact (hbad hcollision.bad).elim
  · exact Or.inr (Or.inl hencoding)
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨⟨hbad, hwin⟩, hfresh⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨⟨hbad, hwin⟩, hbackward⟩)))
  · exact Or.inr (Or.inr (Or.inr ⟨hbad, huncovered⟩))

theorem probEvent_win_le_verifierPrimitive_add_message_add_forest (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[verifierPrimitiveEvent parameter otsSecret ftsSecret | run] +
      (Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret | run] +
        Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret | run]) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let primitive := verifierPrimitiveEvent parameter otsSecret ftsSecret
  let message := ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret
  let forest := ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret
  calc
    _ = Pr[fun result => result.1.2.2 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput,
        ← gameAfterSecretsWithViewTrace_verdictCache_projection adversary parameter otsSecret
          ftsSecret, probEvent_map]
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => primitive result ∨ message result ∨ forest result | run] := by
      apply probEvent_mono
      intro result hresult hwin
      rcases gameAfterSecretsWithViewTrace_winning_usedCollision_classify adversary
        parameter otsSecret ftsSecret result hresult hwin with hcollision | hterminal
      · exact Or.inl ⟨hwin, Or.inl hcollision⟩
      · rcases viewedWinningHonestLeakTerminalWitness_cases parameter otsSecret ftsSecret
          result hterminal with hfresh | hencoding | hbackward | hmessage | hforest | huncovered
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inl hfresh))⟩
        · exact Or.inl ⟨hwin, Or.inr (Or.inl hencoding)⟩
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inr (Or.inl hbackward)))⟩
        · exact Or.inr (Or.inl hmessage)
        · exact Or.inr (Or.inr hforest)
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inr (Or.inr huncovered)))⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add le_rfl (probEvent_or_le _ _ _))

end SphincsSecurity.Concrete
