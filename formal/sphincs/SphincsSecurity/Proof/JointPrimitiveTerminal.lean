import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeHonestLeakBound
import SphincsSecurity.Proof.OtsProbeGroupedTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def jointPrimitiveEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧
    (Bad parameter otsSecret ftsSecret result.2.cache ∨
      ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∨
      cleanOtsOpeningEvent parameter otsSecret ftsSecret result ∨
      cleanUncoveredEvent parameter otsSecret ftsSecret result)

theorem probEvent_win_le_jointPrimitive_add_message_add_forest (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[jointPrimitiveEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
        Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret | run]) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let primitive := jointPrimitiveEvent parameter otsSecret ftsSecret
  let message := cleanMessageEvent parameter otsSecret ftsSecret
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
      by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
      · exact Or.inl ⟨hwin, Or.inl hbad⟩
      · have hterminal :=
          (gameAfterSecretsWithViewTrace_winning_honestLeakTerminal_classify adversary
            parameter otsSecret ftsSecret result hresult hwin).resolve_left hbad
        rcases viewedWinningHonestLeakTerminalWitness_cases parameter otsSecret ftsSecret
          result hterminal with hfresh | hencoding | hbackward | hmessage | hforest | huncovered
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inl (Or.inl ⟨⟨hbad, hwin⟩, hfresh⟩)))⟩
        · exact Or.inl ⟨hwin, Or.inr (Or.inl hencoding)⟩
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inl (Or.inr ⟨⟨hbad, hwin⟩, hbackward⟩)))⟩
        · exact Or.inr (Or.inl ⟨hbad, hmessage⟩)
        · exact Or.inr (Or.inr hforest)
        · exact Or.inl ⟨hwin, Or.inr (Or.inr (Or.inr ⟨hbad, huncovered⟩))⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add le_rfl (probEvent_or_le _ _ _))

end SphincsSecurity.Concrete
