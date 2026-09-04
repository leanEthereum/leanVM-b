import SphincsSecurity.Proof.ChargeStep
import SphincsSecurity.Proof.OneTimeEvents

/-!
# Probability decomposition after deterministic descent

The support-level forgery classification is lifted to event probabilities. The structural branch
is discharged immediately by the amortized `44`-unit cache bound, leaving one explicit terminal
event for the remaining probability arguments.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

def TerminalWitnessFor (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : Bool × QueryCache HashSpec) : Prop :=
  ∃ root forgery signingLog f digest,
    let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
    result.2.AgreesWithFn f
      ∧ SigningTranscript.Valid signingLog
      ∧ ¬ SigningTranscript.Contains signingLog forgery
      ∧ evalWithAnswerFn f
          (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
      ∧ Admissible digest
      ∧ event f result.2 secretKey signingLog forgery
          (digestIndex digest) (digestLeaves digest)

def TerminalWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret TerminalForgeryEvent

def FreshLayerOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      SettledForgedFreshLayerOpening f cache secretKey signingLog index leaves forgery.signature

def EncodingCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret fun f cache secretKey signingLog _ _ _ =>
    EncodingCollision f cache secretKey signingLog

def BackwardChainOpeningWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      SettledForgedBackwardChainOpening f cache secretKey signingLog index leaves
        forgery.signature

def MessageDigestCollisionWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      MessageDigestCollision f cache secretKey signingLog forgery ∧
        FewTimeLeak f cache secretKey signingLog index leaves

def ProperFewTimeLeakWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog _ index leaves =>
      ProperFewTimeLeak f cache secretKey signingLog index leaves

def UncoveredFtsSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Bool × QueryCache HashSpec → Prop :=
  TerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      UncoveredFtsSecret f cache secretKey signingLog index leaves forgery.signature.ftsSecret

noncomputable instance (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DecidablePred (TerminalWitness parameter otsSecret ftsSecret) :=
  fun result => Classical.propDecidable (TerminalWitness parameter otsSecret ftsSecret result)

theorem terminalWitness_cases (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : Bool × QueryCache HashSpec)
    (hwitness : TerminalWitness parameter otsSecret ftsSecret result) :
    FreshLayerOpeningWitness parameter otsSecret ftsSecret result
      ∨ EncodingCollisionWitness parameter otsSecret ftsSecret result
      ∨ BackwardChainOpeningWitness parameter otsSecret ftsSecret result
      ∨ MessageDigestCollisionWitness parameter otsSecret ftsSecret result
      ∨ ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
      ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result := by
  obtain ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, hterminal⟩ := hwitness
  rcases hterminal with hfresh | hencoding | hbackward | hmessage | hfewTime | huncovered
  · exact Or.inl ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains,
      hdigest, hadmissible, hfresh⟩
  · exact Or.inr (Or.inl ⟨root, forgery, signingLog, f, digest, hf, hvalid,
      hnotContains, hdigest, hadmissible, hencoding⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨root, forgery, signingLog, f, digest, hf, hvalid,
      hnotContains, hdigest, hadmissible, hbackward⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨root, forgery, signingLog, f, digest, hf,
      hvalid, hnotContains, hdigest, hadmissible, hmessage⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨root, forgery, signingLog, f,
      digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfewTime⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨root, forgery, signingLog, f,
      digest, hf, hvalid, hnotContains, hdigest, hadmissible, huncovered⟩))))

theorem probEvent_terminalWitness_le (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (oa : ProbComp (Bool × QueryCache HashSpec)) :
    Pr[TerminalWitness parameter otsSecret ftsSecret | oa] ≤
      Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | oa] +
      (Pr[EncodingCollisionWitness parameter otsSecret ftsSecret | oa] +
      (Pr[BackwardChainOpeningWitness parameter otsSecret ftsSecret | oa] +
      (Pr[MessageDigestCollisionWitness parameter otsSecret ftsSecret | oa] +
      (Pr[ProperFewTimeLeakWitness parameter otsSecret ftsSecret | oa] +
        Pr[UncoveredFtsSecretWitness parameter otsSecret ftsSecret | oa])))) := by
  classical
  calc
    _ ≤ Pr[fun result =>
        FreshLayerOpeningWitness parameter otsSecret ftsSecret result
          ∨ EncodingCollisionWitness parameter otsSecret ftsSecret result
          ∨ BackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ MessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result | oa] := by
      apply probEvent_mono
      intro result _ hwitness
      exact terminalWitness_cases parameter otsSecret ftsSecret result hwitness
    _ ≤ Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | oa] +
        Pr[fun result => EncodingCollisionWitness parameter otsSecret ftsSecret result
          ∨ BackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ MessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result | oa] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | oa] +
        (Pr[EncodingCollisionWitness parameter otsSecret ftsSecret | oa] +
        Pr[fun result => BackwardChainOpeningWitness parameter otsSecret ftsSecret result
          ∨ MessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result | oa]) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | oa] +
        (Pr[EncodingCollisionWitness parameter otsSecret ftsSecret | oa] +
        (Pr[BackwardChainOpeningWitness parameter otsSecret ftsSecret | oa] +
        Pr[fun result => MessageDigestCollisionWitness parameter otsSecret ftsSecret result
          ∨ ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result | oa])) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | oa] +
        (Pr[EncodingCollisionWitness parameter otsSecret ftsSecret | oa] +
        (Pr[BackwardChainOpeningWitness parameter otsSecret ftsSecret | oa] +
        (Pr[MessageDigestCollisionWitness parameter otsSecret ftsSecret | oa] +
        Pr[fun result => ProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∨ UncoveredFtsSecretWitness parameter otsSecret ftsSecret result | oa]))) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ _ := by
      gcongr
      exact probEvent_or_le _ _ _

theorem winning_implies_bad_or_terminal (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : Bool × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅))
    (hwin : result.1 = true) :
    Bad parameter otsSecret ftsSecret result.2
      ∨ TerminalWitness parameter otsSecret ftsSecret result := by
  rcases result with ⟨verdict, finalCache⟩
  simp only at hwin
  subst verdict
  rcases winning_support_terminal_classify adversary parameter otsSecret ftsSecret
      finalCache hresult with hbad | hwitness
  · exact Or.inl hbad
  · exact Or.inr hwitness

theorem probEvent_win_le_bad_add_terminal (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[fun result => Bad parameter otsSecret ftsSecret result.2 |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] +
      Pr[TerminalWitness parameter otsSecret ftsSecret |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
  let run := (simulateQ romImpl
    (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅
  calc
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] =
        Pr[fun result => result.1 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2
          ∨ TerminalWitness parameter otsSecret ftsSecret result | run] := by
      apply probEvent_mono
      intro result hresult hwin
      exact winning_implies_bad_or_terminal adversary parameter otsSecret ftsSecret
        result hresult hwin
    _ ≤ _ := probEvent_or_le _ _ _

theorem probEvent_win_le_structural_add_terminal (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      Pr[TerminalWitness parameter otsSecret ftsSecret |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
  calc
    _ ≤ _ := probEvent_win_le_bad_add_terminal adversary parameter otsSecret ftsSecret
    _ ≤ _ := by
      gcongr
      exact probEvent_bad_gameAfterSecrets_le adversary parameter otsSecret ftsSecret q hq

theorem probEvent_win_le_structural_add_terminal_cases (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    let run := (simulateQ romImpl
      (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[FreshLayerOpeningWitness parameter otsSecret ftsSecret | run] +
      (Pr[EncodingCollisionWitness parameter otsSecret ftsSecret | run] +
      (Pr[BackwardChainOpeningWitness parameter otsSecret ftsSecret | run] +
      (Pr[MessageDigestCollisionWitness parameter otsSecret ftsSecret | run] +
      (Pr[ProperFewTimeLeakWitness parameter otsSecret ftsSecret | run] +
        Pr[UncoveredFtsSecretWitness parameter otsSecret ftsSecret | run]))))) := by
  dsimp only
  let run := (simulateQ romImpl
    (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅
  calc
    _ ≤ ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[TerminalWitness parameter otsSecret ftsSecret | run] :=
      probEvent_win_le_structural_add_terminal adversary parameter otsSecret ftsSecret q hq
    _ ≤ _ := by
      gcongr
      exact probEvent_terminalWitness_le parameter otsSecret ftsSecret run

end Concrete

end SphincsSecurity
