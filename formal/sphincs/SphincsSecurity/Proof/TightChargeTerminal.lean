import SphincsSecurity.Proof.TightChargeStep
import SphincsSecurity.Proof.TerminalView

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_bad_gameAfterSecretsWithViewTrace_le_two_mul (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((2 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun result : Bool × QueryCache HashSpec =>
          Bad parameter otsSecret ftsSecret result.2 |
        (fun result => (result.1.2.2, result.2.cache)) <$>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => Bad parameter otsSecret ftsSecret result.2 |
        (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅] := by
      rw [gameAfterSecretsWithViewTrace_verdictCache_projection]
    _ ≤ _ := probEvent_bad_gameAfterSecrets_le_two_mul adversary parameter otsSecret ftsSecret q hq


end SphincsSecurity.Concrete
