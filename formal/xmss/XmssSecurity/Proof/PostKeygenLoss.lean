import XmssSecurity.Proof.CappedExactFirstLaneBoundedProof

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The strengthened first-lane estimate needed when honest key-generation queries are free. -/
def HasPostKeygenExactFirstLaneBound
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[WinningExactFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)

theorem postKeygenHashQueryBound_at_least_verificationQueries
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (key : PublicKey × SecretKey) (hkey : key ∈ support Concrete.scheme.keygen) :
    verificationChainHashes + 1 ≤ q := by
  have hafter :=
    (hasPostKeygenHashQueryBound_iff_detailedGameAfterKeygen
      Concrete.scheme adversary q).mp hpost key hkey
  unfold detailedGameAfterKeygen at hafter
  obtain ⟨adversaryResult, hfinish⟩ :=
    ExactQueryCount.exists_queryBoundP_continuation hafter
  have hverify :
      (Concrete.scheme.verify key.1 adversaryResult.1.epoch
        adversaryResult.1.message adversaryResult.1.signature)
          |>.IsQueryBoundP (· matches .inr _) q :=
    OracleComp.IsQueryBoundP.of_bind_left hfinish
  exact Concrete.verify_hashQueryBound_at_least_verificationWork
    key.1 adversaryResult.1.epoch adversaryResult.1.message
      adversaryResult.1.signature q hverify

theorem hasPostKeygenSecondLaneBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q) :
    Pr[WinningSecondLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have htotal := hasHashQueryBound_of_postKeygen adversary q hpost
  have hsecond := hasSecondLaneBound_of_hashQueryBound
    (treeHashQueryCount treeHeight + q) adversary htotal
  simpa [HasSecondLaneBound] using hsecond

theorem postKeygen_two_lane_loss_budget_le_127 (q : Nat) :
    (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  rw [← two_mul]
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  norm_num [digestBits]
  ring

theorem forgeAdvantage_le_postKeygen_127
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hpost : HasPostKeygenHashQueryBound Concrete.scheme adversary q)
    (hfirst : HasPostKeygenExactFirstLaneBound q adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.scheme adversary ≤
        Pr[WinningExactFirstLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[WinningSecondLaneBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] :=
      capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary
    _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add hfirst (hasPostKeygenSecondLaneBound q adversary hpost)
    _ ≤ _ := postKeygen_two_lane_loss_budget_le_127 q

def HasPostKeygenExactFirstLaneBounds : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.scheme),
    HasPostKeygenHashQueryBound Concrete.scheme adversary q →
      HasPostKeygenExactFirstLaneBound q adversary

theorem concreteScheme_has_postKeygen_127_of_firstLaneBounds
    (hfirst : HasPostKeygenExactFirstLaneBounds) :
    HasPostKeygenClassicalSecurityBits Concrete.scheme 127 := by
  intro q _hq
  unfold postKeygenForgeAtMost
  refine iSup_le fun adversary => iSup_le fun hpost => ?_
  exact forgeAdvantage_le_postKeygen_127 q adversary hpost
    (hfirst q adversary hpost)

end XmssSecurity
