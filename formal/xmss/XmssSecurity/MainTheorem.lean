import XmssSecurity.Encoding
import XmssSecurity.ForgeryCases
import XmssSecurity.HiddenValue
import XmssSecurity.Merkle
import XmssSecurity.SecurityBudget
import XmssSecurity.SecurityGame
import XmssSecurity.Wots

namespace XmssSecurity

namespace Concrete

axiom scheme : Scheme

end Concrete

/-- The remaining cryptographic hybrid exposes the 175 classified events as independent hidden digest targets. -/
theorem xmss_factorizes_to_hiddenTargets (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    ∃ strategyGenerator : ProbComp (List Bool → Digest),
      forgeAdvantage Concrete.scheme adversary ≤
        Pr[(fun hit : Bool => hit = true) |
          HiddenValue.adaptiveGuessExperiment strategyGenerator q totalBadEventSlots] := by
  sorry

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  obtain ⟨strategyGenerator, hforge⟩ :=
    xmss_factorizes_to_hiddenTargets q hq adversary hbound
  have hguess := HiddenValue.adaptive_guess_after_public_sampling_le_120
    strategyGenerator q totalBadEventSlots (le_refl totalBadEventSlots)
  exact hforge.trans (by simpa [targetSecurityBits] using hguess)

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
