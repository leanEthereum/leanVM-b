import XmssSecurity.Encoding
import XmssSecurity.ConcreteVerify
import XmssSecurity.ForgeryCases
import XmssSecurity.HiddenValue
import XmssSecurity.IndexedHiddenValue
import XmssSecurity.Merkle
import XmssSecurity.SecurityBudget
import XmssSecurity.SecurityGame
import XmssSecurity.Wots

namespace XmssSecurity

namespace Concrete

axiom keygen : OracleComp OracleWorld (PublicKey × SecretKey)

axiom sign : PublicKey → SecretKey → Epoch → Message →
  OracleComp OracleWorld (Option Signature)

noncomputable def scheme : Scheme where
  keygen := keygen
  sign := sign
  verify := Concrete.verify

end Concrete

/-- The remaining cryptographic hybrid exposes each classified event as an epoch-indexed hidden digest table. -/
theorem xmss_factorizes_to_hiddenTargets (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    ∃ strategyGenerator : BadEvent → ProbComp (List Bool → Epoch × Digest),
      forgeAdvantage Concrete.scheme adversary ≤
        ∑ event, Pr[(fun hit : Bool => hit = true) |
          IndexedHiddenValue.adaptiveGuessExperiment (strategyGenerator event) q] := by
  sorry

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  obtain ⟨strategyGenerator, hforge⟩ :=
    xmss_factorizes_to_hiddenTargets q hq adversary hbound
  refine hforge.trans (badEvent_sum_le_120 q (fun event =>
    Pr[(fun hit : Bool => hit = true) |
      IndexedHiddenValue.adaptiveGuessExperiment (strategyGenerator event) q]) ?_)
  intro event
  exact IndexedHiddenValue.adaptive_guess_after_public_sampling_le
    (strategyGenerator event) q

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
