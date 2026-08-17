import XmssSecurity.CappedUnifiedMainTheorem

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

inductive UnifiedSecurityIndex where
  | chainValue (index : CappedChain.GlobalChainValueIndex)
  | signingRandomness (index : Epoch × Fin signingAttemptLimit)
  | encodingDigest (index : Epoch × Fin signingAttemptLimit)
  | leafDigest (epoch : Epoch)
  | merkleDigest (index : MerkleLevel × MerkleNode)
deriving DecidableEq, Fintype

noncomputable def HasCappedUnifiedTwoLaneReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) : Prop :=
  ∃ (Result : Type)
      (computation : OracleComp
        (RevealProbeOracleSimulation.World UnifiedSecurityIndex) Result),
    computation.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery
        (2 * q) ∧
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningUnifiedBadEventOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment computation]

theorem unifiedTwoLaneReduction_probability_le
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : HasCappedUnifiedTwoLaneReduction q adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningUnifiedBadEventOccurs execution.2 execution.1 |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  obtain ⟨Result, computation, hbound, hprobability⟩ := hreduction
  refine hprobability.trans ?_
  refine (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
    (2 * q) computation hbound).trans_eq ?_
  push_cast
  simp only [div_eq_mul_inv]
  ac_rfl

theorem two_digest_terms_le_127 (q : Nat) :
    2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) =
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  have hbits : digestBits = 1 + 127 := by decide
  have hzero : ((2 ^ 1 : Nat) : ENNReal) ≠ 0 := by positivity
  have htop : ((2 ^ 1 : Nat) : ENNReal) ≠ ∞ := by simp
  rw [show (2 : ENNReal) = ((2 ^ 1 : Nat) : ENNReal) by norm_num]
  rw [hbits, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ 1 : Nat) : ENNReal) *
        ((q : ENNReal) *
          (((2 ^ 1 : Nat) : ENNReal)⁻¹ *
            ((2 ^ 127 : Nat) : ENNReal)⁻¹)) =
      (((2 ^ 1 : Nat) : ENNReal) *
        ((2 ^ 1 : Nat) : ENNReal)⁻¹) *
        ((q : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
      ac_rfl
    _ = (q : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]
    _ = (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
      rw [div_eq_mul_inv]

theorem capped_xmss_forgeAdvantage_le_127_of_unifiedTwoLaneReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : HasCappedUnifiedTwoLaneReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  exact (capped_forgeAdvantage_le_winningUnifiedBadEvent adversary).trans
    ((unifiedTwoLaneReduction_probability_le q adversary hreduction).trans_eq
      (two_digest_terms_le_127 q))

def HasCappedUnifiedTwoLaneReductions : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.cappedScheme),
    HasHashQueryBound Concrete.cappedScheme adversary q →
      HasCappedUnifiedTwoLaneReduction q adversary

theorem xmss_has_127_bits_of_classical_security_of_unifiedTwoLaneReductions
    (hreductions : HasCappedUnifiedTwoLaneReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 127 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_127_of_unifiedTwoLaneReduction q
    adversary (hreductions q adversary hbound)

theorem HasClassicalSecurityBits.mono
    {scheme : Scheme} {small large : Nat}
    (hsecurity : HasClassicalSecurityBits scheme large)
    (hbits : small ≤ large) :
    HasClassicalSecurityBits scheme small := by
  intro q hq
  refine (hsecurity q hq).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast Nat.pow_le_pow_right (by omega) hbits

theorem xmss_has_126_bits_of_classical_security_of_unifiedTwoLaneReductions
    (hreductions : HasCappedUnifiedTwoLaneReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 126 :=
  (xmss_has_127_bits_of_classical_security_of_unifiedTwoLaneReductions
    hreductions).mono (by omega)

theorem xmss_has_125_bits_of_classical_security_of_unifiedTwoLaneReductions
    (hreductions : HasCappedUnifiedTwoLaneReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 :=
  (xmss_has_127_bits_of_classical_security_of_unifiedTwoLaneReductions
    hreductions).mono (by omega)

theorem xmss_has_125_126_127_bits_of_classical_security_of_unifiedTwoLaneReductions
    (hreductions : HasCappedUnifiedTwoLaneReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 ∧
      HasClassicalSecurityBits Concrete.cappedScheme 126 ∧
      HasClassicalSecurityBits Concrete.cappedScheme 127 :=
  ⟨xmss_has_125_bits_of_classical_security_of_unifiedTwoLaneReductions
      hreductions,
    xmss_has_126_bits_of_classical_security_of_unifiedTwoLaneReductions
      hreductions,
    xmss_has_127_bits_of_classical_security_of_unifiedTwoLaneReductions
      hreductions⟩

end XmssSecurity
