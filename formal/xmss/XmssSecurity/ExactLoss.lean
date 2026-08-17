import XmssSecurity.LossDecomposition
import XmssSecurity.CappedGlobalChainTable
import XmssSecurity.CappedVerifierQueryFloor
import XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

inductive UnifiedDigestIndex where
  | encodingDigest (index : Epoch × Fin signingAttemptLimit)
  | chainValue (index : CappedChain.GlobalChainValueIndex)
  | leafDigest (epoch : Epoch)
  | merkleDigest (index : MerkleLevel × MerkleNode)
deriving DecidableEq, Fintype

noncomputable def HasUnifiedDigestReduction
    (q : Nat) (adversary : XmssAdversary) : Prop :=
  ∃ (Result : Type)
      (computation : OracleComp
        (RevealProbeOracleSimulation.World UnifiedDigestIndex) Result),
    computation.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery
        (q + numChains) ∧
      Pr[WinningDigestBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment computation]

theorem unifiedDigestReduction_probability_le
    (q : Nat) (adversary : XmssAdversary)
    (hreduction : HasUnifiedDigestReduction q adversary) :
    Pr[WinningDigestBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  obtain ⟨Result, computation, hbound, hprobability⟩ := hreduction
  exact hprobability.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
      (q + numChains) computation hbound)

theorem exact_loss_budget_le_127
    (q : Nat) (hq : verificationChainHashes + 1 ≤ q) :
    (q : ENNReal) / ((2 ^ 137 : Nat) : ENNReal) +
        ((q + numChains : Nat) : ENNReal) /
          ((2 ^ digestBits : Nat) : ENNReal) ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  rw [verificationChainHashes_eq] at hq
  norm_num at hq
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  norm_num [digestBits, numChains]
  have hqreal : (100 : Real) ≤ (q : Real) := by exact_mod_cast hq
  field_simp
  ring_nf at ⊢
  linarith [hqreal]

theorem xmssForgeAdvantage_le_127_of_unifiedDigestReduction
    (q : Nat) (adversary : XmssAdversary)
    (hbound : XmssHasHashQueryBound adversary q)
    (hreduction : HasUnifiedDigestReduction q adversary) :
    xmssForgeAdvantage adversary ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.cappedScheme adversary ≤
        Pr[WinningEncodingPrehitOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[WinningDigestBadEventOccurs |
          cappedDetailedGameWithEncodingTrace adversary] :=
      capped_forgeAdvantage_le_encodingPrehit_add_digestBad adversary
    _ ≤ (lifetime : ENNReal) *
          ((signingAttemptLimit : ENNReal) * (q : ENNReal) *
            ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) +
        ((q + numChains : Nat) : ENNReal) /
          ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add (capped_encodingPrehit_probability_le_exact q adversary hbound)
        (unifiedDigestReduction_probability_le q adversary hreduction)
    _ = (q : ENNReal) / ((2 ^ 137 : Nat) : ENNReal) +
        ((q + numChains : Nat) : ENNReal) /
          ((2 ^ digestBits : Nat) : ENNReal) := by
      rw [capped_encodingPrehit_budget_eq_137]
    _ ≤ _ := exact_loss_budget_le_127 q
      (hashQueryBound_at_least_verificationQueries adversary q hbound)

def HasUnifiedDigestReductions : Prop :=
  ∀ (q : Nat) (adversary : XmssAdversary),
    XmssHasHashQueryBound adversary q →
      HasUnifiedDigestReduction q adversary

theorem xmss_has_127_bits_of_classical_security_of_unifiedDigestReductions
    (hreductions : HasUnifiedDigestReductions) :
    XmssHasClassicalSecurityBits 127 := by
  change HasClassicalSecurityBits xmssScheme 127
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmssForgeAdvantage_le_127_of_unifiedDigestReduction q adversary
    hbound (hreductions q adversary hbound)

end XmssSecurity
