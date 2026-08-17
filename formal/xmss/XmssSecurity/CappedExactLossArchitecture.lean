import XmssSecurity.CappedUnifiedTwoLaneReduction
import XmssSecurity.CappedVerifierQueryFloor

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)

def WinningEncodingPrehitOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
    execution.2.1.2.HasEncodingInputPrehit execution.1.secretKey

def WinningDigestBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  (WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2.2 = true) ∨
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1 ∨
      WinningStructuralCollisionOccurs execution.2.1.1 execution.1

theorem capped_winning_implies_encodingPrehit_or_digestBad
    (adversary : Adversary Concrete.cappedScheme)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hwin : execution.1.won = true) :
    WinningEncodingPrehitOccurs execution ∨
      WinningDigestBadEventOccurs execution := by
  have hcache : (execution.1, execution.2.1.1) ∈ support
      (detailedGameWithCache Concrete.cappedScheme adversary) := by
    rw [← cappedDetailedGameWithEncodingTrace_cache_projection, support_map]
    exact ⟨execution, hmem, rfl⟩
  have hunified := winning_outcome_has_unifiedBadEvent execution.2.1.1
    execution.1 (capped_detailed_execution_consistent adversary _ hcache) hwin
  rcases hunified with hencoding | hchain | hstructural
  · have hencoding' : WinningOutcomeBadEventOccurs execution.2.1.1
        execution.1 .encoding := by
      simpa [WinningEncodingEventOccurs, WinningGlobalBadEventOccurs,
        GlobalOutcomeBadEventOccurs, WinningOutcomeBadEventOccurs] using hencoding
    have hsigning : (execution.1, execution.2.1) ∈ support
        (cappedDetailedGameWithSigningTrace adversary) := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
      exact ⟨execution, hmem, rfl⟩
    obtain ⟨entry, hentry, hprehit | hsigningCollision |
        hforgedCollision⟩ :=
      cappedWinning_encoding_event_trace_postSigning_decomposition adversary
        (execution.1, execution.2.1) hsigning hencoding'
    · exact Or.inl ⟨hencoding', entry, hentry, hprehit⟩
    · exact Or.inr (Or.inl ⟨hencoding',
        cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
          adversary execution hmem hencoding'
            ⟨entry, hentry, hsigningCollision⟩⟩)
    · obtain ⟨encoding, hdecode⟩ := hencoding'.forgery_decode
      exact Or.inr (Or.inl ⟨hencoding',
        cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
          adversary execution hmem hencoding' encoding hdecode
            ⟨entry, hentry, hforgedCollision⟩⟩)
  · exact Or.inr (Or.inr (Or.inl hchain))
  · exact Or.inr (Or.inr (Or.inr hstructural))

theorem capped_forgeAdvantage_le_encodingPrehit_add_digestBad
    (adversary : Adversary Concrete.cappedScheme) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      Pr[WinningEncodingPrehitOccurs |
        cappedDetailedGameWithEncodingTrace adversary] +
      Pr[WinningDigestBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] := by
  calc
    forgeAdvantage Concrete.cappedScheme adversary =
        Pr[fun execution : CappedEncodingTraceExecution =>
          execution.1.won = true |
          cappedDetailedGameWithEncodingTrace adversary] := by
      rw [forgeAdvantage_eq_detailedGameWithCache,
        ← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map]
      rfl
    _ ≤ Pr[fun execution : CappedEncodingTraceExecution =>
          WinningEncodingPrehitOccurs execution ∨
            WinningDigestBadEventOccurs execution |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact capped_winning_implies_encodingPrehit_or_digestBad adversary
        execution hmem hwin
    _ ≤ _ := probEvent_or_le _ _ _

theorem capped_encodingPrehit_probability_le_exact
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[WinningEncodingPrehitOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      (lifetime : ENNReal) *
        ((signingAttemptLimit : ENNReal) * (q : ENNReal) *
          ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ :=
      cappedDetailedGameWithSigningTrace_winning_prehit_probability_le_exact
        q adversary hbound

theorem capped_encodingPrehit_budget_eq_137 (q : Nat) :
    (lifetime : ENNReal) *
        ((signingAttemptLimit : ENNReal) * (q : ENNReal) *
          ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) =
      (q : ENNReal) / ((2 ^ 137 : Nat) : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_div]
  norm_num [lifetime, treeHeight, signingAttemptLimit, randomnessBits]
  field_simp
  ring

inductive UnifiedDigestIndex where
  | encodingDigest (index : Epoch × Fin signingAttemptLimit)
  | chainValue (index : CappedChain.GlobalChainValueIndex)
  | leafDigest (epoch : Epoch)
  | merkleDigest (index : MerkleLevel × MerkleNode)
deriving DecidableEq, Fintype

noncomputable def HasCappedUnifiedDigestReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) : Prop :=
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
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : HasCappedUnifiedDigestReduction q adversary) :
    Pr[WinningDigestBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  obtain ⟨Result, computation, hbound, hprobability⟩ := hreduction
  exact hprobability.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
      (q + numChains) computation hbound)

theorem capped_exact_loss_budget_le_127
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

theorem capped_xmss_forgeAdvantage_le_127_of_unifiedDigestReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hreduction : HasCappedUnifiedDigestReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
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
    _ ≤ _ := capped_exact_loss_budget_le_127 q
      (hashQueryBound_at_least_verificationQueries adversary q hbound)

def HasCappedUnifiedDigestReductions : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.cappedScheme),
    HasHashQueryBound Concrete.cappedScheme adversary q →
      HasCappedUnifiedDigestReduction q adversary

theorem xmss_has_127_bits_of_classical_security_of_unifiedDigestReductions
    (hreductions : HasCappedUnifiedDigestReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 127 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_127_of_unifiedDigestReduction q adversary
    hbound (hreductions q adversary hbound)

theorem xmss_has_126_bits_of_classical_security_of_unifiedDigestReductions
    (hreductions : HasCappedUnifiedDigestReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 126 :=
  (xmss_has_127_bits_of_classical_security_of_unifiedDigestReductions
    hreductions).mono (by omega)

theorem xmss_has_125_bits_of_classical_security_of_unifiedDigestReductions
    (hreductions : HasCappedUnifiedDigestReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 :=
  (xmss_has_127_bits_of_classical_security_of_unifiedDigestReductions
    hreductions).mono (by omega)

theorem xmss_has_125_126_127_bits_of_classical_security_of_unifiedDigestReductions
    (hreductions : HasCappedUnifiedDigestReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 ∧
      HasClassicalSecurityBits Concrete.cappedScheme 126 ∧
      HasClassicalSecurityBits Concrete.cappedScheme 127 :=
  ⟨xmss_has_125_bits_of_classical_security_of_unifiedDigestReductions
      hreductions,
    xmss_has_126_bits_of_classical_security_of_unifiedDigestReductions
      hreductions,
    xmss_has_127_bits_of_classical_security_of_unifiedDigestReductions
      hreductions⟩

end XmssSecurity
