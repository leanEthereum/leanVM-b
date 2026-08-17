import XmssSecurity.Capped125MainTheorem
import XmssSecurity.CappedExactLossArchitecture

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem capped_globalWinningChainValueRevealed_probability_le_q_add_numChains
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalWinningChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeGuessesKeygenChainValue
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningChainValueRevealed_probability_le_globalKeygenValueGuess
        adversary
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningKeygenValueGuess_probability_le_origin adversary
    _ ≤ _ :=
      CappedChain.globalWinningChainOrigin_probability_le_q_add_numChains
        q adversary hreduction

theorem capped_winningDigestBadEvent_probability_le_separate
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hchain : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[WinningDigestBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) +
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  let encoding := fun execution : CappedEncodingTraceExecution =>
    WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2.2 = true
  let chain := fun execution : CappedEncodingTraceExecution =>
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1
  let structural := fun execution : CappedEncodingTraceExecution =>
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1
  calc
    Pr[WinningDigestBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] =
      Pr[fun execution => encoding execution ∨
          (chain execution ∨ structural execution) |
        cappedDetailedGameWithEncodingTrace adversary] := by rfl
    _ ≤ Pr[encoding | cappedDetailedGameWithEncodingTrace adversary] +
        Pr[fun execution => chain execution ∨ structural execution |
          cappedDetailedGameWithEncodingTrace adversary] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[encoding | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[chain | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[structural | cappedDetailedGameWithEncodingTrace adversary]) := by
      gcongr
      exact probEvent_or_le _ _ _
    _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
        (((q + numChains : Nat) : ENNReal) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
      gcongr
      · exact cappedWinning_encoding_monitorHit_probability_le
          q adversary hbound
      · change Pr[fun execution : CappedEncodingTraceExecution =>
            GlobalWinningChainValueRevealed execution.2.1.1 execution.1 |
          cappedDetailedGameWithEncodingTrace adversary] ≤ _
        calc
          _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                GlobalWinningChainValueRevealed execution.2 execution.1 |
              detailedGameWithCache Concrete.cappedScheme adversary] := by
            rw [← cappedDetailedGameWithEncodingTrace_cache_projection,
              probEvent_map]
            rfl
          _ ≤ _ :=
            capped_globalWinningChainValueRevealed_probability_le_q_add_numChains
              q adversary hchain
      · change Pr[fun execution : CappedEncodingTraceExecution =>
            WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
          cappedDetailedGameWithEncodingTrace adversary] ≤ _
        calc
          _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                WinningStructuralCollisionOccurs execution.2 execution.1 |
              detailedGameWithCache Concrete.cappedScheme adversary] := by
            rw [← cappedDetailedGameWithEncodingTrace_cache_projection,
              probEvent_map]
            rfl
          _ ≤ _ := capped_winningStructuralCollision_probability_le
            q adversary hbound
    _ = _ := by ring

theorem capped_separate_loss_budget_le_126
    (q : Nat) (hq : verificationChainHashes + 1 ≤ q) :
    (q : ENNReal) / ((2 ^ 137 : Nat) : ENNReal) +
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
          ((q + numChains : Nat) : ENNReal) /
            ((2 ^ digestBits : Nat) : ENNReal) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) := by
  rw [verificationChainHashes_eq] at hq
  norm_num at hq
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  norm_num [digestBits, numChains]
  have hqreal : (100 : Real) ≤ (q : Real) := by exact_mod_cast hq
  field_simp
  ring_nf at ⊢
  linarith [hqreal]

theorem capped_xmss_forgeAdvantage_le_126_of_boundedPublicReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hchain : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) := by
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
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
          ((q + numChains : Nat) : ENNReal) /
            ((2 ^ digestBits : Nat) : ENNReal) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) :=
      add_le_add (capped_encodingPrehit_probability_le_exact q adversary hbound)
        (capped_winningDigestBadEvent_probability_le_separate q adversary
          hbound hchain)
    _ = (q : ENNReal) / ((2 ^ 137 : Nat) : ENNReal) +
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
          ((q + numChains : Nat) : ENNReal) /
            ((2 ^ digestBits : Nat) : ENNReal) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
      rw [capped_encodingPrehit_budget_eq_137]
    _ ≤ _ := capped_separate_loss_budget_le_126 q
      (hashQueryBound_at_least_verificationQueries adversary q hbound)

theorem xmss_cappedSigner_has_126_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.cappedScheme 126 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_126_of_boundedPublicReduction q adversary
    hbound
      (CappedChain.hasGlobalHighBoundedPublicReduction_of_hashQueryBound
        q adversary hbound)

theorem xmss_cappedSigner_has_125_and_126_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.cappedScheme 125 ∧
      HasClassicalSecurityBits Concrete.cappedScheme 126 :=
  ⟨xmss_cappedSigner_has_125_bits_of_classical_security,
    xmss_cappedSigner_has_126_bits_of_classical_security⟩

end XmssSecurity
