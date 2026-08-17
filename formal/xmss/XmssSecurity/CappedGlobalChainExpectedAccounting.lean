import XmssSecurity.CappedGlobalChainExpectedBound
import XmssSecurity.CappedUnifiedExpectedDigest

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

@[simp]
theorem CappedChain.globalLeafInputData?_encodingInput
    (parameter : PublicParameter) (epoch : Epoch) (payload : Message × Randomness) :
    CappedChain.globalLeafInputData? parameter
        (Concrete.CacheView.encodingInput parameter epoch payload) = none := by
  unfold CappedChain.globalLeafInputData?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata.symm
    cases hdomain
  · rfl

theorem encodingHashQuery_globalChainRelevant_disjoint
    (secretKey : SecretKey) (input : OracleWorld.Domain) :
    ¬(CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter input ∧
      Rom.IsRelevantHashQuery
        (CappedChain.GlobalChainProbeRelevantInput secretKey) input) := by
  cases input with
  | inl index => simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      intro hboth
      rcases hboth with ⟨hencoding, hrelevant⟩
      change (encodingInputEpoch? secretKey.parameter hashInput).isSome at hencoding
      change CappedChain.GlobalChainProbeRelevantInput secretKey hashInput at hrelevant
      cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
      | none => simp [hepoch] at hencoding
      | some epoch =>
          obtain ⟨payload, hinput⟩ :=
            exists_encodingInput_of_encodingInputEpoch?_eq_some
              secretKey.parameter hashInput epoch hepoch
          subst hashInput
          simp [CappedChain.GlobalChainProbeRelevantInput] at hrelevant

noncomputable def expectedPostKeygenGlobalChainRelevantQueries
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' keyResult,
    Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
      expectedSimulatedQueryCount xmssRomImpl
        (Rom.IsRelevantHashQuery
          (CappedChain.GlobalChainProbeRelevantInput keyResult.1.2))
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2

noncomputable def expectedGlobalHighDirectProbeQueries
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  expectedSimulatedQueryCount
    RevealProbeOracleSimulation.lazyMonitorImpl
    RevealProbeOracleSimulation.IsProbeQuery
    (CappedChain.globalHighDirectProgram adversary)
    AdaptiveRevealMonitor.State.empty

theorem CappedChain.observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace
    (result : CappedChain.GlobalHighDirectResult) :
    RevealProbeOracleSimulation.observedProbeCount
        (CappedChain.globalHighDirectForgeryPrimaryProbeTrace result) =
      numChains := by
  unfold CappedChain.globalHighDirectForgeryPrimaryProbeTrace
  exact CappedChain.observedProbeCount_globalForgeryPrimaryProbeTrace _

theorem expectedGlobalHighDirectPublicProbeQueries_le
    (adversary : Adversary Concrete.scheme) :
    expectedSimulatedQueryCount
        RevealProbeOracleSimulation.lazyMonitorImpl
        RevealProbeOracleSimulation.IsProbeQuery
        (CappedChain.globalHighDirectPublicProgram adversary)
        AdaptiveRevealMonitor.State.empty ≤
      expectedGlobalHighDirectProbeQueries adversary + numChains := by
  unfold CappedChain.globalHighDirectPublicProgram
  unfold expectedGlobalHighDirectProbeQueries
  rw [expectedSimulatedQueryCount_bind]
  apply add_le_add le_rfl
  calc
    (∑' result,
        Pr[= result |
          (simulateQ RevealProbeOracleSimulation.lazyMonitorImpl
            (CappedChain.globalHighDirectProgram adversary)).run
              AdaptiveRevealMonitor.State.empty] *
          expectedSimulatedQueryCount
            RevealProbeOracleSimulation.lazyMonitorImpl
            RevealProbeOracleSimulation.IsProbeQuery
            (RevealProbeOracleSimulation.emitObservedTrace
              (CappedChain.globalHighDirectForgeryPrimaryProbeTrace result.1))
            result.2) ≤
      ∑' result,
        Pr[= result |
          (simulateQ RevealProbeOracleSimulation.lazyMonitorImpl
            (CappedChain.globalHighDirectProgram adversary)).run
              AdaptiveRevealMonitor.State.empty] * (numChains : ENNReal) := by
        apply ENNReal.tsum_le_tsum
        intro result
        gcongr
        apply expectedSimulatedQueryCount_le_of_isQueryBoundP
        simpa [CappedChain.observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace]
          using RevealProbeOracleSimulation.emitObservedTrace_isProbeQueryBoundP
            (CappedChain.globalHighDirectForgeryPrimaryProbeTrace result.1)
    _ = (∑' result,
          Pr[= result |
            (simulateQ RevealProbeOracleSimulation.lazyMonitorImpl
              (CappedChain.globalHighDirectProgram adversary)).run
                AdaptiveRevealMonitor.State.empty]) * (numChains : ENNReal) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (numChains : ENNReal) := by
      gcongr
      exact tsum_probOutput_le_one
    _ = numChains := one_mul _

theorem CappedChain.globalWinningChainOrigin_probability_le_expectedGlobalHighDirectProbes
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hreduction : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
        result.1.2 result.2.2 result.1.1.2 result.2.1 |
      CappedChain.detailedGameWithKeygenCache adversary] ≤
      (expectedGlobalHighDirectProbeQueries adversary + numChains) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  apply (CappedChain.globalWinningChainOrigin_probability_le_unboundedExpectedProbes
    q adversary hreduction).trans
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exact expectedGlobalHighDirectPublicProbeQueries_le adversary

theorem postKeygenEncoding_add_globalChainRelevant_expected_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary +
        expectedPostKeygenGlobalChainRelevantQueries adversary ≤
      (q - treeHashQueryCount treeHeight : Nat) := by
  unfold CappedEncodingMonitor.expectedPostKeygenEncodingQueries
    expectedPostKeygenGlobalChainRelevantQueries
  rw [← ENNReal.tsum_add]
  simp_rw [← mul_add]
  calc
    _ ≤ ∑' keyResult,
        Pr[= keyResult |
          (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          (q - treeHashQueryCount treeHeight : Nat) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeyResult : keyResult ∈ support
          ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul_right
        let encodingPredicate :=
          CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter
        let chainPredicate := Rom.IsRelevantHashQuery
          (CappedChain.GlobalChainProbeRelevantInput keyResult.1.2)
        let source := cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2
        calc
          expectedSimulatedQueryCount xmssRomImpl encodingPredicate source keyResult.2 +
              expectedSimulatedQueryCount xmssRomImpl chainPredicate source
                keyResult.2 =
            expectedSimulatedQueryCount xmssRomImpl
              (fun input => encodingPredicate input ∨ chainPredicate input)
              source keyResult.2 := by
                symm
                exact expectedSimulatedQueryCount_or_of_disjoint xmssRomImpl
                  encodingPredicate chainPredicate
                  (encodingHashQuery_globalChainRelevant_disjoint
                    keyResult.1.2) source keyResult.2
          _ ≤ expectedSimulatedQueryCount xmssRomImpl IsHashQuery source
              keyResult.2 := by
            apply expectedSimulatedQueryCount_mono
            intro input hinput
            cases input with
            | inl index =>
                rcases hinput with hencoding | hchain
                · simp [encodingPredicate,
                    CappedEncodingMonitor.IsEncodingHashQuery] at hencoding
                · simp [chainPredicate, Rom.IsRelevantHashQuery] at hchain
            | inr hashInput => simp [IsHashQuery]
          _ ≤ (q - treeHashQueryCount treeHeight : Nat) := by
            apply expectedSimulatedQueryCount_le_of_isQueryBoundP
            exact cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
              q adversary hbound keyResult hkeyResult
      · rw [probOutput_eq_zero_of_not_mem_support hkeyResult, zero_mul]
        exact zero_le
    _ = (∑' keyResult,
          Pr[= keyResult |
            (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅]) *
        (q - treeHashQueryCount treeHeight : Nat) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (q - treeHashQueryCount treeHeight : Nat) := by
      gcongr
      exact tsum_probOutput_le_one
    _ = _ := one_mul _

end XmssSecurity
