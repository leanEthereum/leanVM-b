import XmssSecurity.Proof.CappedEncodingExpectedBound
import XmssSecurity.Proof.CappedUnifiedStructuralCollision
import XmssSecurity.Proof.ExactKeygenQueryCount
import XmssSecurity.Proof.LossDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

theorem CappedSuffix.keygenChainTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (epoch : Epoch) (payload : Message × Randomness) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
    Concrete.CacheView.encodingInput secretKey.parameter epoch payload := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (epoch : Epoch) (payload : Message × Randomness) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
    Concrete.CacheView.encodingInput secretKey.parameter epoch payload := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (epoch : Epoch) (payload : Message × Randomness) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
    Concrete.CacheView.encodingInput secretKey.parameter epoch payload := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

@[simp]
theorem keygenStructuralTargetInput_encodingInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (epoch : Epoch) (payload : Message × Randomness) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
    Concrete.CacheView.encodingInput secretKey.parameter epoch payload := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_encodingInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self]

theorem encodingHashQuery_structuralQuery_disjoint
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : OracleWorld.Domain) :
    ¬(CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter input ∧
      Rom.IsRelevantHashQuery (fun hashInput =>
        keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput) input) := by
  cases input with
  | inl index => simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      intro hboth
      rcases hboth with ⟨hencoding, hstructural⟩
      change (encodingInputEpoch? secretKey.parameter hashInput).isSome at hencoding
      change keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput at hstructural
      cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
      | none => simp [hepoch] at hencoding
      | some epoch =>
          obtain ⟨payload, hpayload⟩ :=
            exists_encodingInput_of_encodingInputEpoch?_eq_some
              secretKey.parameter hashInput epoch hepoch
          rw [← hpayload] at hstructural
          exact hstructural
            (keygenStructuralTargetInput_encodingInput secretKey cache epoch payload)

theorem cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    (cappedSourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1
      keyResult.1.2).IsQueryBoundP IsHashQuery
        (q - treeHashQueryCount treeHeight) := by
  have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
    apply support_simulateQ_run'_subset romImpl Concrete.scheme.keygen ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨keyResult, hkeyResult, rfl⟩
  have hkeyPrecomputed : keyResult.1 ∈ support Concrete.precomputedKeygen := by
    simpa [Concrete.scheme] using hkeySupport
  have hcontinuation := detailedGameAfterKeygen_hashQueryBound_sub_keygen
    adversary q hbound keyResult.1 hkeyPrecomputed
  have hstandard :
      (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1
        keyResult.1.2).IsQueryBoundP IsHashQuery
          (q - treeHashQueryCount treeHeight) := hcontinuation
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (cappedDetailedGameAfterKeygen_unloggedProjection adversary keyResult.1.1
      keyResult.1.2)).mp hstandard

noncomputable def expectedPostKeygenStructuralQueries
    (adversary : Adversary) : ENNReal :=
  ∑' keyResult,
    Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2

theorem expectedStructuralQueries_detailed_eq_source
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2) keyResult.2 =
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2 := by
  have hprojection := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
      computation keyResult.2)
    (cappedDetailedGameAfterKeygen_unloggedProjection adversary
      keyResult.1.1 keyResult.1.2)
  rw [expectedSimulatedQueryCount_map] at hprojection
  exact hprojection

theorem winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries
    (adversary : Adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningStructuralCollisionOccurs execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      expectedPostKeygenStructuralQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  apply (winningStructuralCollision_probability_le_expectedMovedQueries
    adversary).trans_eq
  unfold expectedPostKeygenStructuralQueries
  congr 1
  apply tsum_congr
  intro keyResult
  congr 1
  exact expectedStructuralQueries_detailed_eq_source adversary keyResult

theorem postKeygenEncoding_add_structural_expected_le
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary +
        expectedPostKeygenStructuralQueries adversary ≤
      (q - treeHashQueryCount treeHeight : Nat) := by
  unfold CappedEncodingMonitor.expectedPostKeygenEncodingQueries
    expectedPostKeygenStructuralQueries
  rw [← ENNReal.tsum_add]
  simp_rw [← mul_add]
  calc
    _ ≤ ∑' keyResult,
        Pr[= keyResult |
          (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          (q - treeHashQueryCount treeHeight : Nat) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeyResult : keyResult ∈ support
          ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul_right
        let encodingPredicate :=
          CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter
        let structuralPredicate := Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input
        let source := cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2
        calc
          expectedSimulatedQueryCount romImpl encodingPredicate source keyResult.2 +
              expectedSimulatedQueryCount romImpl structuralPredicate source
                keyResult.2 =
            expectedSimulatedQueryCount romImpl
              (fun input => encodingPredicate input ∨ structuralPredicate input)
              source keyResult.2 := by
                symm
                exact expectedSimulatedQueryCount_or_of_disjoint romImpl
                  encodingPredicate structuralPredicate
                  (encodingHashQuery_structuralQuery_disjoint
                    keyResult.1.2 keyResult.2) source keyResult.2
          _ ≤ expectedSimulatedQueryCount romImpl IsHashQuery source
              keyResult.2 := by
            apply expectedSimulatedQueryCount_mono
            intro input hinput
            cases input with
            | inl index =>
                rcases hinput with hencoding | hstructural
                · simp [encodingPredicate,
                    CappedEncodingMonitor.IsEncodingHashQuery] at hencoding
                · simp [structuralPredicate, Rom.IsRelevantHashQuery] at hstructural
            | inr hashInput => simp [IsHashQuery]
          _ ≤ (q - treeHashQueryCount treeHeight : Nat) := by
            apply expectedSimulatedQueryCount_le_of_isQueryBoundP
            exact cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
              q adversary hbound keyResult hkeyResult
      · rw [probOutput_eq_zero_of_not_mem_support hkeyResult, zero_mul]
        exact zero_le
    _ = (∑' keyResult,
          Pr[= keyResult |
            (simulateQ romImpl Concrete.scheme.keygen).run ∅]) *
        (q - treeHashQueryCount treeHeight : Nat) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (q - treeHashQueryCount treeHeight : Nat) := by
      gcongr
      exact tsum_probOutput_le_one
    _ = _ := one_mul _

end XmssSecurity
