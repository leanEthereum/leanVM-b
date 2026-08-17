import XmssSecurity.CappedGlobalChainHighCausalSimulator

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem programmedGlobal_filteredKeygen_stateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalFilteredCausalStateRelation left right.1 left.cache
      (globalFilteredCausalKeygenState right.1.1) := by
  classical
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.1.2
  refine ⟨?_, ?_, le_rfl, rfl, ?_⟩
  · intro input hinput
    obtain ⟨epoch, message, randomness, rfl⟩ := hinput
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey epoch (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter epoch (message, randomness)) = none at hleftNone
    have hnotMerkle : ¬ MerkleHashInput right.1.1.secretKey.parameter
        (Concrete.CacheView.encodingInput left.secretKey.parameter epoch
          (message, randomness)) := by
      rintro ⟨level, node, hmerkle⟩
      have hmerkleCanonical : AtHashAddress
          right.1.1.secretKey.parameter (.merkle level node)
          (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
            (message, randomness)) := by
        simpa only [hparameter] using hmerkle
      have hencoding : AtHashAddress right.1.1.secretKey.parameter
          (.encoding epoch)
          (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
            (message, randomness)) := by
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique right.1.1.secretKey.parameter
        (.merkle level node) (.encoding epoch)
        (Concrete.CacheView.encodingInput right.1.1.secretKey.parameter epoch
          (message, randomness)) hmerkleCanonical hencoding
      simp at hdomain
    simpa [globalFilteredCausalKeygenState, hnotMerkle] using hleftNone
  · intro input
    by_cases hmerkle : MerkleHashInput right.1.1.secretKey.parameter input
    · left
      have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
        rw [hparameter]
        exact hmerkle
      simpa [globalFilteredCausalKeygenState, hmerkle] using
        htree.merkle input hmerkleLeft
    · right
      exact ⟨rfl, by simp [globalFilteredCausalKeygenState, hmerkle]⟩
  · intro index value hvalue
    simp [globalFilteredCausalKeygenState] at hvalue

end XmssSecurity.CappedChain
