import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def KeygenAddressedHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, AtHashAddress parameter domain input

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (KeygenAddressedHashInput parameter) :=
  Classical.decPred _

theorem Concrete.tweakableHash_queryBound_zero_unaddressed
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash,
    KeygenAddressedHashInput]

theorem Concrete.chainWalk_queryBound_zero_unaddressed
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter epoch chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.oneTimePublicKey_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    (Concrete.oneTimePublicKey parameter secret epoch :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.oneTimePublicKey]
  apply Concrete.sequenceFin_queryBound_zero
  intro chain
  exact Concrete.chainWalk_queryBound_zero_unaddressed parameter epoch chain
    0 (chainLength - 1) (secret epoch chain)

theorem Concrete.leafAt_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    (Concrete.leafAt parameter secret epoch :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_unaddressed parameter secret
      epoch) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _

theorem Concrete.treeNode_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact Concrete.leafAt_queryBound_zero_unaddressed parameter secret node
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node false)) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node true)) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.keygen_cache_none_unaddressed
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput)
    (hinput : ¬ KeygenAddressedHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Concrete.treeNode_queryBound_zero_unaddressed parameter secret
      treeHeight Concrete.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

theorem Concrete.keygen_cache_none_at_encodingAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress keyResult.1.2.parameter (.encoding epoch) input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Concrete.treeNode_queryBound_zero_encodingAddress parameter secret
      epoch treeHeight Concrete.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

end XmssSecurity.CappedChain
