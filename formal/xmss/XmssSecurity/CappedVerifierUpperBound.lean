import XmssSecurity.CappedVerifierQueryFloor

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

namespace ExactQueryCount

theorem isTotalQueryBound {computation : OracleComp spec α} {count : Nat}
    (hexact : ExactQueryCount computation count) :
    computation.IsTotalQueryBound count := by
  induction hexact with
  | pure value => trivial
  | query input next count hnext ih =>
      rw [OracleComp.isTotalQueryBound_query_bind_iff]
      exact ⟨by omega, fun output => ih output⟩

theorem leafHash (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    ExactQueryCount
      (Concrete.leafHash parameter epoch endpoints : OracleComp HashSpec Digest) 1 := by
  exact tweakableHash parameter (.leaf epoch) (Concrete.leafPayload endpoints)

theorem authenticationNodeHash (parameter : PublicParameter) (epoch : Epoch)
    (level : Nat) (current sibling : Digest) (hlevel : level < treeHeight) :
    ExactQueryCount
      (Concrete.authenticationNodeHash (m := OracleComp HashSpec) parameter epoch
        level current sibling) 1 := by
  rw [Concrete.authenticationNodeHash]
  simp only [hlevel, ↓reduceDIte]
  split <;> apply tweakableHash

theorem authenticationRoot (parameter : PublicParameter) (epoch : Epoch)
    (signature : Signature) (levels : Nat) (leaf : Digest)
    (hlevels : levels ≤ treeHeight) :
    ExactQueryCount
      (Concrete.authenticationRoot (m := OracleComp HashSpec) parameter epoch
        signature levels leaf) levels := by
  induction levels with
  | zero => exact .pure leaf
  | succ levels ih =>
      rw [Concrete.authenticationRoot]
      exact (ih (Nat.le_of_succ_le hlevels)).bind
        (fun current => Concrete.authenticationNodeHash parameter epoch levels
          current (Concrete.signaturePath signature levels)) 1
        (fun current => authenticationNodeHash parameter epoch levels current
          (Concrete.signaturePath signature levels) (Nat.lt_of_succ_le hlevels))

theorem verifyAfterLeaf (publicKey : PublicKey) (epoch : Epoch)
    (signature : Signature) (leaf : Digest) :
    ExactQueryCount
      (Concrete.verifyAfterLeaf (m := OracleComp HashSpec) publicKey epoch
        signature leaf) treeHeight := by
  rw [Concrete.verifyAfterLeaf]
  exact (authenticationRoot publicKey.parameter epoch signature treeHeight leaf
    le_rfl).bind
      (fun root => (Pure.pure (decide (root = publicKey.root)) :
        OracleComp HashSpec Bool)) 0
      (fun root => ExactQueryCount.pure (decide (root = publicKey.root)))

end ExactQueryCount

def verifierHashQueryUpperBound : Nat :=
  1 + verificationChainHashes + 1 + treeHeight

theorem Concrete.verify_hashQueryBound_upper
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.verify publicKey epoch message signature :
      OracleComp HashSpec Bool).IsTotalQueryBound verifierHashQueryUpperBound := by
  unfold Concrete.verify verifierHashQueryUpperBound
  rw [Concrete.encodingHash]
  rw [show 1 + verificationChainHashes + 1 + treeHeight =
    1 + (verificationChainHashes + 1 + treeHeight) by omega]
  apply OracleComp.isTotalQueryBound_bind
    (ExactQueryCount.tweakableHash publicKey.parameter (.encoding epoch)
      (Concrete.encodingPayload message signature.randomness)).isTotalQueryBound
  intro digest
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only
      exact (show (Pure.pure false : OracleComp HashSpec Bool)
        |>.IsTotalQueryBound 0 by trivial).mono (by omega)
  | some encoding =>
      simp only
      have hvalid := (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2
      have hwork := TargetSum.verificationWork_eq encoding hvalid
      have hrecovery :
          (Concrete.recoverEndpoints (m := OracleComp HashSpec)
            publicKey.parameter epoch encoding signature).IsTotalQueryBound
              verificationChainHashes := by
        rw [← hwork]
        exact (ExactQueryCount.recoverEndpoints publicKey.parameter epoch
          encoding signature).isTotalQueryBound
      rw [show verificationChainHashes + 1 + treeHeight =
        verificationChainHashes + (1 + treeHeight) by omega]
      apply OracleComp.isTotalQueryBound_bind
        hrecovery
      intro endpoints
      have hleaf :
          (Concrete.leafHash publicKey.parameter epoch endpoints :
            OracleComp HashSpec Digest).IsTotalQueryBound 1 :=
        (ExactQueryCount.leafHash publicKey.parameter epoch endpoints
          ).isTotalQueryBound
      apply OracleComp.isTotalQueryBound_bind
        hleaf
      intro leaf
      have hroot := (ExactQueryCount.verifyAfterLeaf publicKey epoch signature
        leaf).isTotalQueryBound
      simpa [hwork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hroot

theorem Concrete.scheme_verify_hashQueryBound_upper
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.scheme.verify publicKey epoch message signature).IsQueryBoundP
      (· matches .inr _) verifierHashQueryUpperBound := by
  change (liftM (Concrete.verify publicKey epoch message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool).IsQueryBoundP
      (· matches .inr _) verifierHashQueryUpperBound
  rw [← OracleComp.liftComp_eq_liftM]
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : HashSpec.Domain => True)
    (q := fun input : OracleWorld.Domain => input matches .inr _)
    (fun input => by
      change True ↔ ((Sum.inr input : OracleWorld.Domain) matches .inr _)
      simp)
    (Concrete.verify_hashQueryBound_upper publicKey epoch message signature
      ).isQueryBoundP

end XmssSecurity
