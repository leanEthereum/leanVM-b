import XmssSecurity.Proof.ExactQueryCount
import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.DetailedExecution
import XmssSecurity.Proof.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.QueryBoundSupport
import XmssSecurity.Statement
import XmssSecurity.Proof.StatementLemmas
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

def treeHashQueryCount : Nat → Nat
  | 0 => numChains * (chainLength - 1) + 1
  | levels + 1 => 2 * treeHashQueryCount levels + 1

namespace ExactQueryCount

theorem oneTimePublicKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) :
    ExactQueryCount
      (Concrete.oneTimePublicKey (m := OracleComp HashSpec) parameter secret epoch)
      (numChains * (chainLength - 1)) := by
  unfold Concrete.oneTimePublicKey
  have hexact := sequenceFin
    (fun chain : ChainIndex =>
      Concrete.chainWalk (m := OracleComp HashSpec) parameter epoch chain 0
        (chainLength - 1) (secret epoch chain))
    (fun _ : ChainIndex => chainLength - 1)
    (fun chain => chainWalk parameter epoch chain 0 (chainLength - 1)
      (secret epoch chain) (by omega))
  simpa using hexact

theorem leafAt (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) :
    ExactQueryCount
      (Concrete.leafAt (m := OracleComp HashSpec) parameter secret epoch)
      (numChains * (chainLength - 1) + 1) := by
  unfold Concrete.leafAt
  exact (oneTimePublicKey parameter secret epoch).bind
    (fun endpoints => Concrete.leafHash parameter epoch endpoints) 1
    (fun endpoints => tweakableHash parameter (.leaf epoch)
      (Concrete.leafPayload endpoints))

theorem treeNode (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) :
    ExactQueryCount
      (Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels node)
      (treeHashQueryCount levels) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact leafAt parameter secret node
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Concrete.treeNode_succ_eq]
      have hleft := ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
      have hright := ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
      have hcontinuation (left : Digest) :
          ExactQueryCount (do
            let right ← Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right)
            (treeHashQueryCount levels + 1) :=
        hright.bind
          (fun right => Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right) 1
          (fun right => tweakableHash parameter (.merkle ⟨levels, hlevel⟩ node)
            (Concrete.nodePayload left right))
      simpa [hlevel, treeHashQueryCount, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.two_mul] using
        hleft.bind
          (fun left => do
            let right ← Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right)
          (treeHashQueryCount levels + 1) hcontinuation

theorem rootTree (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) :
    ExactQueryCount
      (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
        Concrete.rootNode)
      (treeHashQueryCount treeHeight) :=
  treeNode parameter secret treeHeight Concrete.rootNode le_rfl

end ExactQueryCount

theorem treeHashQueryCount_base_le (levels : Nat) :
    numChains * (chainLength - 1) + 1 ≤ treeHashQueryCount levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simp only [treeHashQueryCount]
      omega

def IsHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsHashQuery := by
  intro input
  cases input <;> unfold IsHashQuery <;> exact inferInstance

namespace ExactQueryCount.ExactPredicateQueryCount

theorem liftProbComp_hashCount_zero (computation : ProbComp α) :
    ExactPredicateQueryCount IsHashQuery
      (liftM computation : OracleComp OracleWorld α) 0 := by
  apply ExactQueryCount.ExactPredicateQueryCount.of_isQueryBoundP_zero
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False) (q := IsHashQuery)
    (fun input => by simp [IsHashQuery])
    (OracleComp.isQueryBoundP_false computation 0)

theorem rootTreeWithLog_hashCount
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ExactPredicateQueryCount IsHashQuery
      (liftM
        (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
          Concrete.rootNode).withQueryLog :
        OracleComp OracleWorld (Digest × QueryLog HashSpec))
      (treeHashQueryCount treeHeight) := by
  exact ExactQueryCount.liftComp_predicate
    (ExactQueryCount.withQueryLog (ExactQueryCount.rootTree parameter secret))
    IsHashQuery (fun input => by
      change IsHashQuery (Sum.inr input)
      simp [IsHashQuery])

theorem precomputedKeygen_hashCount :
    ExactPredicateQueryCount IsHashQuery Concrete.precomputedKeygen
      (treeHashQueryCount treeHeight) := by
  unfold Concrete.precomputedKeygen
  exact ExactQueryCount.ExactPredicateQueryCount.bind
    (liftProbComp_hashCount_zero Concrete.samplePublicParameter)
    (fun parameter => do
      let secret ← liftM Concrete.sampleSecret
      let result ← liftM
        (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
          Concrete.rootNode).withQueryLog
      let cache := hashCacheOfLog result.2
      return (PublicKey.mk result.1 parameter,
        Concrete.precomputedSecretKey parameter secret cache))
    (treeHashQueryCount treeHeight) (fun parameter =>
      ExactQueryCount.ExactPredicateQueryCount.bind
        (liftProbComp_hashCount_zero Concrete.sampleSecret)
        (fun secret => do
          let result ← liftM
            (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
              Concrete.rootNode).withQueryLog
          let cache := hashCacheOfLog result.2
          return (PublicKey.mk result.1 parameter,
            Concrete.precomputedSecretKey parameter secret cache))
        (treeHashQueryCount treeHeight) (fun secret =>
          ExactQueryCount.ExactPredicateQueryCount.bind
            (rootTreeWithLog_hashCount parameter secret)
            (fun result =>
              let cache := hashCacheOfLog result.2
              (Pure.pure (PublicKey.mk result.1 parameter,
                Concrete.precomputedSecretKey parameter secret cache) :
                OracleComp OracleWorld (PublicKey × SecretKey)))
            0 (fun result => ExactPredicateQueryCount.pure _)))

end ExactQueryCount.ExactPredicateQueryCount

theorem detailedGameAfterKeygen_hashQueryBound_sub_keygen
    (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (key : PublicKey × SecretKey) (hkey : key ∈ support Concrete.precomputedKeygen) :
    (detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2).IsQueryBoundP
      IsHashQuery (q - treeHashQueryCount treeHeight) := by
  have hdetailed :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  have hdetailedHash :
      (detailedGameCore Concrete.scheme adversary).IsQueryBoundP IsHashQuery q :=
    (OracleComp.isQueryBoundP_congr_pred (p' := IsHashQuery)
      (fun input => by cases input <;> simp [IsHashQuery])).mp hdetailed
  unfold detailedGameCore Concrete.scheme at hdetailedHash
  change (Concrete.precomputedKeygen >>= fun key =>
    detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2).IsQueryBoundP
      IsHashQuery q at hdetailedHash
  exact (ExactQueryCount.ExactPredicateQueryCount.bind_right_of_mem_support
    ExactQueryCount.ExactPredicateQueryCount.precomputedKeygen_hashCount
    hdetailedHash key hkey).2

theorem keygen_hashQueryCount_le
    (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    treeHashQueryCount treeHeight ≤ q := by
  have hdetailed :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  have hdetailedHash :
      (detailedGameCore Concrete.scheme adversary).IsQueryBoundP IsHashQuery q :=
    (OracleComp.isQueryBoundP_congr_pred (p' := IsHashQuery)
      (fun input => by cases input <;> simp [IsHashQuery])).mp hdetailed
  unfold detailedGameCore Concrete.scheme at hdetailedHash
  change (Concrete.precomputedKeygen >>= fun key =>
    detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2).IsQueryBoundP
      IsHashQuery q at hdetailedHash
  exact ExactQueryCount.ExactPredicateQueryCount.le_of_isQueryBoundP
    ExactQueryCount.ExactPredicateQueryCount.precomputedKeygen_hashCount
    (OracleComp.IsQueryBoundP.of_bind_left hdetailedHash)

namespace CappedChain

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      |>.IsQueryBoundP (· matches .inr _)
        (q - treeHashQueryCount treeHeight) := by
  have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
    apply support_simulateQ_run'_subset romImpl Concrete.scheme.keygen ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨keyResult, hkeyResult, rfl⟩
  have hkeyPrecomputed : keyResult.1 ∈ support Concrete.precomputedKeygen := by
    simpa [Concrete.scheme] using hkeySupport
  have hcontinuation := detailedGameAfterKeygen_hashQueryBound_sub_keygen
    adversary q hbound keyResult.1 hkeyPrecomputed
  have hcontinuationStandard :
      (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1
        keyResult.1.2).IsQueryBoundP (· matches .inr _)
          (q - treeHashQueryCount treeHeight) :=
    (OracleComp.isQueryBoundP_congr_pred (p' := IsHashQuery)
      (fun input => by cases input <;> simp [IsHashQuery])).mpr hcontinuation
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1
      keyResult.1.2)).mp hcontinuationStandard

end CappedChain

end XmssSecurity
