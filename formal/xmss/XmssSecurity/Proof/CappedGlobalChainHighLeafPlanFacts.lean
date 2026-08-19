import XmssSecurity.Proof.CappedGlobalChainHighLeafCoupling

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalFilteredCausalAttackerHashPlan_eq_leafProbeThenFresh
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.leafInput secretKey.parameter epoch
      endpoints)
    (hcache : state.cache input = none)
    (hprobe : globalHiddenLeafProbe? state epoch endpoints =
      some (index, target)) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_leafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hprobe]

theorem globalFilteredCausalAttackerHashPlan_eq_leafRedirect
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) (output : HashOutput)
    (hinput : input = Concrete.CacheView.leafInput secretKey.parameter epoch
      endpoints)
    (hcache : state.cache input = none)
    (hhidden : globalHiddenLeafProbe? state epoch endpoints = none)
    (hmatch : GlobalLeafRevealsMatch state epoch endpoints)
    (hkeygen : state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) = some output) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .redirect output := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_leafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hhidden, if_pos hmatch, hkeygen]

theorem globalFilteredCausalAttackerHashPlan_eq_leafFresh_of_mismatch
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput secretKey.parameter epoch
      endpoints)
    (hcache : state.cache input = none)
    (hhidden : globalHiddenLeafProbe? state epoch endpoints = none)
    (hmatch : ¬ GlobalLeafRevealsMatch state epoch endpoints) :
    globalFilteredCausalAttackerHashPlan secretKey input state = .fresh := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_leafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hhidden, if_neg hmatch]

end XmssSecurity.CappedChain
