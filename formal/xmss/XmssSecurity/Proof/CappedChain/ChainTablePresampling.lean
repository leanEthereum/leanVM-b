import XmssSecurity.Proof.ChainTablePresampling
import XmssSecurity.Proof.MixedOraclePresampling
import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

abbrev ProgrammedFixedChainKeygenView :=
  XmssSecurity.ProgrammedFixedChainKeygenView

noncomputable def Concrete.keygenAfterParameter
    (parameter : PublicParameter) :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let secret ← liftM Concrete.sampleSecret
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩,
    Concrete.precomputedSecretKey parameter secret cache)

theorem Concrete.keygen_eq_samplePublicParameter_bind :
    Concrete.precomputedKeygen =
      (liftM Concrete.samplePublicParameter >>= Concrete.keygenAfterParameter) := by
  unfold Concrete.precomputedKeygen Concrete.keygenAfterParameter
  rfl

/-- After separating the public-parameter draw, every candidate fixed-chain edge can be front-loaded before the remainder of key generation. -/
theorem evalDist_keygen_eq_presample_chainTableTrace
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl Concrete.precomputedKeygen).run' ∅] =
      𝒟[Concrete.samplePublicParameter >>= fun parameter => do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl (Concrete.keygenAfterParameter parameter)).run' trace.2] := by
  rw [Concrete.keygen_eq_samplePublicParameter_bind, simulateQ_bind]
  change 𝒟[(simulateQ
    (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (liftM Concrete.samplePublicParameter) >>= fun parameter =>
      simulateQ xmssRomImpl (Concrete.keygenAfterParameter parameter)).run' ∅] = _
  rw [roSim.run'_liftM_bind]
  exact evalDist_samplePublicParameter_then_xmssRom_eq_presample_chainTableTrace
    Concrete.keygenAfterParameter chain table

noncomputable def Concrete.detailedGameAfterParameter
    (adversary : Adversary Concrete.scheme) (parameter : PublicParameter) :
    OracleComp OracleWorld GameOutcome := do
  let keys ← Concrete.keygenAfterParameter parameter
  detailedGameAfterKeygen Concrete.scheme adversary keys.1 keys.2

theorem Concrete.detailedGameCore_eq_samplePublicParameter_bind
    (adversary : Adversary Concrete.scheme) :
    detailedGameCore Concrete.scheme adversary =
      (liftM Concrete.samplePublicParameter >>=
        Concrete.detailedGameAfterParameter adversary) := by
  unfold detailedGameCore Concrete.detailedGameAfterParameter
  change (Concrete.precomputedKeygen >>= fun keys =>
    detailedGameAfterKeygen Concrete.scheme adversary keys.1 keys.2) = _
  rw [Concrete.keygen_eq_samplePublicParameter_bind]
  simp only [bind_assoc]

/-- The full detailed game admits candidate fixed-chain presampling after the real public parameter is sampled. -/
theorem evalDist_detailedGame_eq_presample_chainTableTrace
    (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl
      (detailedGameCore Concrete.scheme adversary)).run' ∅] =
      𝒟[Concrete.samplePublicParameter >>= fun parameter => do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl
          (Concrete.detailedGameAfterParameter adversary parameter)).run' trace.2] := by
  rw [Concrete.detailedGameCore_eq_samplePublicParameter_bind, simulateQ_bind]
  change 𝒟[(simulateQ
    (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (liftM Concrete.samplePublicParameter) >>= fun parameter =>
      simulateQ xmssRomImpl
        (Concrete.detailedGameAfterParameter adversary parameter)).run' ∅] = _
  rw [roSim.run'_liftM_bind]
  exact evalDist_samplePublicParameter_then_xmssRom_eq_presample_chainTableTrace
    (Concrete.detailedGameAfterParameter adversary) chain table

end XmssSecurity.CappedChain
