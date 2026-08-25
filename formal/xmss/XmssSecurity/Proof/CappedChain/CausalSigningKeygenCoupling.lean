import XmssSecurity.Proof.CacheAgreement
import XmssSecurity.Proof.ChainWalkCache
import XmssSecurity.Proof.BoundedSignProbability
import XmssSecurity.Proof.PrecomputedBoundedSignProbability
import XmssSecurity.Proof.CappedChain.TreeCacheStability
import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem simulate_sequenceFin_run_eq_pure
    {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (values : Fin n → α)
    (hrun : ∀ index,
      (simulateQ randomOracle (computation index)).run cache =
        pure (values index, cache)) :
    (simulateQ randomOracle (Concrete.sequenceFin computation)).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact Fin.elim0 index
      simp [Concrete.sequenceFin, hvalues]
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind, hrun 0]
      simp only [pure_bind]
      rw [simulateQ_bind, StateT.run_bind,
        ih (fun index => computation index.succ)
          (fun index => values index.succ) (fun index => hrun index.succ)]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem Concrete.keygen_signedChainValues_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signedChainValues keyResult.1.2 epoch encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signedChainValues largerCache
        keyResult.1.2 epoch encoding, largerCache) := by
  let values : ChainIndex → Digest := fun chain =>
    keygenChainValueTable keyResult.2 keyResult.1.2 chain
      (epoch, encoding chain)
  have hrun : ∀ chain,
      (simulateQ randomOracle
        (Concrete.chainWalk keyResult.1.2.parameter epoch chain 0
          (encoding chain).val
          (keyResult.1.2.chainStart epoch chain))).run largerCache =
        pure (values chain, largerCache) := by
    intro chain
    exact simulate_chainWalk_run_eq_pure_of_table_matches largerCache
      keyResult.1.2 chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain)
      (keygenChainValueTable_seedsMatch keyResult.2 keyResult.1.2 chain)
      ((Concrete.keygenChainValueTable_edgesMatch
        keyResult hkeyResult chain).mono hle)
      epoch (encoding chain).val (encoding chain).isLt
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun chain => Concrete.chainWalk keyResult.1.2.parameter epoch chain 0
      (encoding chain).val (keyResult.1.2.chainStart epoch chain))
    largerCache values hrun
  have hvalues : values = Concrete.CacheReplay.signedChainValues
      largerCache keyResult.1.2 epoch encoding := by
    funext chain
    exact Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeyResult
      largerCache hle epoch chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  simpa [Concrete.signedChainValues, hvalues] using hsequence

theorem TreeCacheStable.authenticationPath_run_eq_pure
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (epoch : Epoch) :
    (simulateQ randomOracle
      (Concrete.authenticationPath secretKey epoch)).run largerCache =
      pure (Concrete.CacheReplay.authenticationPath largerCache secretKey epoch,
        largerCache) := by
  have hrun : ∀ level,
      (simulateQ randomOracle
        (Concrete.treeNode secretKey.parameter secretKey.chainStart level.val
          (Concrete.authenticationPathNode epoch level) :
          OracleComp HashSpec Digest)).run largerCache =
        pure (Concrete.CacheReplay.treeNode cache secretKey.parameter
          secretKey.chainStart level.val
            (Concrete.authenticationPathNode epoch level), largerCache) := by
    intro level
    exact hstable level.val (Concrete.authenticationPathNode epoch level)
      (by omega) (authenticationPathNode_subtreeValid epoch level)
        largerCache hle
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun level => Concrete.treeNode secretKey.parameter secretKey.chainStart
      level.val (Concrete.authenticationPathNode epoch level)) largerCache
    (Concrete.CacheReplay.authenticationPath cache secretKey epoch) hrun
  rw [hstable.authenticationPath_eq secretKey cache largerCache hle epoch]
    at hsequence
  simpa [Concrete.authenticationPath] using hsequence

theorem Concrete.keygen_signWithEncoding_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signWithEncoding keyResult.1.2 epoch randomness encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        epoch randomness encoding, largerCache) := by
  unfold Concrete.signWithEncoding
  rw [simulateQ_bind, StateT.run_bind,
    Concrete.keygen_signedChainValues_run_eq_pure keyResult hkeyResult
      largerCache hle epoch encoding]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind,
    hstable.authenticationPath_run_eq_pure keyResult.1.2 keyResult.2
      largerCache hle epoch]
  simp [Concrete.CacheReplay.signWithEncoding]

theorem Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    evalDist ((simulateQ randomOracle
      (Concrete.precomputedSignAttempt
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message randomness : OracleComp HashSpec (Option Signature))).run
        largerCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.signAttempt keyResult.1.2 epoch message randomness :
          OracleComp HashSpec (Option Signature))).run largerCache) := by
  have hmaterialized :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen keyResult hkeyResult
  have hconsistent := Concrete.precomputedKeygen_support_consistent
    (Concrete.materializeCachedKeyResult keyResult) hmaterialized
  unfold Concrete.precomputedSignAttempt Concrete.signAttempt
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [Concrete.materializePrecomputation,
    Concrete.precomputedSecretKey]
  apply evalDist_bind_congr
  intro digestResult hdigestResult
  have hdigestLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.encodingHash keyResult.1.2.parameter epoch message randomness)
      largerCache digestResult (by
        simpa [Concrete.materializePrecomputation] using hdigestResult)
  cases hdecode : TargetSum.decodeDigest digestResult.1 with
  | none =>
    simp only
  | some encoding =>
    simp only
    rw [simulateQ_map, StateT.run_map]
    rw [Concrete.keygen_signWithEncoding_run_eq_pure keyResult hkeyResult
      hstable digestResult.2 (hle.trans hdigestLe)
      epoch randomness encoding]
    simp only [Functor.map]
    have hsignature := hconsistent digestResult.2 (hle.trans hdigestLe)
      epoch randomness encoding
    change Concrete.precomputedSignWithEncoding
      (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
        epoch randomness encoding =
      Concrete.CacheReplay.signWithEncoding digestResult.2 keyResult.1.2
        epoch randomness encoding at hsignature
    simp only [Concrete.materializePrecomputation,
      Concrete.precomputedSecretKey] at hsignature
    rw [hsignature]
    rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    (attempts : Nat)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) :
    evalDist ((simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts attempts
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message)).run largerCache) =
      evalDist ((simulateQ romImpl
        (Concrete.signBoundedAttempts attempts keyResult.1.2 epoch message)).run
          largerCache) := by
  induction attempts generalizing largerCache with
  | zero => rfl
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq,
        Concrete.signBoundedAttempts_run_succ_eq]
      apply evalDist_bind_congr
      intro randomness _hrandomness
      calc
        evalDist ((simulateQ randomOracle
              (Concrete.precomputedSignAttempt
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  epoch message randomness :
                    OracleComp HashSpec (Option Signature))).run largerCache >>=
            Concrete.precomputedSignBoundedAttemptsContinuation attempts
              (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                epoch message) =
            evalDist ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.precomputedSignBoundedAttemptsContinuation attempts
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  epoch message) := by
          rw [evalDist_bind, evalDist_bind,
            Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
              keyResult hkeyResult hstable largerCache hle epoch message randomness]
        _ = evalDist ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.signBoundedAttemptsContinuation attempts keyResult.1.2
                epoch message) := by
          apply evalDist_bind_congr
          intro result hresult
          cases hoption : result.1 with
          | none =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]
              apply ih result.2
              exact hle.trans (Concrete.CacheReplay.randomOracle_cache_le
                (Concrete.signAttempt keyResult.1.2 epoch message randomness :
                  OracleComp HashSpec (Option Signature)) largerCache result hresult)
          | some signature =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]

theorem Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (message : Message) :
    evalDist ((simulateQ romImpl
      (Concrete.precomputedCappedSign
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          epoch message)).run largerCache) =
      evalDist ((simulateQ romImpl
        (Concrete.cappedSign keyResult.1.2 epoch message)).run
          largerCache) := by
  rw [Concrete.precomputedCappedSign, Concrete.cappedSign_eq]
  exact Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    signingAttemptLimit keyResult hkeyResult hstable largerCache hle epoch message

end XmssSecurity.CappedChain
