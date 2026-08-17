import XmssSecurity.CappedGlobalChainHighSigningSimulator
import XmssSecurity.CappedGlobalChainHighAttackerHashPlan

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def GlobalChainProbeRelevantInput
    (secretKey : SecretKey) (input : HashInput) : Prop :=
  globalChainInputProbe? secretKey.parameter input ≠ none ∨
    globalLeafInputData? secretKey.parameter input ≠ none

noncomputable instance (secretKey : SecretKey) :
    DecidablePred (GlobalChainProbeRelevantInput secretKey) :=
  Classical.decPred _

theorem globalFilteredCausalAttackerHashPlan_eq_cached_or_fresh_of_irrelevant
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hirrelevant : ¬GlobalChainProbeRelevantInput secretKey input) :
    (∃ output, globalFilteredCausalAttackerHashPlan secretKey input state =
        .cached output) ∨
      globalFilteredCausalAttackerHashPlan secretKey input state = .fresh := by
  classical
  rw [GlobalChainProbeRelevantInput, not_or] at hirrelevant
  have hchain : globalChainInputProbe? secretKey.parameter input = none := by
    by_contra hne
    exact hirrelevant.1 hne
  have hleaf : globalLeafInputData? secretKey.parameter input = none := by
    by_contra hne
    exact hirrelevant.2 hne
  by_cases hcache : state.cache input = none
  · right
    rw [globalFilteredCausalAttackerHashPlan, hcache,
      globalFilteredCausalUncachedAttackerHashPlan.eq_def, hchain,
      globalFilteredCausalLeafHashPlan.eq_def, hleaf]
  · left
    obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcache
    exact ⟨output, by rw [globalFilteredCausalAttackerHashPlan, houtput]⟩

theorem globalCausalAttackerHashQueryFromHigh_irrelevant_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hirrelevant : ¬GlobalChainProbeRelevantInput secretKey input) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  rcases globalFilteredCausalAttackerHashPlan_eq_cached_or_fresh_of_irrelevant
      secretKey input state hirrelevant with ⟨output, hplan⟩ | hplan
  · rw [hplan]
    simp
  · rw [hplan]
    exact globalCausalHashQuery_run_isProbeQueryBoundP input
      (globalCausalRecordedState secretKey input state)

theorem globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (globalCausalRevealHashQueryFromHigh high secretKey input state index)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalRevealHashQueryFromHigh
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
  intro value _hvalue
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  generalize hplan :
    globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact (globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)).mono (by omega)
  | reveal index =>
      exact (globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP high
        secretKey input state index).mono (by omega)
  | probeThenFresh index target =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP index target)
      intro _ _
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)

theorem globalFilteredCausalSigningAttempt_isProbeQueryBoundP
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSigningAttempt keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalFilteredCausalSigningAttempt
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      Concrete.signingRandomness 0)
  intro randomness _hrandomness
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      ((simulateQ randomOracle
        (Concrete.encodingHash keyView.secretKey.parameter request.epoch
          request.message randomness)).run state.cache) 0)
  intro encoded _hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
    exact OracleComp.isQueryBoundP_pure
      (p := RevealProbeOracleSimulation.IsProbeQuery)
        (none, { state with cache := encoded.2 }) 0
  | some encoding =>
    apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (revealGlobalSignatureChains_run_isProbeQueryBoundP request encoding
        allChains (Concrete.CacheReplay.signWithEncoding keyView.cache
          keyView.secretKey request.epoch randomness encoding)
        { state with cache := encoded.2 })
    intro result _hresult
    exact OracleComp.isQueryBoundP_pure
      (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem globalFilteredCausalSignBoundedAttempts_isProbeQueryBoundP
    (attempts : Nat) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSignBoundedAttempts attempts keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction attempts generalizing state with
  | zero =>
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (none, state) 0
  | succ attempts ih =>
      rw [globalFilteredCausalSignBoundedAttempts]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFilteredCausalSigningAttempt_isProbeQueryBoundP keyView request
          state)
      intro result _hresult
      cases result.1 with
      | none => exact ih result.2
      | some signature =>
          exact OracleComp.isQueryBoundP_pure
            (p := RevealProbeOracleSimulation.IsProbeQuery)
              (some signature, result.2) 0

theorem globalFilteredCausalSigningQuery_isProbeQueryBoundP
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSigningQuery keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalFilteredCausalSigningQuery
  exact globalFilteredCausalSignBoundedAttempts_isProbeQueryBoundP
    signingAttemptLimit keyView request state

end XmssSecurity.CappedChain
