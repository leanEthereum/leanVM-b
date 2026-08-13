import XmssSecurity.CausalFilteredResampling

open OracleComp OracleSpec

namespace XmssSecurity

theorem chainInputProbe?_eq_some_iff
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) (index : ChainValueIndex) (target : Digest) :
    chainInputProbe? parameter selected input = some (index, target) ↔
      ∃ step : ChainStep,
        input = Concrete.CacheView.chainInput parameter index.1 selected
          step target ∧ index.2 = chainStepDigit step := by
  constructor
  · intro hprobe
    unfold chainInputProbe? at hprobe
    split at hprobe
    · rename_i hexists
      let data := hexists.choose
      have hdata := hexists.choose_spec
      simp only [Option.some.injEq, Prod.mk.injEq] at hprobe
      obtain ⟨hindex, htarget⟩ := hprobe
      refine ⟨data.2.1, ?_, ?_⟩
      · rw [hdata]
        rw [← congrArg Prod.fst hindex, ← htarget]
      · exact (congrArg Prod.snd hindex).symm
    · simp at hprobe
  · rintro ⟨step, rfl, hindex⟩
    rw [chainInputProbe?_chainInput]
    rw [← hindex]

theorem programmedActual_left_chainValue_eq_table
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (index : ChainValueIndex) :
    Wots.walk
        (Concrete.CacheView.chainStep left.cache left.secretKey.parameter
          index.1 selected)
        0 index.2.val (left.secretKey.chainStart index.1 selected) =
      right.2 index := by
  change keygenChainValueTable left.cache left.secretKey selected index =
    right.2 index
  rw [programmedWarmedFixedChainKeygen_support_table
    selected left hleftSupport]
  exact congrFun hrel.1.1 index

theorem programmedActual_left_cache_chainInput_eq_none_of_probe_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmiss : right.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨step, hinput, hindex⟩ :=
    (chainInputProbe?_eq_some_iff left.secretKey.parameter selected input
      index target).mp hprobe
  rw [hinput]
  apply Concrete.keygen_cache_chainInput_eq_none_of_ne left.keyResult
    (programmedWarmedFixedChainKeygen_support_keyResult
      selected left hleftSupport)
  intro heq
  apply hmiss
  rw [← programmedActual_left_chainValue_eq_table selected left right hrel
    hleftSupport index]
  rw [hindex]
  simpa [ProgrammedFixedChainKeygenView.keyResult, chainStepDigit] using heq.symm

theorem programmedActual_current_caches_eq_of_probe_miss
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (input : HashInput) (index : ChainValueIndex) (target : Digest)
    (hprobe : chainInputProbe? left.secretKey.parameter selected input =
      some (index, target))
    (hmiss : right.2 index ≠ target) :
    leftCache input = rightState.cache input := by
  rcases hstate.2.1 input with hagrees | ⟨hbase, hright⟩
  · exact hagrees
  · rw [hbase, hright]
    exact programmedActual_left_cache_chainInput_eq_none_of_probe_miss
      selected left right hrel hleftSupport input index target hprobe hmiss

noncomputable def filteredProbingAttackerHashQueryAt
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : Option (ChainValueIndex × Digest) →
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState)
  | none => (filteredCausalAttackerHashQuery
      secretKey selected input).run state
  | some probe =>
      match state.revealed probe.1 with
      | some _ => (filteredCausalAttackerHashQuery
          secretKey selected input).run state
      | none => do
          let _ ← RevealProbeOracleSimulation.probeQuery probe.1 probe.2
          (filteredCausalAttackerHashQuery secretKey selected input).run state

noncomputable def filteredProbingAttackerHashQuery
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      HashOutput := fun state =>
  filteredProbingAttackerHashQueryAt secretKey selected input state
    (chainInputProbe? secretKey.parameter selected input)

theorem filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredCausalAttackerHashQuery secretKey selected input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [filteredCausalAttackerHashQuery_run]
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output => simp
  | conditioned digest =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest digest) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (output,
          { (causalRecordedState secretKey selected input state) with
            cache := (causalRecordedState secretKey selected input state).cache.cacheQuery
              input output }) 0
  | fresh =>
      exact causalHashQuery_run_isProbeQueryBoundP input
        (causalRecordedState secretKey selected input state)
  | reveal index =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest value) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (output,
          causalRevealResultState secretKey selected input state
            index value output) 0

theorem filteredProbingAttackerHashQueryAt_isProbeQueryBoundP
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    (filteredProbingAttackerHashQueryAt secretKey selected input state probe)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  cases probe with
  | none =>
      simpa only [filteredProbingAttackerHashQueryAt] using
        (filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
          secretKey selected input state).mono (by omega)
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          simpa only [filteredProbingAttackerHashQueryAt, hrevealed] using
            (filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
              secretKey selected input state).mono (by omega)
      | none =>
          rw [filteredProbingAttackerHashQueryAt, hrevealed]
          apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
            (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP
              probe.1 probe.2)
          intro _ _hunit
          exact filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
            secretKey selected input state

end XmssSecurity
