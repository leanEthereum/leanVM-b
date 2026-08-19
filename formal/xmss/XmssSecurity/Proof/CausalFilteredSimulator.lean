import XmssSecurity.Proof.CausalSigningKeygenCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def ProgrammedActualKeygenReplayRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) : Prop :=
  ProgrammedActualKeygenCacheRelation chain left right ∧
    ∃ values,
      TreeValuesReplay left.secretKey.parameter left.secretKey.chainStart
        left.cache allTreeValueIndices values ∧
      TreeValuesReplay right.1.secretKey.parameter
        right.1.secretKey.chainStart right.1.cache allTreeValueIndices values

theorem relTriple_coupledWarmedFixedChainKeygen_withBase_replay
    (chain : ChainIndex) :
    RelTriple
      (coupledWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBase chain)
      (ProgrammedActualKeygenReplayRelation chain) := by
  unfold coupledWarmedFixedChainKeygen
    coupledWarmedFixedChainKeygenWithBase
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_withBase_cache
      leftParameter chain)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨?_, leftView.values, ?_, ?_⟩
  · refine ⟨⟨hview.1.1, ?_, hview.1.2.1,
      hview.1.2.2.2.2.2.2⟩, hview.2⟩
    exact congrArg (fun root => PublicKey.mk root leftParameter)
      hview.1.2.2.2.2.2.1
  · exact hview.1.2.2.2.1
  · rw [hview.1.2.2.1]
    exact hview.1.2.2.2.2.1

theorem relTriple_programmedWarmedFixedChainKeygen_withBase_replay
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))
      (ProgrammedActualKeygenReplayRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain).symm
  exact relTriple_of_evalDist_eq_right
    (evalDist_coupledWarmedFixedChainKeygenWithBase_eq_actual chain)
      (relTriple_coupledWarmedFixedChainKeygen_withBase_replay chain)

def ProgrammedActualKeygenFullRelation
    (chain : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) : Prop :=
  ProgrammedActualKeygenReplayRelation chain left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache

theorem relTriple_programmedWarmedFixedChainKeygen_withBase_full
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base => pure (keyView, base))
      (ProgrammedActualKeygenFullRelation chain) := by
  apply relTriple_post_mono
    (relTriple_with_support
      (relTriple_programmedWarmedFixedChainKeygen_withBase_replay chain))
  intro left right hrel
  refine ⟨hrel.1, ?_, ?_⟩
  · exact programmedWarmedFixedChainKeygen_support_treeCacheStable
      chain left hrel.2.1
  · exact actualFixedChainKeygen_support_treeCacheStable chain right.1
      (actualWithBase_support_keyView chain right hrel.2.2)

def SelectedChainHashInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Prop :=
  ∃ epoch step,
    AtHashAddress parameter (.chain epoch selected step) input

noncomputable def outsideChainOnly
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) : QueryCache HashSpec := by
  classical
  exact fun input => if OutsideChainHashInput parameter selected input then
      cache input
    else
      none

theorem outsideChainOnly_of_outside
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : OutsideChainHashInput parameter selected input) :
    outsideChainOnly parameter selected cache input = cache input := by
  simp [outsideChainOnly, hinput]

theorem outsideChainOnly_of_not_outside
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : ¬ OutsideChainHashInput parameter selected input) :
    outsideChainOnly parameter selected cache input = none := by
  simp [outsideChainOnly, hinput]

noncomputable def filteredCausalKeygenState
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    CausalHashState := {
  cache := outsideChainOnly view.secretKey.parameter selected view.cache
  keygenCache := view.cache
  revealed := fun _ => none
  probes := []
}

@[simp]
theorem filteredCausalKeygenState_cache
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    (filteredCausalKeygenState selected view).cache =
      outsideChainOnly view.secretKey.parameter selected view.cache := rfl

@[simp]
theorem filteredCausalKeygenState_keygenCache
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    (filteredCausalKeygenState selected view).keygenCache = view.cache := rfl

@[simp]
theorem filteredCausalKeygenState_revealed
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (index : ChainValueIndex) :
    (filteredCausalKeygenState selected view).revealed index = none := rfl

theorem programmedActual_filteredKeygen_cachesAgree
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected)) :
    HashCachesAgreeOn
      (SigningComparableHashInput left.secretKey.parameter selected)
      left.cache (filteredCausalKeygenState selected right.1).cache := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hleftParameter := left.parameter_eq hleftKey
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter := hleftParameter.symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  intro input hinput
  rcases hinput with houtside | ⟨epoch, message, randomness, rfl⟩
  · rw [filteredCausalKeygenState_cache]
    have houtsideRight : OutsideChainHashInput
        right.1.secretKey.parameter selected input := by
      rw [← hparameter]
      exact houtside
    rw [outsideChainOnly_of_outside _ _ _ _ houtsideRight]
    apply hrel.1.2 input
    rw [hleftParameter]
    exact houtside
  · rw [filteredCausalKeygenState_cache, ← hparameter]
    have hnotOutside : ¬ OutsideChainHashInput left.secretKey.parameter
        selected (Concrete.CacheView.encodingInput left.secretKey.parameter
          epoch (message, randomness)) := by
      rintro ⟨chainEpoch, candidate, step, _hne, hchain⟩
      have hencoding : AtHashAddress left.secretKey.parameter (.encoding epoch)
          (Concrete.CacheView.encodingInput left.secretKey.parameter epoch
            (message, randomness)) := by
        simp [Concrete.CacheView.encodingInput]
      have haddress := atHashAddress_unique left.secretKey.parameter
        (.chain chainEpoch candidate step) (.encoding epoch)
        (Concrete.CacheView.encodingInput left.secretKey.parameter epoch
          (message, randomness)) hchain hencoding
      simp at haddress
    rw [outsideChainOnly_of_not_outside _ _ _ _ hnotOutside]
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey epoch (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter epoch (message, randomness)) = none at hleftNone
    exact hleftNone

theorem programmedActual_filteredKeygen_cache_le
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected)) :
    (filteredCausalKeygenState selected right.1).cache ≤ left.cache := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  intro input output houtput
  rw [filteredCausalKeygenState_cache] at houtput
  by_cases houtside : OutsideChainHashInput
      right.1.secretKey.parameter selected input
  · rw [outsideChainOnly_of_outside _ _ _ _ houtside] at houtput
    have houtsideLeft : OutsideChainHashInput
        left.publicKey.parameter selected input := by
      rw [left.parameter_eq hleftKey, hparameter]
      exact houtside
    rw [hrel.2 input houtsideLeft]
    exact houtput
  · rw [outsideChainOnly_of_not_outside _ _ _ _ houtside] at houtput
    simp at houtput

def FilteredCacheExtensionRelation
    (leftBase left right : QueryCache HashSpec) : Prop :=
  ∀ input,
    left input = right input ∨
      (left input = leftBase input ∧ right input = none)

theorem FilteredCacheExtensionRelation.right_le_left
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right) :
    right ≤ left := by
  intro input output hright
  rcases hrel input with hagrees | ⟨_hbase, hnone⟩
  · rw [hagrees]
    exact hright
  · rw [hnone] at hright
    simp at hright

theorem FilteredCacheExtensionRelation.cacheQuery
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput) (output : HashOutput) :
    FilteredCacheExtensionRelation leftBase
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hrel candidate

theorem programmedActual_filteredKeygen_extensionRelation
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected)) :
    FilteredCacheExtensionRelation left.cache left.cache
      (filteredCausalKeygenState selected right.1).cache := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  intro input
  rw [filteredCausalKeygenState_cache]
  by_cases houtside : OutsideChainHashInput
      right.1.secretKey.parameter selected input
  · left
    rw [outsideChainOnly_of_outside _ _ _ _ houtside]
    have houtsideLeft : OutsideChainHashInput
        left.publicKey.parameter selected input := by
      rw [left.parameter_eq hleftKey, hparameter]
      exact houtside
    exact hrel.2 input houtsideLeft
  · right
    exact ⟨rfl, outsideChainOnly_of_not_outside
      right.1.secretKey.parameter selected right.1.cache input houtside⟩

theorem relTriple_randomOracle_run_of_cachesAgreeOn_subset
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (input : HashInput) (hinput : inputs input)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hsubset : right ≤ left) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          rightResult.2 ≤ leftResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        QueryCache.cacheQuery_mono hsubset input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hsubset⟩

theorem relTriple_randomOracle_run_of_cachesAgreeOn_filtered
    (inputs : HashInput → Prop)
    (leftBase left right : QueryCache HashSpec)
    (input : HashInput) (hinput : inputs input)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

def EncodingFilteredResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (leftResult rightResult : Digest × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    HashCachesAgreeOn (SigningComparableHashInput parameter selected)
      leftResult.2 rightResult.2 ∧
    initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2 ∧
    FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2 ∧
    Concrete.CacheView.encodingHash leftResult.2 parameter epoch
      (message, randomness) = leftResult.1 ∧
    Concrete.CacheView.encodingHash rightResult.2 parameter epoch
      (message, randomness) = rightResult.1

theorem relTriple_encodingHash_run_of_signingComparableCaches_filtered
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (SigningComparableHashInput parameter selected) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (EncodingFilteredResultRelation parameter selected leftBase left right
        epoch message randomness) := by
  have hquery := relTriple_randomOracle_run_of_cachesAgreeOn_filtered
    (SigningComparableHashInput parameter selected) leftBase left right
      (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
      (Or.inr ⟨epoch, message, randomness, rfl⟩) hagrees hfiltered
  have hmapped : RelTriple
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run left)
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn
            (SigningComparableHashInput parameter selected)
            leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
    apply relTriple_map
    apply relTriple_post_mono hquery
    intro leftResult rightResult hresult
    exact ⟨congrArg truncateHash hresult.1, hresult.2⟩
  have hstrengthened := relTriple_strengthen_support hmapped
    (fun result hresult => encodingHash_run_cache_eq parameter left result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
    (fun result hresult => encodingHash_run_cache_eq parameter right result.2
      epoch message randomness result.1 (by
        simpa [Concrete.encodingHash, Concrete.tweakableHash,
          Concrete.oracleHash, Concrete.CacheView.encodingInput,
          map_eq_bind_pure_comp] using hresult))
  apply relTriple_post_mono hstrengthened
  intro leftResult rightResult hresult
  exact ⟨hresult.1.1, hresult.1.2.1, hresult.1.2.2.1,
    hresult.1.2.2.2.1, hresult.1.2.2.2.2, hresult.2.1, hresult.2.2⟩

theorem Concrete.keygen_signWithEncoding_eq_base
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        epoch randomness encoding =
      Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
        epoch randomness encoding := by
  unfold Concrete.CacheReplay.signWithEncoding
  congr 1
  · funext chain
    calc
      Concrete.CacheReplay.signedChainValues largerCache keyResult.1.2
          epoch encoding chain =
        keygenChainValueTable keyResult.2 keyResult.1.2 chain
          (epoch, encoding chain) :=
        Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult largerCache hle epoch randomness encoding chain
      _ = Concrete.CacheReplay.signedChainValues keyResult.2 keyResult.1.2
          epoch encoding chain :=
        (Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult keyResult.2 le_rfl epoch randomness encoding
            chain).symm
  · exact (TreeCacheStable.authenticationPath_eq keyResult.1.2 keyResult.2
      hstable largerCache hle epoch).symm

noncomputable def filteredCausalSigningQuery
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (Option Signature × CausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash keyView.secretKey.parameter request.epoch
        request.message randomness)).run state.cache)
  let encodedState := { state with cache := encoded.2 }
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encodedState)
  | some encoding => do
      let value ← RevealProbeOracleSimulation.revealQuery
        (request.epoch, encoding selected)
      let signature := replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding) selected value
      pure (some signature,
        encodedState.recordReveal (request.epoch, encoding selected) value)

def FilteredCausalStateRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState) : Prop :=
  HashCachesAgreeOn (SigningComparableHashInput parameter selected)
      leftCache rightState.cache ∧
    FilteredCacheExtensionRelation leftBase leftCache rightState.cache ∧
    leftBase ≤ leftCache ∧
    rightState.keygenCache = rightBase ∧
    CausalRevealsAgree table rightState

theorem FilteredCausalStateRelation.causalRecordedStateSetCache
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (newLeft newRight : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (SigningComparableHashInput parameter selected) newLeft newRight)
    (hfiltered : FilteredCacheExtensionRelation leftBase newLeft newRight)
    (hle : leftCache ≤ newLeft) :
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      newLeft
      { (causalRecordedState secretKey selected input rightState) with
        cache := newRight } := by
  refine ⟨hagrees, hfiltered, hstate.2.2.1.trans hle, ?_, ?_⟩
  · simpa using hstate.2.2.2.1
  · exact (hstate.2.2.2.2.causalRecordedState
      secretKey selected input).setCache _

theorem FilteredCausalStateRelation.causalRecordedState
    (hstate : FilteredCausalStateRelation parameter selected leftBase rightBase
      table leftCache rightState)
    (secretKey : SecretKey) (input : HashInput) :
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftCache (causalRecordedState secretKey selected input rightState) := by
  refine ⟨?_, ?_, hstate.2.2.1, ?_,
    hstate.2.2.2.2.causalRecordedState secretKey selected input⟩
  · simpa using hstate.1
  · simpa using hstate.2.1
  · simpa using hstate.2.2.2.1

theorem programmedActual_filteredKeygen_stateRelation
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected)) :
    FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 left.cache
        (filteredCausalKeygenState selected right.1) := by
  refine ⟨programmedActual_filteredKeygen_cachesAgree selected left right
      hrel hleftSupport hrightSupport,
    programmedActual_filteredKeygen_extensionRelation selected left right hrel.1
      hleftSupport hrightSupport,
    le_rfl, rfl, ?_⟩
  intro index value hvalue
  simp at hvalue

inductive FilteredCausalHashPlan where
  | cached (output : HashOutput)
  | reveal (index : ChainValueIndex)
  | conditioned (digest : Digest)
  | fresh

noncomputable def filteredCausalUncachedHashPlanAt
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState) :
    Option (ChainValueIndex × Digest) → FilteredCausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.val + 1 < chainLength then
              .reveal (index.1, ⟨index.2.val + 1, hnext⟩)
            else
              .fresh
          else
            .fresh
      | none => .fresh
  | none =>
      match state.keygenCache
          (keygenLeafTargetInput secretKey state.keygenCache input) with
      | some output => .conditioned (truncateHash output)
      | none => .fresh

noncomputable def filteredCausalUncachedHashPlan
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredCausalHashPlan :=
  filteredCausalUncachedHashPlanAt secretKey input state
    (chainInputProbe? secretKey.parameter selected input)

noncomputable def filteredCausalAttackerHashPlan
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) : FilteredCausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => filteredCausalUncachedHashPlan secretKey selected input state

noncomputable def filteredCausalAttackerHashQuery
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      HashOutput := fun state =>
  let recorded := causalRecordedState secretKey selected input state
  match filteredCausalAttackerHashPlan secretKey selected input state with
  | .cached output => pure (output, recorded)
  | .reveal index => causalRevealHashQuery secretKey selected input state index
  | .conditioned digest => do
      let output ← RevealProbeOracleSimulation.liftProbComp
        (Rom.sampleHashOutputWithDigest digest)
      pure (output,
        { recorded with cache := recorded.cache.cacheQuery input output })
  | .fresh => (causalHashQuery input).run recorded

theorem filteredCausalAttackerHashQuery_run
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredCausalAttackerHashQuery secretKey selected input).run state =
      (let recorded := causalRecordedState secretKey selected input state
        match filteredCausalAttackerHashPlan secretKey selected input state with
        | .cached output => pure (output, recorded)
        | .reveal index =>
            causalRevealHashQuery secretKey selected input state index
        | .conditioned digest => do
            let output ← RevealProbeOracleSimulation.liftProbComp
              (Rom.sampleHashOutputWithDigest digest)
            pure (output,
              { recorded with
                cache := recorded.cache.cacheQuery input output })
        | .fresh => (causalHashQuery input).run recorded) := rfl

def FilteredSigningResultRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    FilteredCausalStateRelation parameter selected leftBase rightBase table
      leftResult.2 rightResult.1.2

set_option maxRecDepth 100000 in
theorem relTriple_programmed_filteredCausalSigningQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState)
    (hstate : FilteredCausalStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.singleAttemptScheme.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (filteredCausalSigningQuery right.1 selected request rightState)).run)
      (FilteredSigningResultRelation left.secretKey.parameter selected
        left.cache right.1.cache right.2) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (left.parameter_eq hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  simp only [Concrete.singleAttemptScheme]
  rw [Concrete.sign_run_eq]
  unfold filteredCausalSigningQuery
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← Concrete.signingRandomness_eq]
  apply relTriple_bind (relTriple_refl Concrete.signingRandomness)
  intro leftRandomness rightRandomness hrandomness
  subst rightRandomness
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_encodingHash_run_of_signingComparableCaches_filtered
      left.secretKey.parameter selected left.cache leftCache rightState.cache
      hstate.1 hstate.2.1 request.epoch request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.1
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      unfold FilteredSigningResultRelation FilteredCausalStateRelation
      refine ⟨rfl, hencoded.2.1,
        hencoded.2.2.2.2.1,
        hstate.2.2.1.trans hencoded.2.2.1, hstate.2.2.2.1,
        hstate.2.2.2.2.setCache rightEncoded.2⟩
  | some encoding =>
      simp only
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey request.epoch
              leftRandomness encoding)).run leftEncoded.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftEncoded.2
              left.secretKey request.epoch leftRandomness encoding,
                leftEncoded.2) := by
        simpa [ProgrammedFixedChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.2.1 leftEncoded.2
            (hstate.2.2.1.trans hencoded.2.2.1) request.epoch
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply]
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      apply relTriple_pure_pure
      unfold FilteredSigningResultRelation FilteredCausalStateRelation
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.2.1 leftEncoded.2
        (hstate.2.2.1.trans hencoded.2.2.1) request.epoch leftRandomness encoding
      have hbase := keygenViews_signWithEncoding_eq_replaced selected left right
        hrel.1 hleftSupport hrightSupport request.epoch leftRandomness encoding
      have hsignature :
          Concrete.CacheReplay.signWithEncoding leftEncoded.2 left.secretKey
              request.epoch leftRandomness encoding =
            replaceSignatureChainValue
              (Concrete.CacheReplay.signWithEncoding right.1.cache
                right.1.secretKey request.epoch leftRandomness encoding)
              selected (right.2 (request.epoch, encoding selected)) :=
        hleftStable.trans hbase
      refine ⟨congrArg some hsignature, hencoded.2.1,
        hencoded.2.2.2.2.1,
        hstate.2.2.1.trans hencoded.2.2.1, hstate.2.2.2.1, ?_⟩
      exact (hstate.2.2.2.2.setCache rightEncoded.2).recordReveal
        (request.epoch, encoding selected)
        (right.2 (request.epoch, encoding selected)) rfl

end XmssSecurity
