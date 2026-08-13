import XmssSecurity.CausalSigningKeygenCoupling

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

def SelectedKeygenSensitiveHashInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Prop :=
  SelectedChainHashInput parameter selected input ∨
    ∃ epoch, AtHashAddress parameter (.leaf epoch) input

noncomputable def withoutSelectedKeygenInputs
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) : QueryCache HashSpec := by
  classical
  exact fun input => if SelectedKeygenSensitiveHashInput
      parameter selected input then
      none
    else
      cache input

theorem withoutSelectedKeygenInputs_selected
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : SelectedChainHashInput parameter selected input) :
    withoutSelectedKeygenInputs parameter selected cache input = none := by
  simp [withoutSelectedKeygenInputs, SelectedKeygenSensitiveHashInput, hinput]

theorem withoutSelectedKeygenInputs_leaf
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (epoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf epoch) input) :
    withoutSelectedKeygenInputs parameter selected cache input = none := by
  unfold withoutSelectedKeygenInputs
  rw [if_pos]
  exact Or.inr ⟨epoch, hinput⟩

theorem withoutSelectedKeygenInputs_outside
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : OutsideChainHashInput parameter selected input) :
    withoutSelectedKeygenInputs parameter selected cache input = cache input := by
  have hnot : ¬ SelectedKeygenSensitiveHashInput
      parameter selected input := by
    rintro (hselected | hleaf)
    · obtain ⟨selectedEpoch, selectedStep, hselected⟩ := hselected
      obtain ⟨outsideEpoch, candidate, outsideStep, hne, houtside⟩ := hinput
      have haddress := atHashAddress_unique parameter
        (.chain selectedEpoch selected selectedStep)
        (.chain outsideEpoch candidate outsideStep) input hselected houtside
      simp only [HashDomain.chain.injEq] at haddress
      exact hne haddress.2.1.symm
    · obtain ⟨leafEpoch, hleaf⟩ := hleaf
      obtain ⟨outsideEpoch, candidate, outsideStep, _hne, houtside⟩ := hinput
      have haddress := atHashAddress_unique parameter
        (.leaf leafEpoch) (.chain outsideEpoch candidate outsideStep)
        input hleaf houtside
      simp at haddress
  simp [withoutSelectedKeygenInputs, hnot]

theorem withoutSelectedKeygenInputs_encoding
    (parameter : PublicParameter) (selected : ChainIndex)
    (cache : QueryCache HashSpec) (epoch : Epoch)
    (message : Message) (randomness : Randomness) :
    withoutSelectedKeygenInputs parameter selected cache
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) =
      cache (Concrete.CacheView.encodingInput parameter epoch
        (message, randomness)) := by
  have hnot : ¬ SelectedKeygenSensitiveHashInput parameter selected
      (Concrete.CacheView.encodingInput parameter epoch
        (message, randomness)) := by
    have hencoding : AtHashAddress parameter (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) := by
      simp [Concrete.CacheView.encodingInput]
    rintro (⟨chainEpoch, step, hchain⟩ | ⟨leafEpoch, hleaf⟩)
    · have haddress := atHashAddress_unique parameter
        (.chain chainEpoch selected step) (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) hchain hencoding
      simp at haddress
    · have haddress := atHashAddress_unique parameter
        (.leaf leafEpoch) (.encoding epoch)
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) hleaf hencoding
      simp at haddress
  simp [withoutSelectedKeygenInputs, hnot]

noncomputable def filteredCausalKeygenState
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    CausalHashState := {
  cache := withoutSelectedKeygenInputs
    view.secretKey.parameter selected view.cache
  keygenCache := view.cache
  revealed := fun _ => none
  probes := []
}

@[simp]
theorem filteredCausalKeygenState_cache
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView) :
    (filteredCausalKeygenState selected view).cache =
      withoutSelectedKeygenInputs
        view.secretKey.parameter selected view.cache := rfl

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
    rw [withoutSelectedKeygenInputs_outside _ _ _ _ houtsideRight]
    apply hrel.1.2 input
    rw [hleftParameter]
    exact houtside
  · rw [filteredCausalKeygenState_cache, ← hparameter,
      withoutSelectedKeygenInputs_encoding]
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey epoch (message, randomness)
    have hrightNone := Concrete.keygen_cache_none_encodingInput
      right.1.keyResult hrightKey epoch (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter epoch (message, randomness)) = none at hleftNone
    change right.1.cache (Concrete.CacheView.encodingInput
      right.1.secretKey.parameter epoch (message, randomness)) = none at hrightNone
    rw [← hparameter] at hrightNone
    exact hleftNone.trans hrightNone.symm

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
    leftBase ≤ leftCache ∧
    rightState.keygenCache = rightBase ∧
    CausalRevealsAgree table rightState

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
        (Concrete.scheme.sign left.publicKey left.secretKey
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
  simp only [Concrete.scheme]
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
    (relTriple_encodingHash_run_of_signingComparableCaches
      left.secretKey.parameter selected leftCache rightState.cache hstate.1
      request.epoch request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.1
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      unfold FilteredSigningResultRelation FilteredCausalStateRelation
      refine ⟨rfl, hencoded.2.1,
        hstate.2.1.trans hencoded.2.2.1, hstate.2.2.1,
        hstate.2.2.2.setCache rightEncoded.2⟩
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
            (hstate.2.1.trans hencoded.2.2.1) request.epoch
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply]
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      apply relTriple_pure_pure
      unfold FilteredSigningResultRelation FilteredCausalStateRelation
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.2.1 leftEncoded.2
        (hstate.2.1.trans hencoded.2.2.1) request.epoch leftRandomness encoding
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
        hstate.2.1.trans hencoded.2.2.1, hstate.2.2.1, ?_⟩
      exact (hstate.2.2.2.setCache rightEncoded.2).recordReveal
        (request.epoch, encoding selected)
        (right.2 (request.epoch, encoding selected)) rfl

end XmssSecurity
