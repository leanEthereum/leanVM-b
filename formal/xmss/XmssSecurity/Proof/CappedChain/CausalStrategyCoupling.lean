import XmssSecurity.Proof.CappedChain.ChainTablePresampling
import XmssSecurity.Proof.CappedChain.ChainTracedGame
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

abbrev FixedChainActionTracedResult :=
  ((ProgrammedFixedChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseFixedChainKeygenView
    (result : FixedChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, Concrete.materializePrecomputation
      result.1.1.cache result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)

noncomputable def detailedGameWithFixedChainKeygenView
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← actualFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey) keyView.cache
  pure ((keyView, execution.1), execution.2)

noncomputable def chronologicallyWarmedDetailedGame
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← chronologicallyWarmedExtractedFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey) keyView.cache
  pure ((keyView, execution.1), execution.2)

theorem erase_detailedGameWithFixedChainKeygenView
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (eraseFixedChainKeygenView <$>
        detailedGameWithFixedChainKeygenView adversary chain) =
      evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) := by
  unfold detailedGameWithFixedChainKeygenView actualFixedChainKeygen
    detailedGameWithKeygenCacheAndActionTrace
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [Concrete.scheme]
  rw [evalDist_bind, evalDist_bind]
  calc
    _ = evalDist (Concrete.materializeCachedKeyResult <$>
          (simulateQ xmssRomImpl Concrete.keygen).run ∅) >>= fun keyResult =>
        evalDist (do
          let execution ← detailedGameAfterKeygenWithActionTrace adversary
            keyResult.1.1 keyResult.1.2 keyResult.2
          pure ((keyResult, execution.1), execution.2)) := by
      rw [evalDist_map, map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro keyResult
      simp only [Function.comp_apply, pure_bind]
      rfl
    _ = _ := by
      rw [Concrete.evalDist_materialized_keygen_eq_precomputedKeygen]

theorem evalDist_detailedGameWithFixedChainKeygenView_eq_warmed
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (detailedGameWithFixedChainKeygenView adversary chain) =
      evalDist (chronologicallyWarmedDetailedGame adversary chain) := by
  unfold detailedGameWithFixedChainKeygenView
    chronologicallyWarmedDetailedGame
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed]

theorem evalDist_originalActionTracedGame_eq_erase_warmed
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) =
      evalDist (eraseFixedChainKeygenView <$>
        chronologicallyWarmedDetailedGame adversary chain) := by
  rw [← erase_detailedGameWithFixedChainKeygenView adversary chain]
  rw [evalDist_map,
    evalDist_detailedGameWithFixedChainKeygenView_eq_warmed,
    ← evalDist_map]

theorem chronologicallyWarmedDetailedGame_support_keyView
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (chronologicallyWarmedDetailedGame adversary chain)) :
    result.1.1 ∈ support
      (chronologicallyWarmedExtractedFixedChainKeygen chain) := by
  unfold chronologicallyWarmedDetailedGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨execution, _hexecution, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem chronologicallyWarmedKeygen_support_keygenTable
    (chain : ChainIndex) (result : ProgrammedFixedChainKeygenView)
    (hresult : result ∈ support
      (chronologicallyWarmedExtractedFixedChainKeygen chain)) :
    keygenChainValueTable result.cache result.secretKey chain = result.table := by
  apply actualFixedChainKeygen_support_table chain result
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed chain) result).mpr
      hresult

theorem chronologicallyWarmedDetailedGame_support_trajectoryTable
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (chronologicallyWarmedDetailedGame adversary chain)) :
    ∃ trajectories : List FullChainTrajectory,
      (actionTracedRevealProbeView chain
          (eraseFixedChainKeygenView result)).table =
        chainValueTableOfList trajectories ∧
      trajectories.length = lifetime := by
  have hkeyView := chronologicallyWarmedDetailedGame_support_keyView
    adversary chain result hresult
  obtain ⟨trajectories, htable, hlength⟩ :=
    chronologicallyWarmedExtractedFixedChainKeygen_support_table chain
      result.1.1 hkeyView
  refine ⟨trajectories, ?_, hlength⟩
  change keygenChainValueTable result.1.1.cache
      (Concrete.materializePrecomputation result.1.1.cache
        result.1.1.secretKey) chain = chainValueTableOfList trajectories
  change keygenChainValueTable result.1.1.cache result.1.1.secretKey chain =
      chainValueTableOfList trajectories
  rw [chronologicallyWarmedKeygen_support_keygenTable chain result.1.1
    hkeyView, htable]

noncomputable def chronologicallyWarmedRevealProbeViewExperiment
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp (IndexedHiddenValue.RevealProbeView ChainValueIndex) :=
  (fun result => actionTracedRevealProbeView chain
    (eraseFixedChainKeygenView result)) <$>
      chronologicallyWarmedDetailedGame adversary chain

theorem evalDist_actionTracedRevealProbeView_eq_warmed
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (actionTracedRevealProbeView chain <$>
      detailedGameWithKeygenCacheAndActionTrace adversary) =
      evalDist (chronologicallyWarmedRevealProbeViewExperiment adversary chain) := by
  unfold chronologicallyWarmedRevealProbeViewExperiment
  calc
    evalDist (actionTracedRevealProbeView chain <$>
        detailedGameWithKeygenCacheAndActionTrace adversary) =
        evalDist (actionTracedRevealProbeView chain <$>
          (eraseFixedChainKeygenView <$>
            chronologicallyWarmedDetailedGame adversary chain)) := by
      rw [evalDist_map,
        evalDist_originalActionTracedGame_eq_erase_warmed adversary chain,
        ← evalDist_map]
    _ = evalDist ((fun result => actionTracedRevealProbeView chain
          (eraseFixedChainKeygenView result)) <$>
        chronologicallyWarmedDetailedGame adversary chain) := by
      simp [Functor.map_map]

def replaceSignatureChainValue
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  { signature with
    chainValue := Function.update signature.chainValue chain value }

@[simp]
theorem replaceSignatureChainValue_same
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureChainValue signature chain value).chainValue chain = value := by
  simp [replaceSignatureChainValue]

theorem replaceSignatureChainValue_other
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureChainValue signature chain value).chainValue candidate =
      signature.chainValue candidate := by
  simp [replaceSignatureChainValue, Function.update_of_ne hne]

@[simp]
theorem replaceSignatureChainValue_self
    (signature : Signature) (chain : ChainIndex) :
    replaceSignatureChainValue signature chain (signature.chainValue chain) =
      signature := by
  unfold replaceSignatureChainValue
  congr 1
  funext candidate
  by_cases heq : candidate = chain
  · subst candidate
    simp
  · simp [Function.update_of_ne heq]

theorem Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding)
    (chain : ChainIndex) :
    (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
      epoch randomness encoding).chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (epoch, encoding chain) := by
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen
    largerCache hle epoch chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  simp only [Concrete.CacheReplay.signWithEncoding,
    Concrete.CacheReplay.signedChainValues, keygenChainValueTable]
  exact hwalk.symm

def revealSignatureChainValue
    (chain : ChainIndex) (epoch : Epoch) (encoding : Encoding)
    (signature : Signature) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex) Signature := do
  let value ← RevealProbeOracleSimulation.revealQuery (epoch, encoding chain)
  pure (replaceSignatureChainValue signature chain value)

theorem revealSignatureChainValue_isProbeQueryBoundP
    (chain : ChainIndex) (epoch : Epoch) (encoding : Encoding)
    (signature : Signature) :
    (revealSignatureChainValue chain epoch encoding signature).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold revealSignatureChainValue
  simpa using OracleComp.isQueryBoundP_bind (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
      (epoch, encoding chain) 0)
    (fun value _hvalue => OracleComp.isQueryBoundP_pure
      (p := RevealProbeOracleSimulation.IsProbeQuery)
      (replaceSignatureChainValue signature chain value) 0)

theorem simulate_eagerImpl_revealSignatureChainValue
    (table : ChainValueIndex → Digest) (chain : ChainIndex)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      (revealSignatureChainValue chain epoch encoding signature) =
      pure (replaceSignatureChainValue signature chain
        (table (epoch, encoding chain))) := by
  unfold revealSignatureChainValue RevealProbeOracleSimulation.revealQuery
    RevealProbeOracleSimulation.eagerImpl
  rw [simulateQ_bind, simulateQ_spec_query]
  simp

noncomputable def revealFixedChainAction
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : AttackerAction →
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex) AttackerAction
  | .hash input => pure (.hash input)
  | .sign request none => pure (.sign request none)
  | .sign request (some signature) =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
            (request.message, signature.randomness)) with
      | none => pure (.sign request (some signature))
      | some encoding => do
          let updated ← revealSignatureChainValue chain request.epoch encoding
            signature
          pure (.sign request (some updated))

noncomputable def revealFixedChainActionTrace
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : AttackerActionTrace →
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      AttackerActionTrace
  | [] => pure []
  | action :: actions => do
      let first ← revealFixedChainAction cache secretKey chain action
      let rest ← revealFixedChainActionTrace cache secretKey chain actions
      pure (first :: rest)

theorem revealFixedChainAction_isProbeQueryBoundP
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (action : AttackerAction) :
    (revealFixedChainAction cache secretKey chain action).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases action with
  | hash input => trivial
  | sign request signatureOption =>
      cases signatureOption with
      | none => trivial
      | some signature =>
          rw [revealFixedChainAction]
          split
          · trivial
          · rename_i encoding hdecode
            simpa using OracleComp.isQueryBoundP_bind (m := 0)
              (revealSignatureChainValue_isProbeQueryBoundP chain request.epoch
                encoding signature)
              (fun updated _hupdated => OracleComp.isQueryBoundP_pure
                (p := RevealProbeOracleSimulation.IsProbeQuery)
                (AttackerAction.sign request (some updated)) 0)

theorem revealFixedChainActionTrace_isProbeQueryBoundP
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (trace : AttackerActionTrace) :
    (revealFixedChainActionTrace cache secretKey chain trace).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction trace with
  | nil => trivial
  | cons action actions ih =>
      unfold revealFixedChainActionTrace
      apply OracleComp.isQueryBoundP_bind (m := 0)
        (revealFixedChainAction_isProbeQueryBoundP cache secretKey chain action)
      intro first _hfirst
      apply OracleComp.isQueryBoundP_bind (m := 0) ih
      intro rest _hrest
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (first :: rest) 0

def FixedChainRevealsAgree
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (trace : AttackerActionTrace) : Prop :=
  ∀ reveal ∈ trace.chainValueReveals cache secretKey chain,
    table reveal.1 = reveal.2

theorem detailedGame_fixedChainRevealsAgree
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support
      (detailedGameWithKeygenCacheAndActionTrace adversary)) :
    FixedChainRevealsAgree result.1.2.2 result.1.1.1.2 chain
      (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain)
      result.2 := by
  intro reveal hreveal
  exact detailedGameWithKeygenCacheAndActionTrace_chainValueReveals_eq_table
    adversary result hresult chain reveal hreveal

theorem simulate_eagerImpl_revealFixedChainAction_of_agrees
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (action : AttackerAction)
    (hagrees : FixedChainRevealsAgree cache secretKey chain table [action]) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      (revealFixedChainAction cache secretKey chain action) = pure action := by
  cases action with
  | hash input => rfl
  | sign request signatureOption =>
      cases signatureOption with
      | none => rfl
      | some signature =>
          rw [revealFixedChainAction]
          split
          · rfl
          · rename_i encoding hdecode
            rw [simulateQ_bind,
              simulate_eagerImpl_revealSignatureChainValue]
            simp only [pure_bind]
            have hvalue : table (request.epoch, encoding chain) =
                signature.chainValue chain := by
              apply hagrees ((request.epoch, encoding chain),
                signature.chainValue chain)
              apply (mem_chainValueReveals_iff cache secretKey chain [
                AttackerAction.sign request (some signature)] _).mpr
              exact ⟨request, signature, encoding, by simp, hdecode, rfl⟩
            rw [hvalue, replaceSignatureChainValue_self]
            simp

theorem simulate_eagerImpl_revealFixedChainActionTrace_of_agrees
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (trace : AttackerActionTrace)
    (hagrees : FixedChainRevealsAgree cache secretKey chain table trace) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      (revealFixedChainActionTrace cache secretKey chain trace) = pure trace := by
  induction trace with
  | nil => rfl
  | cons action actions ih =>
      have hfirst : FixedChainRevealsAgree cache secretKey chain table [action] := by
        intro reveal hreveal
        apply hagrees reveal
        unfold AttackerActionTrace.chainValueReveals at hreveal ⊢
        simpa using List.mem_append_left
          (List.filterMap (AttackerAction.chainValueReveal? cache secretKey chain)
            actions) hreveal
      have hrest : FixedChainRevealsAgree cache secretKey chain table actions := by
        intro reveal hreveal
        apply hagrees reveal
        unfold AttackerActionTrace.chainValueReveals at hreveal ⊢
        simpa using List.mem_append_right
          (List.filterMap (AttackerAction.chainValueReveal? cache secretKey chain)
            [action]) hreveal
      unfold revealFixedChainActionTrace
      rw [simulateQ_bind,
        simulate_eagerImpl_revealFixedChainAction_of_agrees cache secretKey
          chain table action hfirst, pure_bind, simulateQ_bind, ih hrest]
      simp

abbrev DetailedActionTracedResult :=
  ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
    (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)

def replaceDetailedActionTrace
    (result : DetailedActionTracedResult) (trace : AttackerActionTrace) :
    DetailedActionTracedResult :=
  ((result.1.1,
    ({ result.1.2.1 with signingLog := trace.toSigningLog }, result.1.2.2)),
    trace)

theorem replaceDetailedActionTrace_eq_self_of_log
    (result : DetailedActionTracedResult)
    (hlog : result.1.2.1.signingLog = result.2.toSigningLog) :
    replaceDetailedActionTrace result result.2 = result := by
  unfold replaceDetailedActionTrace
  cases result with
  | mk paired trace =>
      cases paired with
      | mk keyResult execution =>
          cases execution with
          | mk outcome cache =>
              cases outcome
              simp_all

noncomputable def transcriptProgramFromActionSkeleton
    (chain : ChainIndex) (result : DetailedActionTracedResult) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (List Bool → ChainValueIndex × Digest) := do
  let trace ← revealFixedChainActionTrace result.1.2.2 result.1.1.1.2
    chain result.2
  pure (actionTracedRevealProbeView chain
    (replaceDetailedActionTrace result trace)).strategy

theorem transcriptProgramFromActionSkeleton_isProbeQueryBoundP
    (chain : ChainIndex) (result : DetailedActionTracedResult) :
    (transcriptProgramFromActionSkeleton chain result).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold transcriptProgramFromActionSkeleton
  apply OracleComp.isQueryBoundP_bind (m := 0)
    (revealFixedChainActionTrace_isProbeQueryBoundP result.1.2.2
      result.1.1.1.2 chain result.2)
  intro trace _htrace
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery)
    (actionTracedRevealProbeView chain
      (replaceDetailedActionTrace result trace)).strategy 0

theorem simulate_eagerImpl_transcriptProgramFromActionSkeleton
    (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) (result : DetailedActionTracedResult)
    (hresult : result ∈ support
      (detailedGameWithKeygenCacheAndActionTrace adversary)) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl
      (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain))
      (transcriptProgramFromActionSkeleton chain result) =
      pure (actionTracedRevealProbeView chain result).strategy := by
  unfold transcriptProgramFromActionSkeleton
  rw [simulateQ_bind,
    simulate_eagerImpl_revealFixedChainActionTrace_of_agrees]
  · simp only [pure_bind, simulateQ_pure]
    rw [replaceDetailedActionTrace_eq_self_of_log]
    exact (detailedGameWithKeygenCacheAndActionTrace_support_info adversary
      result hresult).2.2.2.1
  · exact detailedGame_fixedChainRevealsAgree adversary chain result hresult

end XmssSecurity.CappedChain
