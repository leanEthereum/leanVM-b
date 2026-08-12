import XmssSecurity.CausalStrategyReduction
import VCVio.ProgramLogic.Relational.Basic

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

noncomputable local instance causalViewCouplingSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

set_option maxRecDepth 1000000 in
theorem relTriple_programmedWarmedFixedChainKeygen_uniformTable
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      ($ᵗ (ChainValueIndex → Digest))
      (fun keyView table => keyView.table = table ∧
        keyView ∈ support (programmedWarmedFixedChainKeygen chain)) := by
  apply relTriple_of_evalDist_eq_right
    (evalDist_actualFixedChainKeygenTableOnly_eq_uniform chain)
  apply relTriple_of_evalDist_eq_right
    (evalDist_programmedWarmedFixedChainKeygenTableOnly_eq_actual chain)
  have hcoupling : RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (programmedWarmedFixedChainKeygen chain)
      (fun keyView other => keyView = other ∧
        keyView ∈ support (programmedWarmedFixedChainKeygen chain)) := by
    apply relTriple_iff_relWP.2
    refine ⟨SPMF.Coupling.refl
      (evalDist (programmedWarmedFixedChainKeygen chain)), ?_⟩
    intro pair hpair
    obtain ⟨keyView, hkeyView, rfl⟩ : ∃ keyView ∈
        support (evalDist (programmedWarmedFixedChainKeygen chain)),
        (keyView, keyView) = pair := by
      simpa [SPMF.Coupling.refl, support_pure] using hpair
    refine ⟨rfl, ?_⟩
    change keyView ∈ support (programmedWarmedFixedChainKeygen chain)
    rw [mem_support_iff_evalDist_apply_ne_zero] at hkeyView ⊢
    simpa using hkeyView
  have hbound : RelTriple
      (programmedWarmedFixedChainKeygen chain >>= fun keyView => pure keyView)
      (programmedWarmedFixedChainKeygen chain >>= fun keyView =>
        pure keyView.table)
      (fun keyView table => keyView.table = table ∧
        keyView ∈ support (programmedWarmedFixedChainKeygen chain)) :=
    relTriple_bind hcoupling fun keyView other hsame =>
      relTriple_pure_pure ⟨by rw [hsame.1], hsame.2⟩
  simpa [programmedWarmedFixedChainKeygenTableOnly,
    map_eq_bind_pure_comp] using hbound

theorem simulate_eagerTrace_revealSignatureChainValue
    (table : ChainValueIndex → Digest) (chain : ChainIndex)
    (epoch : Epoch) (encoding : Encoding) (signature : Signature) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (revealSignatureChainValue chain epoch encoding signature)).run =
      pure (replaceSignatureChainValue signature chain
        (table (epoch, encoding chain)),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          (epoch, encoding chain) (table (epoch, encoding chain))]) := by
  unfold revealSignatureChainValue
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem simulate_eagerTrace_revealFixedChainAction_of_agrees
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (action : AttackerAction)
    (hagrees : FixedChainRevealsAgree cache secretKey chain table [action]) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (revealFixedChainAction cache secretKey chain action)).run =
      pure (action, revealTrace
        (AttackerActionTrace.chainValueReveals
          cache secretKey chain [action])) := by
  cases action with
  | hash input =>
      simp [revealFixedChainAction, AttackerActionTrace.chainValueReveals,
        AttackerAction.chainValueReveal?, revealTrace]
  | sign request signatureOption =>
      cases signatureOption with
      | none =>
          simp [revealFixedChainAction, AttackerActionTrace.chainValueReveals,
            AttackerAction.chainValueReveal?, revealTrace]
      | some signature =>
          cases hdecode : TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none =>
              simp [revealFixedChainAction, hdecode,
                AttackerActionTrace.chainValueReveals,
                AttackerAction.chainValueReveal?, revealTrace]
          | some encoding =>
              have hvalue : table (request.epoch, encoding chain) =
                  signature.chainValue chain := by
                apply hagrees ((request.epoch, encoding chain),
                  signature.chainValue chain)
                apply (mem_chainValueReveals_iff cache secretKey chain [
                  AttackerAction.sign request (some signature)] _).mpr
                exact ⟨request, signature, encoding, by simp, hdecode, rfl⟩
              rw [revealFixedChainAction]
              simp only [hdecode]
              rw [simulateQ_bind, WriterT.run_bind',
                simulate_eagerTrace_revealSignatureChainValue]
              simp [hvalue, replaceSignatureChainValue_self,
                AttackerActionTrace.chainValueReveals,
                AttackerAction.chainValueReveal?, revealTrace, hdecode]

theorem simulate_eagerTrace_revealFixedChainActionTrace_of_agrees
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (trace : AttackerActionTrace)
    (hagrees : FixedChainRevealsAgree cache secretKey chain table trace) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (revealFixedChainActionTrace cache secretKey chain trace)).run =
      pure (trace, revealTrace
        (trace.chainValueReveals cache secretKey chain)) := by
  induction trace with
  | nil => simp [revealFixedChainActionTrace,
      AttackerActionTrace.chainValueReveals, revealTrace]
  | cons action actions ih =>
      have hfirst : FixedChainRevealsAgree
          cache secretKey chain table [action] := by
        intro reveal hreveal
        apply hagrees reveal
        unfold AttackerActionTrace.chainValueReveals at hreveal ⊢
        simpa using List.mem_append_left
          (List.filterMap
            (AttackerAction.chainValueReveal? cache secretKey chain) actions)
          hreveal
      have hrest : FixedChainRevealsAgree
          cache secretKey chain table actions := by
        intro reveal hreveal
        apply hagrees reveal
        unfold AttackerActionTrace.chainValueReveals at hreveal ⊢
        simpa using List.mem_append_right
          (List.filterMap
            (AttackerAction.chainValueReveal? cache secretKey chain) [action])
          hreveal
      rw [revealFixedChainActionTrace, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealFixedChainAction_of_agrees
          cache secretKey chain table action hfirst]
      simp only [pure_bind]
      rw [simulateQ_bind, WriterT.run_bind', ih hrest]
      simp only [pure_bind]
      unfold AttackerActionTrace.chainValueReveals revealTrace
      generalize haction :
        AttackerAction.chainValueReveal? cache secretKey chain action = reveal
      cases reveal <;> simp [haction]

theorem simulate_eagerTrace_transcriptProgramFromActionSkeleton_of_agrees
    (chain : ChainIndex) (result : DetailedActionTracedResult)
    (hagrees : FixedChainRevealsAgree result.1.2.2 result.1.1.1.2 chain
      (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain) result.2)
    (hlog : result.1.2.1.signingLog = result.2.toSigningLog) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
      (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain))
      (transcriptProgramFromActionSkeleton chain result)).run =
      pure ((actionTracedRevealProbeView chain result).strategy,
        revealTrace (result.2.chainValueReveals
          result.1.2.2 result.1.1.1.2 chain)) := by
  unfold transcriptProgramFromActionSkeleton
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_revealFixedChainActionTrace_of_agrees
      result.1.2.2 result.1.1.1.2 chain
        (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain)
          result.2 hagrees]
  simp only [pure_bind, simulateQ_pure, WriterT.run_pure]
  rw [replaceDetailedActionTrace_eq_self_of_log result hlog]
  simp

set_option maxRecDepth 100000 in
theorem revealTrace_chainValueReveals_covered_by_actionTracedRevealProbeView
    (chain : ChainIndex) (result : DetailedActionTracedResult)
    (hlog : result.1.2.1.signingLog = result.2.toSigningLog) :
    CausalTraceRevealsCovered
      (fun index => index ∈
        (actionTracedRevealProbeView chain result).reveals.map Prod.fst)
      (revealTrace (result.2.chainValueReveals
        result.1.2.2 result.1.1.1.2 chain)) := by
  intro index value hrevealed
  unfold revealTrace at hrevealed
  rw [List.mem_map] at hrevealed
  obtain ⟨reveal, hreveal, haction⟩ := hrevealed
  obtain ⟨request, signature, encoding, hsign, hdecode, hrevealEq⟩ :=
    (mem_chainValueReveals_iff result.1.2.2 result.1.1.1.2 chain result.2
      reveal).mp hreveal
  have hcomponents : reveal.1 = index ∧ reveal.2 = value := by
    simpa using haction
  rw [hrevealEq] at hcomponents
  have hindex : index = (request.epoch, encoding chain) := hcomponents.1.symm
  subst index
  change (request.epoch, encoding chain) ∈
    (returnedChainValueReveals result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1.signingLog chain).map Prod.fst
  rw [mem_returnedChainValueReveals_fst_iff]
  rw [mem_returnedChainValueIndices_iff]
  refine ⟨request, signature, encoding, ?_, hdecode, rfl, le_rfl⟩
  rw [hlog]
  exact result.2.sign_mem_toSigningLog request signature hsign

theorem evalDist_originalActionTracedGame_eq_erase_programmed
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) =
      evalDist (eraseFixedChainKeygenView <$>
        programmedWarmedDetailedGame adversary chain) := by
  rw [evalDist_originalActionTracedGame_eq_erase_warmed adversary chain]
  simp only [evalDist_map]
  rw [evalDist_chronologicallyWarmedDetailedGame_eq_programmed,
    ← evalDist_map]

theorem programmedWarmedDetailedGame_support_erased
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (programmedWarmedDetailedGame adversary chain)) :
    eraseFixedChainKeygenView result ∈ support
      (detailedGameWithKeygenCacheAndActionTrace adversary) := by
  rw [mem_support_iff_evalDist_apply_ne_zero,
    evalDist_originalActionTracedGame_eq_erase_programmed adversary chain,
    ← mem_support_iff_evalDist_apply_ne_zero, support_map]
  exact ⟨result, hresult, rfl⟩

noncomputable def programmedWarmedSkeletonStrategyViewExperiment
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let result ← programmedWarmedDetailedGame adversary chain
  let detailed := eraseFixedChainKeygenView result
  let table := keygenChainValueTable detailed.1.1.2 detailed.1.1.1.2 chain
  let skeleton ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (transcriptProgramFromActionSkeleton chain detailed)).run
  pure (table, skeleton)

noncomputable def programmedWarmedSkeletonResult
    (chain : ChainIndex) (result : FixedChainActionTracedResult) :
    (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  let detailed := eraseFixedChainKeygenView result
  let view := actionTracedRevealProbeView chain detailed
  (view.table, (view.strategy, revealTrace
    (detailed.2.chainValueReveals
      detailed.1.2.2 detailed.1.1.1.2 chain)))

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedSkeletonStrategyViewExperiment_eq_map
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    evalDist (programmedWarmedSkeletonStrategyViewExperiment adversary chain) =
      evalDist (programmedWarmedSkeletonResult chain <$>
        programmedWarmedDetailedGame adversary chain) := by
  unfold programmedWarmedSkeletonStrategyViewExperiment
  rw [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro result hresult
  let detailed := eraseFixedChainKeygenView result
  have hdetailed : detailed ∈ support
      (detailedGameWithKeygenCacheAndActionTrace adversary) :=
    programmedWarmedDetailedGame_support_erased adversary chain result hresult
  have hagrees : FixedChainRevealsAgree detailed.1.2.2
      detailed.1.1.1.2 chain
      (keygenChainValueTable detailed.1.1.2 detailed.1.1.1.2 chain)
      detailed.2 :=
    detailedGame_fixedChainRevealsAgree adversary chain detailed hdetailed
  have hlog : detailed.1.2.1.signingLog = detailed.2.toSigningLog :=
    (detailedGameWithKeygenCacheAndActionTrace_support_info adversary
      detailed hdetailed).2.2.2.1
  dsimp only
  rw [simulate_eagerTrace_transcriptProgramFromActionSkeleton_of_agrees
    chain detailed hagrees hlog]
  simp [programmedWarmedSkeletonResult, actionTracedRevealProbeView, detailed]

def ProgrammedCausalViewRelation
    (programmed : IndexedHiddenValue.RevealProbeView ChainValueIndex)
    (causal : (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  programmed.table = causal.1 ∧
    programmed.strategy = causal.2.1 ∧
    CausalTraceRevealsCovered
      (fun index => index ∈ programmed.reveals.map Prod.fst) causal.2.2

set_option maxRecDepth 100000 in
theorem relTriple_programmedWarmedRevealProbeView_skeleton
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    RelTriple
      (programmedWarmedRevealProbeViewExperiment adversary chain)
      (programmedWarmedSkeletonStrategyViewExperiment adversary chain)
      ProgrammedCausalViewRelation := by
  have hbase : RelTriple
      (programmedWarmedDetailedGame adversary chain)
      (programmedWarmedDetailedGame adversary chain)
      (fun result other => result = other ∧ result ∈ support
        (programmedWarmedDetailedGame adversary chain)) := by
    apply relTriple_iff_relWP.2
    refine ⟨SPMF.Coupling.refl
      (evalDist (programmedWarmedDetailedGame adversary chain)), ?_⟩
    intro pair hpair
    obtain ⟨result, hresult, rfl⟩ : ∃ result ∈ support
        (evalDist (programmedWarmedDetailedGame adversary chain)),
        (result, result) = pair := by
      simpa [SPMF.Coupling.refl, support_pure] using hpair
    refine ⟨rfl, ?_⟩
    change result ∈ support (programmedWarmedDetailedGame adversary chain)
    rw [mem_support_iff_evalDist_apply_ne_zero] at hresult ⊢
    simpa using hresult
  have hbound : RelTriple
      (programmedWarmedDetailedGame adversary chain >>= fun result =>
        pure (actionTracedRevealProbeView chain
          (eraseFixedChainKeygenView result)))
      (programmedWarmedDetailedGame adversary chain >>= fun result =>
        let detailed := eraseFixedChainKeygenView result
        let table := keygenChainValueTable detailed.1.1.2
          detailed.1.1.1.2 chain
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (transcriptProgramFromActionSkeleton chain detailed)).run >>= fun skeleton =>
        pure (table, skeleton))
      ProgrammedCausalViewRelation := by
    apply relTriple_bind hbase
    intro result other hsame
    obtain ⟨rfl, hresult⟩ := hsame
    let detailed := eraseFixedChainKeygenView result
    have hdetailed : detailed ∈ support
        (detailedGameWithKeygenCacheAndActionTrace adversary) := by
      exact programmedWarmedDetailedGame_support_erased adversary chain
        result hresult
    have hagrees : FixedChainRevealsAgree detailed.1.2.2
        detailed.1.1.1.2 chain
        (keygenChainValueTable detailed.1.1.2 detailed.1.1.1.2 chain)
        detailed.2 :=
      detailedGame_fixedChainRevealsAgree adversary chain detailed hdetailed
    have hlog : detailed.1.2.1.signingLog = detailed.2.toSigningLog :=
      (detailedGameWithKeygenCacheAndActionTrace_support_info adversary
        detailed hdetailed).2.2.2.1
    dsimp only
    rw [simulate_eagerTrace_transcriptProgramFromActionSkeleton_of_agrees
      chain detailed hagrees hlog]
    simp only [pure_bind]
    apply relTriple_pure_pure
    exact ⟨rfl, rfl,
      revealTrace_chainValueReveals_covered_by_actionTracedRevealProbeView
        chain detailed hlog⟩
  simpa [programmedWarmedRevealProbeViewExperiment,
    programmedWarmedSkeletonStrategyViewExperiment,
    map_eq_bind_pure_comp, Function.comp_apply] using hbound

theorem programmedCausalViewRelation_of_causalExecution
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × CausalHashState)
    (chain : ChainIndex)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (table : ChainValueIndex → Digest)
    (hinitial : ∀ index,
      keyResult.2.finishKeygen.revealed index = none)
    (hexecution : execution ∈ support
      (causalLazyDetailedGameAfterKeygen adversary keyResult.1.1
        keyResult.1.2 chain keyResult.2.finishKeygen))
    (htable :
      (actionTracedRevealProbeView chain
        (causalDetailedResult keyResult execution.1)).table = table) :
    ProgrammedCausalViewRelation
      (actionTracedRevealProbeView chain
        (causalDetailedResult keyResult execution.1))
      (table, lazyCausalStrategyResult chain keyResult execution) := by
  refine ⟨htable, rfl, ?_⟩
  have hcovered :=
    causalLazyDetailedGameAfterKeygen_support_returnedCovered
      adversary keyResult.1.1 keyResult.1.2 chain
        keyResult.2.finishKeygen hinitial execution hexecution
  intro index value hrevealed
  have hindex := hcovered.2 index value hrevealed
  have hmem := returnedChainValueCovered_mem_reveals
    keyResult.2.cache execution.1.2.cache keyResult.1.2
      execution.1.1.2.toSigningLog chain index hindex
  change index ∈
    (returnedChainValueReveals keyResult.2.cache execution.1.2.cache
      keyResult.1.2 execution.1.1.2.toSigningLog chain).map Prod.fst
  exact hmem

theorem programmedCausalViewRelation_transfers_hit
    (q : Nat)
    (programmed : IndexedHiddenValue.RevealProbeView ChainValueIndex)
    (causal : (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hrel : ProgrammedCausalViewRelation programmed causal)
    (hhit : IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals
      q programmed) :
    CausalTraceHitsAvoidingReveals q causal := by
  rcases hrel with ⟨htable, hstrategy, htrace⟩
  constructor
  · simpa [← htable, ← hstrategy] using hhit.1
  · apply avoids_observedTraceReveals_of_covered
      (fun index => index ∈ programmed.reveals.map Prod.fst)
        causal.2.2 causal.2.1 htrace
    intro history hmem
    exact hhit.2 history (hstrategy ▸ hmem)

theorem programmed_causal_trace_probability_le_of_relTriple
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hcoupling : RelTriple
      (programmedWarmedRevealProbeViewExperiment adversary chain)
      (causalLazyStrategyViewExperiment adversary chain)
      ProgrammedCausalViewRelation) :
    Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        programmedWarmedRevealProbeViewExperiment adversary chain] ≤
      Pr[CausalTraceHitsAvoidingReveals q |
        causalLazyStrategyViewExperiment adversary chain] := by
  apply probEvent_le_of_relTriple hcoupling
  intro programmed causal hrel hhit
  exact programmedCausalViewRelation_transfers_hit
    q programmed causal hrel hhit

theorem programmed_causal_trace_probability_le_of_eager_relTriple
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex)
    (hcoupling : RelTriple
      (programmedWarmedRevealProbeViewExperiment adversary chain)
      (causalEagerStrategyViewExperiment adversary chain)
      ProgrammedCausalViewRelation) :
    Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        programmedWarmedRevealProbeViewExperiment adversary chain] ≤
      Pr[CausalTraceHitsAvoidingReveals q |
        causalLazyStrategyViewExperiment adversary chain] := by
  apply programmed_causal_trace_probability_le_of_relTriple
  exact relTriple_of_evalDist_eq_right
    (evalDist_causalEagerStrategyViewExperiment_eq_lazy adversary chain)
      hcoupling

end XmssSecurity
