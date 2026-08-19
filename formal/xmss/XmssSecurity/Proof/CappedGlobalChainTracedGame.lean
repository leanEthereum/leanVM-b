import XmssSecurity.Proof.CappedGlobalChainOrigin
import XmssSecurity.Proof.CappedGlobalChainTable
import XmssSecurity.Proof.CappedChain.ChainTracedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def liftChainStrategy (chain : ChainIndex)
    (strategy : List Bool → ChainValueIndex × Digest) :
    List Bool → GlobalChainValueIndex × Digest := fun history =>
  let probe := strategy history
  ((chain, probe.1), probe.2)

theorem readMany_globalKeygenTable_liftChainStrategy
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (queries : Nat)
    (strategy : List Bool → ChainValueIndex × Digest) :
    IndexedHiddenValue.readMany
        (globalKeygenChainValueTable keygenCache secretKey) queries
        (liftChainStrategy chain strategy) =
      IndexedHiddenValue.readMany
        (keygenChainValueTable keygenCache secretKey chain) queries strategy := by
  induction queries generalizing strategy with
  | zero => rfl
  | succ queries ih =>
      rw [IndexedHiddenValue.readMany, IndexedHiddenValue.readMany]
      let hit := decide
        (keygenChainValueTable keygenCache secretKey chain (strategy []).1 =
          (strategy []).2)
      change (hit || IndexedHiddenValue.readMany
          (globalKeygenChainValueTable keygenCache secretKey) queries
          (liftChainStrategy chain (fun history => strategy (hit :: history)))) =
        (hit || IndexedHiddenValue.readMany
          (keygenChainValueTable keygenCache secretKey chain) queries
          (fun history => strategy (hit :: history)))
      rw [ih]

theorem liftChainStrategy_avoids_globalReveals
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (strategy : List Bool → ChainValueIndex × Digest)
    (havoid : IndexedHiddenValue.AvoidsReveals
      (returnedChainValueReveals keygenCache finalCache secretKey log chain)
      strategy) :
    IndexedHiddenValue.AvoidsReveals
      (globalReturnedChainValueReveals keygenCache finalCache secretKey log)
      (liftChainStrategy chain strategy) := by
  intro history
  rw [mem_globalReturnedChainValueReveals_fst_iff]
  exact havoid history

noncomputable def globalOriginChain
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) : ChainIndex :=
  by
    classical
    exact if h : GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
        result.1.2.2 result.1.1.1.2 result.1.2.1 then
      h.choose
    else
      ⟨0, by simp [numChains]⟩

theorem globalOriginChain_spec
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1) :
    WinningOutcomeChainValueHasKeygenOrigin result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1 (globalOriginChain result) := by
  simp only [globalOriginChain, dif_pos horigin]
  exact horigin.choose_spec

noncomputable def globalActionTracedRevealProbeView
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    IndexedHiddenValue.RevealProbeView GlobalChainValueIndex :=
  let chain := globalOriginChain result
  let localView := actionTracedRevealProbeView chain result
  ⟨globalReturnedChainValueReveals result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1.signingLog,
    globalKeygenChainValueTable result.1.1.2 result.1.1.1.2,
    liftChainStrategy chain localView.strategy⟩

theorem globalActionTracedRevealProbeView_table_installs_reveals
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    IndexedHiddenValue.installReveals
        (globalActionTracedRevealProbeView result).table
        (globalActionTracedRevealProbeView result).reveals =
      (globalActionTracedRevealProbeView result).table := by
  simp only [globalActionTracedRevealProbeView]
  exact install_globalReturnedChainValueReveals_eq_keygenTable result.1.1.2
    result.1.2.2 result.1.1.1.2 result.1.2.1.signingLog

theorem globalOrigin_implies_globalRevealProbeView_hit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support
      (detailedGameWithKeygenCacheAndActionTrace adversary))
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1) :
    IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q
      (globalActionTracedRevealProbeView result) := by
  let chain := globalOriginChain result
  have hlocalOrigin : WinningOutcomeChainValueHasKeygenOrigin result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1 chain :=
    globalOriginChain_spec result horigin
  have hlocalHit : ActionTracedChainProbeHit q chain result := by
    refine ⟨hlocalOrigin.1.2.1, ?_⟩
    exact hlocalOrigin.readMany_of_mem_actionTracedGame q adversary hbound
      result hresult chain
  have hviewHit := actionTracedChainProbeHit_implies_revealProbeView_hit
    q chain result hlocalHit
  constructor
  · have hlocalRead : IndexedHiddenValue.readMany
        (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain) q
        (actionTracedRevealProbeView chain result).strategy = true := by
      simpa only [actionTracedRevealProbeView] using hviewHit.1
    simpa only [globalActionTracedRevealProbeView, chain,
      readMany_globalKeygenTable_liftChainStrategy] using hlocalRead
  · apply liftChainStrategy_avoids_globalReveals
    exact hviewHit.2

theorem globalWinningChainOrigin_probability_le_revealProbeView
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
      globalActionTracedRevealProbeView <$>
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
  rw [← detailedGameWithKeygenCacheAndActionTrace_projection, probEvent_map,
    probEvent_map]
  apply probEvent_mono
  intro result hresult horigin
  exact globalOrigin_implies_globalRevealProbeView_hit q adversary hbound result
    hresult horigin

noncomputable def HasGlobalChainEagerReduction
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  ∃ (Result : Type)
      (computation : OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex) Result),
    computation.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery q ∧
      Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
        detailedGameWithKeygenCache adversary] ≤
      Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment computation]

theorem globalWinningChainOrigin_probability_le_of_eagerReduction
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hreduction : HasGlobalChainEagerReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨Result, computation, hbound, hprobability⟩ := hreduction
  exact hprobability.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
      q computation hbound)

/-- Exact reveal-view independence is stronger than the eager reduction and is useful when it happens to be available. -/
noncomputable def HasGlobalChainRevealViewCoupling
    (adversary : Adversary Concrete.scheme) : Prop :=
  ∃ transcriptGenerator : ProbComp
      (List (GlobalChainValueIndex × Digest) ×
        (List Bool → GlobalChainValueIndex × Digest)),
    𝒟[globalActionTracedRevealProbeView <$>
        detailedGameWithKeygenCacheAndActionTrace adversary] =
      𝒟[IndexedHiddenValue.adaptiveRevealViewExperiment transcriptGenerator]

theorem globalWinningChainOrigin_probability_le_of_revealViewCoupling
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hcoupling : HasGlobalChainRevealViewCoupling adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨transcriptGenerator, hdist⟩ := hcoupling
  exact (globalWinningChainOrigin_probability_le_revealProbeView
    q adversary hbound).trans
      (IndexedHiddenValue.reveal_view_coupling_hit_le
        (globalActionTracedRevealProbeView <$>
          detailedGameWithKeygenCacheAndActionTrace adversary)
        transcriptGenerator q hdist)

end XmssSecurity.CappedChain
