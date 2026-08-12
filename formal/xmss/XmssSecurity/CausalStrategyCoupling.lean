import XmssSecurity.ChainTablePresampling
import XmssSecurity.ChainTracedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev FixedChainActionTracedResult :=
  ((ProgrammedFixedChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseFixedChainKeygenView
    (result : FixedChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)

noncomputable def detailedGameWithFixedChainKeygenView
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← actualFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey keyView.secretKey keyView.cache
  pure ((keyView, execution.1), execution.2)

noncomputable def chronologicallyWarmedDetailedGame
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← chronologicallyWarmedExtractedFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey keyView.secretKey keyView.cache
  pure ((keyView, execution.1), execution.2)

theorem erase_detailedGameWithFixedChainKeygenView
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    eraseFixedChainKeygenView <$>
        detailedGameWithFixedChainKeygenView adversary chain =
      detailedGameWithKeygenCacheAndActionTrace adversary := by
  unfold detailedGameWithFixedChainKeygenView actualFixedChainKeygen
    detailedGameWithKeygenCacheAndActionTrace
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro keyResult
  rfl

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
  simp only [evalDist_map]
  rw [evalDist_detailedGameWithFixedChainKeygenView_eq_warmed]

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

end XmssSecurity
