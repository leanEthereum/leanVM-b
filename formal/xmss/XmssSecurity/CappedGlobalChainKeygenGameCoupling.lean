import XmssSecurity.CappedGlobalTreeCoupling
import XmssSecurity.CappedGlobalChainTracedGame
import XmssSecurity.PrecomputedKeygenCache

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

noncomputable def trajectoryProgrammedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView :=
  eraseAllChainTrajectories <$> programmedAllChainTrajectoryKeygen

theorem evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist coupledGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories

theorem evalDist_coupledGlobalChainKeygenWithBaseFull_eq_trajectoryProgrammed :
    evalDist coupledGlobalChainKeygenWithBaseFull =
    evalDist (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
      ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
      pure (keyView, base)) :=
  evalDist_coupledGlobalChainKeygenWithBaseFull_eq_programmed

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))
      ProgrammedGlobalChainKeygenRelation := by
  apply relTriple_of_evalDist_eq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
  exact relTriple_of_evalDist_eq_right
    evalDist_coupledGlobalChainKeygenWithBaseFull_eq_trajectoryProgrammed
    relTriple_coupledGlobalChainKeygenWithBaseFull

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_fullRelation :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))
      ProgrammedGlobalChainKeygenFullRelation := by
  apply relTriple_of_evalDist_eq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
  exact relTriple_of_evalDist_eq_right
    evalDist_coupledGlobalChainKeygenWithBaseFull_eq_trajectoryProgrammed
    relTriple_coupledGlobalChainKeygenWithBaseFull_fullRelation

theorem evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist actualGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories

theorem trajectoryProgrammedGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support trajectoryProgrammedGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  apply actualGlobalChainKeygen_support_table result
  exact (mem_support_iff_of_evalDist_eq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed result).mpr hresult

theorem evalDist_trajectoryProgrammedGlobalChainKeygen_table_eq_uniform :
    evalDist (ProgrammedGlobalChainKeygenView.table <$>
      trajectoryProgrammedGlobalChainKeygen) =
    evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold trajectoryProgrammedGlobalChainKeygen
  calc
    _ = evalDist programmedAllChainTrajectoryKeygenTableOnly := by
      simp [programmedAllChainTrajectoryKeygenTableOnly,
        Functor.map_map, eraseAllChainTrajectories]
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_programmedAllChainTrajectoryKeygenTableOnly_eq_uniform

abbrev GlobalChainActionTracedResult :=
  ((ProgrammedGlobalChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseGlobalChainKeygenView
    (result : GlobalChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, Concrete.materializePrecomputation
      result.1.1.cache result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)

noncomputable def detailedGameWithGlobalChainKeygenView
    (adversary : Adversary Concrete.cappedScheme) :
    ProbComp GlobalChainActionTracedResult := do
  let keyView ← actualGlobalChainKeygen
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey) keyView.cache
  pure ((keyView, execution.1), execution.2)

noncomputable def trajectoryProgrammedGlobalChainDetailedGame
    (adversary : Adversary Concrete.cappedScheme) :
    ProbComp GlobalChainActionTracedResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey) keyView.cache
  pure ((keyView, execution.1), execution.2)

theorem erase_detailedGameWithGlobalChainKeygenView
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (eraseGlobalChainKeygenView <$>
        detailedGameWithGlobalChainKeygenView adversary) =
      evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) := by
  unfold detailedGameWithGlobalChainKeygenView actualGlobalChainKeygen
    detailedGameWithKeygenCacheAndActionTrace
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [Concrete.cappedScheme]
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

theorem evalDist_detailedGameWithGlobalChainKeygenView_eq_programmed
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (detailedGameWithGlobalChainKeygenView adversary) =
      evalDist (trajectoryProgrammedGlobalChainDetailedGame adversary) := by
  unfold detailedGameWithGlobalChainKeygenView
    trajectoryProgrammedGlobalChainDetailedGame
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed]

theorem evalDist_originalActionTracedGame_eq_erase_globalProgrammed
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) =
      evalDist (eraseGlobalChainKeygenView <$>
        trajectoryProgrammedGlobalChainDetailedGame adversary) := by
  rw [← erase_detailedGameWithGlobalChainKeygenView adversary]
  rw [evalDist_map,
    evalDist_detailedGameWithGlobalChainKeygenView_eq_programmed,
    ← evalDist_map]

theorem trajectoryProgrammedGlobalChainDetailedGame_support_keyView
    (adversary : Adversary Concrete.cappedScheme)
    (result : GlobalChainActionTracedResult)
    (hresult : result ∈ support
      (trajectoryProgrammedGlobalChainDetailedGame adversary)) :
    result.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold trajectoryProgrammedGlobalChainDetailedGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨execution, _hexecution, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem trajectoryProgrammedGlobalChainDetailedGame_support_table
    (adversary : Adversary Concrete.cappedScheme)
    (result : GlobalChainActionTracedResult)
    (hresult : result ∈ support
      (trajectoryProgrammedGlobalChainDetailedGame adversary)) :
    globalKeygenChainValueTable result.1.1.cache result.1.1.secretKey =
      result.1.1.table := by
  apply trajectoryProgrammedGlobalChainKeygen_support_table result.1.1
  exact trajectoryProgrammedGlobalChainDetailedGame_support_keyView
    adversary result hresult

theorem trajectoryProgrammedGlobalRevealProbeView_table_eq_keyView
    (adversary : Adversary Concrete.cappedScheme)
    (result : GlobalChainActionTracedResult)
    (hresult : result ∈ support
      (trajectoryProgrammedGlobalChainDetailedGame adversary)) :
    (globalActionTracedRevealProbeView
      (eraseGlobalChainKeygenView result)).table = result.1.1.table := by
  change globalKeygenChainValueTable result.1.1.cache result.1.1.secretKey =
    result.1.1.table
  exact trajectoryProgrammedGlobalChainDetailedGame_support_table
    adversary result hresult

noncomputable def trajectoryProgrammedGlobalRevealProbeViewExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    ProbComp (IndexedHiddenValue.RevealProbeView GlobalChainValueIndex) :=
  (fun result => globalActionTracedRevealProbeView
    (eraseGlobalChainKeygenView result)) <$>
      trajectoryProgrammedGlobalChainDetailedGame adversary

theorem evalDist_globalActionTracedRevealProbeView_eq_programmed
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (globalActionTracedRevealProbeView <$>
      detailedGameWithKeygenCacheAndActionTrace adversary) =
    evalDist (trajectoryProgrammedGlobalRevealProbeViewExperiment adversary) := by
  unfold trajectoryProgrammedGlobalRevealProbeViewExperiment
  calc
    evalDist (globalActionTracedRevealProbeView <$>
        detailedGameWithKeygenCacheAndActionTrace adversary) =
      evalDist (globalActionTracedRevealProbeView <$>
        (eraseGlobalChainKeygenView <$>
          trajectoryProgrammedGlobalChainDetailedGame adversary)) := by
      rw [evalDist_map,
        evalDist_originalActionTracedGame_eq_erase_globalProgrammed adversary,
        ← evalDist_map]
    _ = evalDist ((fun result => globalActionTracedRevealProbeView
          (eraseGlobalChainKeygenView result)) <$>
        trajectoryProgrammedGlobalChainDetailedGame adversary) := by
      simp [Functor.map_map]

end XmssSecurity.CappedChain
