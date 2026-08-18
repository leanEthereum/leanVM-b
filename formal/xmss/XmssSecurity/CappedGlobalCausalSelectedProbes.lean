import XmssSecurity.CappedGlobalCausalRevealCoverageGame
import XmssSecurity.CappedGlobalChainHighProbeBounds

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 100000

noncomputable def globalSelectedUnrevealedProbes
    (result : DetailedActionTracedResult) :
    List (GlobalChainValueIndex × Digest) :=
  let chain := globalOriginChain result
  let encoding := actionTracedForgeryEncoding result
  (unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
    result.1.2.1.signingLog chain result.2 result.1.2.1.forgery
      encoding).map fun probe => ((chain, probe.1), probe.2)

theorem chainInputProbe?_ne_none_implies_global_relevant
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (hprobe : chainInputProbe? secretKey.parameter chain input ≠ none) :
    GlobalChainProbeRelevantInput secretKey input := by
  left
  intro hglobal
  unfold chainInputProbe? at hprobe
  split at hprobe
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hglobalSome : globalChainInputProbe? secretKey.parameter input =
        some ((chain, data.1, chainStepDigit data.2.1), data.2.2) := by
      rw [hdata]
      exact globalChainInputProbe?_chainInput secretKey.parameter data.1 chain
        data.2.1 data.2.2
    rw [hglobalSome] at hglobal
    simp at hglobal
  · exact (hprobe rfl).elim

theorem length_filterMap_le_filter_of_ne_none
    (values : List α) (project : α → Option β) (predicate : α → Prop)
    [DecidablePred predicate]
    (hproject : ∀ value, project value ≠ none → predicate value) :
    (values.filterMap project).length ≤ (values.filter predicate).length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      cases hoption : project value with
      | none =>
          by_cases hpredicate : predicate value
          · simpa [hoption, hpredicate] using Nat.le.step ih
          · simpa [hoption, hpredicate] using ih
      | some projected =>
          have hpredicate : predicate value :=
            hproject value (by simp [hoption])
          simpa [hoption, hpredicate] using Nat.succ_le_succ ih

noncomputable def AttackerActionTrace.selectedGlobalRelevantHashInputs
    (secretKey : SecretKey) (trace : AttackerActionTrace) : List HashInput :=
  trace.hashInputs.filter (GlobalChainProbeRelevantInput secretKey)

theorem AttackerActionTrace.chainInputProbes_length_le_globalRelevant
    (secretKey : SecretKey) (chain : ChainIndex)
    (trace : AttackerActionTrace) :
    (trace.chainInputProbes secretKey.parameter chain).length ≤
      (trace.selectedGlobalRelevantHashInputs secretKey).length := by
  unfold AttackerActionTrace.chainInputProbes
    AttackerActionTrace.selectedGlobalRelevantHashInputs
  exact length_filterMap_le_filter_of_ne_none trace.hashInputs
    (chainInputProbe? secretKey.parameter chain)
    (GlobalChainProbeRelevantInput secretKey)
    (chainInputProbe?_ne_none_implies_global_relevant secretKey chain)

theorem globalSelectedUnrevealedProbes_length_le
    (result : DetailedActionTracedResult) :
    (globalSelectedUnrevealedProbes result).length ≤
      (result.2.selectedGlobalRelevantHashInputs result.1.1.1.2).length + 1 := by
  let chain := globalOriginChain result
  let encoding := actionTracedForgeryEncoding result
  calc
    (globalSelectedUnrevealedProbes result).length =
        (unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
          result.1.2.1.signingLog chain result.2 result.1.2.1.forgery
            encoding).length := by
      simp [globalSelectedUnrevealedProbes, chain, encoding]
    _ ≤ (chainValueProbes result.1.1.1.2.parameter chain result.2
          result.1.2.1.forgery encoding).length :=
      unrevealedChainValueProbes_length_le result.1.2.2 result.1.1.1.2
        result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding
    _ = (result.2.chainInputProbes result.1.1.1.2.parameter chain).length +
          1 := by
      simp [chainValueProbes]
    _ ≤ (result.2.selectedGlobalRelevantHashInputs result.1.1.1.2).length +
          1 := by
      exact Nat.add_le_add_right
        (result.2.chainInputProbes_length_le_globalRelevant
          result.1.1.1.2 chain) 1

theorem globalSelectedUnrevealedProbes_avoids_returnedReveals
    (result : DetailedActionTracedResult)
    (probe : GlobalChainValueIndex × Digest)
    (hprobe : probe ∈ globalSelectedUnrevealedProbes result) :
    probe.1 ∉ (globalReturnedChainValueReveals result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1.signingLog).map Prod.fst := by
  let chain := globalOriginChain result
  let encoding := actionTracedForgeryEncoding result
  unfold globalSelectedUnrevealedProbes at hprobe
  rw [List.mem_map] at hprobe
  obtain ⟨localProbe, hlocalProbe, rfl⟩ := hprobe
  rw [mem_globalReturnedChainValueReveals_fst_iff]
  exact unrevealedChainValueProbes_avoid_reveals result.1.1.2 result.1.2.2
    result.1.1.1.2 result.1.2.1.signingLog chain result.2
      result.1.2.1.forgery encoding localProbe hlocalProbe

theorem globalSelectedUnrevealedProbes_avoids_covered
    (result : DetailedActionTracedResult)
    (probe : GlobalChainValueIndex × Digest)
    (hprobe : probe ∈ globalSelectedUnrevealedProbes result) :
    probe.1 ∉ GlobalReturnedChainValueCovered result.1.2.2
      result.1.1.1.2 result.1.2.1.signingLog := by
  intro hcovered
  exact globalSelectedUnrevealedProbes_avoids_returnedReveals result probe
    hprobe (globalReturnedChainValueCovered_mem_reveals result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1.signingLog probe.1
        hcovered)

theorem globalOrigin_has_selectedUnrevealedProbe
    (result : DetailedActionTracedResult)
    (hsecret : result.1.2.1.secretKey = result.1.1.1.2)
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1) :
    ∃ probe ∈ globalSelectedUnrevealedProbes result,
      globalKeygenChainValueTable result.1.1.2 result.1.1.1.2 probe.1 =
        probe.2 := by
  let chain := globalOriginChain result
  have hlocalOrigin : WinningOutcomeChainValueHasKeygenOrigin result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1 chain :=
    globalOriginChain_spec result horigin
  obtain ⟨encoding, hdecode, hvalue⟩ :=
    winningOutcomeChainValueHasKeygenOrigin_eq_table result.1.1.2
      result.1.2.2 result.1.1.1.2 result.1.2.1 chain hlocalOrigin
  let probe : ChainValueIndex × Digest :=
    ((result.1.2.1.forgery.epoch, encoding chain),
      result.1.2.1.forgery.signature.chainValue chain)
  have hunrevealed : (result.1.2.1.forgery.epoch, encoding chain) ∉
      returnedChainValueIndices result.1.2.2 result.1.1.1.2
        result.1.2.1.signingLog chain := by
    rw [← hsecret]
    exact
      WinningOutcomeBadEventOccurs.forged_chain_coordinate_not_mem_returned
        hlocalOrigin.1 encoding (by simpa [hsecret] using hdecode)
  have hprobe : probe ∈ unrevealedChainValueProbes result.1.2.2
      result.1.1.1.2 result.1.2.1.signingLog chain result.2
        result.1.2.1.forgery encoding := by
    apply List.mem_filter.mpr
    exact ⟨by simp [chainValueProbes, probe], by simpa [probe] using hunrevealed⟩
  have hencoding : actionTracedForgeryEncoding result = encoding := by
    unfold actionTracedForgeryEncoding
    rw [hdecode]
    rfl
  refine ⟨((chain, probe.1), probe.2), ?_, ?_⟩
  · unfold globalSelectedUnrevealedProbes
    rw [hencoding]
    exact List.mem_map.mpr ⟨probe, hprobe, rfl⟩
  · exact hvalue.symm

end XmssSecurity.CappedChain
