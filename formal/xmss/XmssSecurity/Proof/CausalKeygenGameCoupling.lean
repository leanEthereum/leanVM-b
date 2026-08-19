import XmssSecurity.Proof.CausalKeygenCoupling
import XmssSecurity.Proof.CausalStrategyCoupling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def programmedWarmedDetailedGame
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    ProbComp FixedChainActionTracedResult := do
  let keyView ← programmedWarmedFixedChainKeygen chain
  let execution ← detailedGameAfterKeygenWithActionTrace adversary
    keyView.publicKey keyView.secretKey keyView.cache
  pure ((keyView, execution.1), execution.2)

theorem evalDist_chronologicallyWarmedDetailedGame_eq_programmed
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    evalDist (chronologicallyWarmedDetailedGame adversary chain) =
      evalDist (programmedWarmedDetailedGame adversary chain) := by
  unfold chronologicallyWarmedDetailedGame programmedWarmedDetailedGame
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_chronologicallyWarmedFixedChainKeygen_eq_programmed]

theorem programmedWarmedDetailedGame_support_keyView
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (programmedWarmedDetailedGame adversary chain)) :
    result.1.1 ∈ support (programmedWarmedFixedChainKeygen chain) := by
  unfold programmedWarmedDetailedGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨execution, _hexecution, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem programmedWarmedDetailedGame_support_keygenTable
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (programmedWarmedDetailedGame adversary chain)) :
    keygenChainValueTable result.1.1.cache result.1.1.secretKey chain =
      result.1.1.table := by
  apply programmedWarmedFixedChainKeygen_support_table chain result.1.1
  exact programmedWarmedDetailedGame_support_keyView
    adversary chain result hresult

theorem programmedWarmedRevealProbeView_table_eq_keyView
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (result : FixedChainActionTracedResult)
    (hresult : result ∈ support
      (programmedWarmedDetailedGame adversary chain)) :
    (actionTracedRevealProbeView chain
      (eraseFixedChainKeygenView result)).table = result.1.1.table := by
  change keygenChainValueTable result.1.1.cache result.1.1.secretKey chain =
    result.1.1.table
  exact programmedWarmedDetailedGame_support_keygenTable
    adversary chain result hresult

noncomputable def programmedWarmedRevealProbeViewExperiment
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    ProbComp (IndexedHiddenValue.RevealProbeView ChainValueIndex) :=
  (fun result => actionTracedRevealProbeView chain
    (eraseFixedChainKeygenView result)) <$>
      programmedWarmedDetailedGame adversary chain

theorem evalDist_chronologicallyWarmedRevealProbeView_eq_programmed
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    evalDist (chronologicallyWarmedRevealProbeViewExperiment adversary chain) =
      evalDist (programmedWarmedRevealProbeViewExperiment adversary chain) := by
  unfold chronologicallyWarmedRevealProbeViewExperiment
    programmedWarmedRevealProbeViewExperiment
  rw [evalDist_map,
    evalDist_chronologicallyWarmedDetailedGame_eq_programmed,
    ← evalDist_map]

theorem chronologicallyWarmedRevealProbeHit_probability_eq_programmed
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (chain : ChainIndex) :
    Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        chronologicallyWarmedRevealProbeViewExperiment adversary chain] =
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        programmedWarmedRevealProbeViewExperiment adversary chain] :=
  probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_chronologicallyWarmedRevealProbeView_eq_programmed
      adversary chain)

end XmssSecurity
