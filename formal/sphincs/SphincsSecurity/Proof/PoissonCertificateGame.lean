import SphincsSecurity.Proof.CertificateTerminalGame
import Mathlib.Probability.Distributions.Poisson.Basic

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def randomTerminalGame (lengthLaw : PMF Nat) (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule) (stopped : Nat → Bool) :
    PMF (Nat × (CertificateGameResult × List Index)) :=
  lengthLaw.bind fun total =>
    (certificateTerminalGame adversary budget required (stopAfter total) (stopped total) total).map (fun result => (total, result))

theorem randomTerminalGame_original (lengthLaw : PMF Nat) (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule) (stopped : Nat → Bool) :
    (randomTerminalGame lengthLaw adversary budget required stopAfter stopped).map
        (fun result => (certificateGameVerdict result.2.1.1, result.2.1.2.2.1)) =
      (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) := by
  rw [randomTerminalGame, PMF.map_bind]
  have hbranch (total : Nat) :
      ((certificateTerminalGame adversary budget required (stopAfter total) (stopped total) total).map
          (fun result => (total, result))).map
            (fun result => (certificateGameVerdict result.2.1.1, result.2.1.2.2.1)) =
        (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) := by
    rw [PMF.map_comp]
    exact certificateTerminalGame_original adversary budget required (stopAfter total) (stopped total) total
  simp_rw [hbranch]
  exact PMF.bind_const _ _

theorem randomTerminalGame_word (lengthLaw : PMF Nat) (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule) (stopped : Nat → Bool) :
    (randomTerminalGame lengthLaw adversary budget required stopAfter stopped).map (fun result => (result.1, result.2.2)) =
      lengthLaw.bind (fun total => (independentProposalWord (PMF.uniformOfFintype Index) total).map (fun word => (total, word))) := by
  rw [randomTerminalGame, PMF.map_bind]
  apply congrArg (PMF.bind lengthLaw)
  funext total
  calc
    _ = ((certificateTerminalGame adversary budget required (stopAfter total) (stopped total) total).map Prod.snd).map
        (fun word => (total, word)) := by rw [PMF.map_comp, PMF.map_comp]; rfl
    _ = _ := by rw [certificateTerminalGame_word]

theorem randomTerminalGame_cost_le (lengthLaw : PMF Nat) (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule) (stopped : Nat → Bool)
    (hbound : HasHashQueryBound scheme adversary q) (result : Nat × (CertificateGameResult × List Index))
    (hr : result ∈ (randomTerminalGame lengthLaw adversary q required stopAfter stopped).support) :
    result.2.1.2.2.2.spent ≤ q ∧ result.2.1.2.2.2.creationMass ≤ q := by
  rw [randomTerminalGame, PMF.mem_support_bind_iff] at hr
  obtain ⟨total, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, rfl⟩ := hr
  exact certificateTerminalGame_cost_le adversary q required (stopAfter total) (stopped total) total hbound source hsource

theorem expected_randomTerminalGame_mass_payoff_le (lengthLaw : PMF Nat) (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule) (stopped : Nat → Bool)
    (hbound : HasHashQueryBound scheme adversary q) (payoff : Nat → List Index → ENNReal) :
    (∑' result, Pr[= result | randomTerminalGame lengthLaw adversary q required stopAfter stopped] *
        (result.2.1.2.2.2.creationMass * payoff result.1 result.2.2)) ≤
      (q : ENNReal) * ∑' total, Pr[= total | lengthLaw] *
        ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff total word := by
  rw [randomTerminalGame, ← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
  simp_rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  calc
    _ ≤ ∑' total, (q : ENNReal) * (Pr[= total | lengthLaw] *
        ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff total word) := by
      apply ENNReal.tsum_le_tsum
      intro total
      calc
        _ ≤ Pr[= total | lengthLaw] * ((q : ENNReal) *
            ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff total word) :=
          mul_le_mul' le_rfl (expected_certificateTerminalGame_mass_payoff_le adversary q required
            (stopAfter total) (stopped total) total hbound (payoff total))
        _ = _ := by ring
    _ = _ := ENNReal.tsum_mul_left

noncomputable def targetProposalPool : PMF Nat :=
  (ProbabilityTheory.poissonMeasure ((19 / 50 : NNReal) * ((2 ^ totalHeight : Nat) : NNReal))).toPMF

noncomputable def proposalPrefixStop : CertificateStopRule :=
  fun input state length record => decide (
    targetProposalOverhead * (state.2.log ++ signingLogFragment input record.output).length + 131072 <
      ((state.2.proposals + length : Nat) : ENNReal))

noncomputable def poissonCertificateGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : Nat → SecretKey → CertificateStopRule) : PMF (Nat × (CertificateGameResult × List Index)) :=
  randomTerminalGame targetProposalPool adversary budget required
    (fun total key input state length record =>
      proposalPrefixStop input state length record || stopAfter total key input state length record)
    (fun total => decide (total < 25313293))

theorem poissonCertificateGame_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : Nat → SecretKey → CertificateStopRule) :
    (poissonCertificateGame adversary budget required stopAfter).map
        (fun result => (certificateGameVerdict result.2.1.1, result.2.1.2.2.1)) =
      (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) :=
  randomTerminalGame_original _ _ _ _ _ _

theorem poissonCertificateGame_word (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : Nat → SecretKey → CertificateStopRule) :
    (poissonCertificateGame adversary budget required stopAfter).map (fun result => (result.1, result.2.2)) =
      targetProposalPool.bind (fun total =>
        (independentProposalWord (PMF.uniformOfFintype Index) total).map (fun word => (total, word))) :=
  randomTerminalGame_word _ _ _ _ _ _

theorem expected_poissonCertificateGame_mass_payoff_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule)
    (hbound : HasHashQueryBound scheme adversary q) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | poissonCertificateGame adversary q required stopAfter] *
        (result.2.1.2.2.2.creationMass * payoff result.2.2)) ≤
      (q : ENNReal) * ∑' total, Pr[= total | targetProposalPool] *
        ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff word :=
  expected_randomTerminalGame_mass_payoff_le _ _ _ _ _ _ hbound (fun _ => payoff)

end SphincsSecurity.Concrete
