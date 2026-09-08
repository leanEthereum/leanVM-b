import SphincsSecurity.Proof.StoppedRemainingCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
set_option backward.isDefEq.respectTransparency false

theorem remainingCoveragePotential_nonmessage_step (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hmessage : ¬ MessageHashInput key.parameter input) (result : HashOutput × CoverLogState)
    (hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl (.inr input))).run state))
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    remainingCoveragePotential key cap budget result.2 groups remaining = remainingCoveragePotential key cap budget state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
  obtain ⟨base, hb, rfl⟩ := hr
  simp only [signingLogFragment, List.append_nil]
  change base ∈ support ((randomOracle input).run state.1) at hb
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hb
    obtain ⟨output, _, rfl⟩ := hb
    exact remainingCoveragePotential_cacheQuery_nonmessage key cap budget state input output hfresh hsigned hmessage groups remaining
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, mem_support_pure_iff] at hb
    subst base
    rfl

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem expectedStepLogDiscard_remainingCoverage_nonmessage_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input)
    (hactive : (hit || failed) = false) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    expectedStepLogDiscard exception parameter root otsTable ftsTable (.inl (.inr input)) frame state hit failed
      (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget current groups remaining) =
      Pr[fun result => (result.1.2.2 || result.2) = true |
        stepWithFailure exception parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 hit failed] *
          remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state groups remaining := by
  apply expectedStepLogDiscard_eq_prob_mul_of_constant exception parameter root otsTable ftsTable (.inl (.inr input)) frame state hit failed _ _ hactive
  intro result hr
  exact remainingCoveragePotential_nonmessage_step (secretKey parameter root otsTable ftsTable) cap budget state input hsigned hmessage _
    (stepWithFailure_logged_support exception parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 state.2 hit failed result hr) groups remaining

theorem stoppedRemainingCoverageStepCharge_nonmessage_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input)
    (hactive : (hit || failed) = false) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    stoppedRemainingCoverageStepCharge exception parameter root otsTable ftsTable cap budget (.inl (.inr input)) frame state hit failed groups remaining =
      remainingUnusedCoverageStepCharge (secretKey parameter root otsTable ftsTable) cap budget state (.inl (.inr input)) groups remaining +
        Pr[fun result => (result.1.2.2 || result.2) = true |
          stepWithFailure exception parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 hit failed] *
            remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state groups remaining := by
  rw [stoppedRemainingCoverageStepCharge, survivingLogPotential]
  simp only [hactive, Bool.false_eq_true, if_false]
  rw [expectedStepLogDiscard_remainingCoverage_nonmessage_eq exception parameter root otsTable ftsTable cap _ input frame state hit failed hsigned hmessage hactive]
  rfl

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
