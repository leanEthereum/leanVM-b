import SphincsSecurity.Proof.StoppedOuterCap
import SphincsSecurity.Proof.BeforeFailureSigningCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem expectedBeforeFailureSigningCharge_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (project : α → β)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (project <$> computation) frame cache hit failed =
      expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih => simp only [map_bind, expectedBeforeFailureSigningCharge_query_bind, ih]

theorem expectedBeforeFailureSigningCharge_signingTrace
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (signingTraceComputation computation) frame cache hit failed =
      expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed := by
  have h := expectedBeforeFailureSigningCharge_map exception charge parameter root otsTable ftsTable (signingTraceComputation computation)
    Prod.fst frame cache hit failed
  rw [signingTraceComputation_fst] at h
  exact h.symm

theorem expectedBeforeFailureSigningCharge_outerCap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (OtsProbeSimulation.capOuterHashQueries computation q) frame cache hit failed =
      expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing q frame cache hit failed with
  | pure value => simp only [OtsProbeSimulation.capOuterHashQueries_pure, expectedBeforeFailureSigningCharge_pure]
  | query_bind input next ih =>
      have hbudget := OtsProbeSimulation.expandedQuery_hashBudget key input next q hbound
      rw [OtsProbeSimulation.capOuterHashQueries_query_bind_of_budget input next q hbudget.1,
        expectedBeforeFailureSigningCharge_query_bind, expectedBeforeFailureSigningCharge_query_bind]
      congr 1
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
      · have hactual := runExceptionMonitor_support_project exception _ cache hit
          (stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr)
        rw [← unloggedMappedAdversaryImpl_eq_simulateQ_expanded] at hactual
        have hreply := unloggedMappedAdversaryImpl_output_mem_support_expanded key input cache result.1.2.1.2 result.1.2.1.1 hactual
        rw [ih result.1.2.1.1 (q - OtsProbeSimulation.outerHashQueryCount input) (hbudget.2 _ hreply)]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expectedBeforeFailureSigningCharge_retainedComputation
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed =
      expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable
        (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) frame cache hit failed := by
  rw [retainedComputation, expectedBeforeFailureSigningCharge_map, expectedBeforeFailureSigningCharge_outerCap exception charge parameter root otsTable ftsTable _ q hbound,
    retainedGameRestComputation_eq_signingTrace, expectedBeforeFailureSigningCharge_map, expectedBeforeFailureSigningCharge_signingTrace]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
