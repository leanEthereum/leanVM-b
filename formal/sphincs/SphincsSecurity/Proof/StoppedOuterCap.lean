import SphincsSecurity.Proof.StoppedSigningLog
import SphincsSecurity.Proof.OuterHashQueryCapBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem runWithFailure_outerCap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (OtsProbeSimulation.capOuterHashQueries computation q) frame cache hit failed =
      (fun result => ((result.1.1, ((some result.1.2.1.1, result.1.2.1.2), result.1.2.2)), result.2)) <$>
        runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing q frame cache hit failed with
  | pure value => simp only [OtsProbeSimulation.capOuterHashQueries_pure, runWithFailure_pure, map_pure]
  | query_bind input next ih =>
      have hbudget := OtsProbeSimulation.expandedQuery_hashBudget key input next q hbound
      rw [OtsProbeSimulation.capOuterHashQueries_query_bind_of_budget input next q hbudget.1,
        runWithFailure_query_bind, runWithFailure_query_bind, map_bind]
      apply evalDist_bind_congr (m := SPMF)
      intro result hresult
      have hactual := runExceptionMonitor_support_project exception _ cache hit
        (stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hresult)
      rw [← unloggedMappedAdversaryImpl_eq_simulateQ_expanded] at hactual
      have hreply := unloggedMappedAdversaryImpl_output_mem_support_expanded key input cache result.1.2.1.2 result.1.2.1.1 hactual
      exact ih result.1.2.1.1 (q - OtsProbeSimulation.outerHashQueryCount input) (hbudget.2 _ hreply)
        result.1.1 result.1.2.1.2 result.1.2.2 result.2

theorem runWithFailure_retainedComputation_uncapped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed =
      (fun result => ((result.1.1, ((some (root, result.1.2.1.1), result.1.2.1.2), result.1.2.2)), result.2)) <$>
        runWithFailure exception parameter root otsTable ftsTable (retainedGameRestComputation adversary ⟨root, parameter⟩) frame cache hit failed := by
  rw [retainedComputation, runWithFailure_map, runWithFailure_outerCap exception parameter root otsTable ftsTable _ q hbound,
    Functor.map_map]
  rfl

theorem runWithFailure_retainedComputation_trace
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed =
      (fun result => ((result.1.1, ((some (root, arrangeRetainedTrace result.1.2.1.1), result.1.2.1.2), result.1.2.2)), result.2)) <$>
        runWithFailure exception parameter root otsTable ftsTable
          (withSigningLog (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) []) frame cache hit failed := by
  have hlog : withSigningLog (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) [] =
      signingTraceComputation (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) := by simp [withSigningLog]
  rw [hlog, runWithFailure_retainedComputation_uncapped exception adversary parameter root otsTable ftsTable q hbound,
    retainedGameRestComputation_eq_signingTrace, runWithFailure_map, Functor.map_map]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
