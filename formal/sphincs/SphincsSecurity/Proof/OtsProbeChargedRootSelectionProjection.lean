import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootCutRisk
import SphincsSecurity.Proof.OtsProbeChargedRootSelection
import SphincsSecurity.Proof.OtsProbeLiveHashCut
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem chargedNativeRootTraceCutCandidate_retain
    (parameter : PublicParameter) (target : Position)
    (result : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache))) :
    chargedNativeRootTraceCutCandidate parameter target (retainCompletableResult result) =
      chargedNativeRootSelectionCandidate parameter target (liveNativeHashCutSelection result) := by
  cases result with
  | none => rfl
  | some result =>
      simp only [retainCompletableResult, liveNativeHashCutSelection]
      by_cases hcomplete : DeferredCompletable result.table result.context
      · simp only [if_pos hcomplete, chargedNativeRootTraceCutCandidate, chargedNativeRootCutCandidate_eq_query]
        cases hinput : result.value.1.input? <;> simp [chargedNativeRootSelectionCandidate]
      · simp [hcomplete, chargedNativeRootTraceCutCandidate, chargedNativeRootSelectionCandidate]

theorem evalDist_chargedNativeRootTraceCutCandidate_eq_selection
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist ((fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1) <$>
      runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache) =
    evalDist (chargedNativeRootSelectionCandidate parameter target <$>
      liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        computation ordinal context fuel table cache) := by
  have hresult := evalDist_map_eq_of_evalDist_eq
    (runNativeQueryTrace_result_projection parameter root ftsSecret (outerHashQueryCutAt computation ordinal)
      context fuel table cache hconsistent hstarts) (chargedNativeRootTraceCutCandidate parameter target)
  have hselection := evalDist_map_eq_of_evalDist_eq
    (evalDist_liveNativeHashQuerySelection_eq_cut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      computation ordinal context fuel table cache hconsistent hstarts) (chargedNativeRootSelectionCandidate parameter target)
  simp only [Functor.map_map, chargedNativeRootTraceCutCandidate_retain] at hresult hselection
  exact hresult.trans hselection.symm

theorem probEvent_chargedNativeRootTraceCutCandidate_occurrence_eq_selection
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1 ≠ none |
      runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache] =
    Pr[fun selection => chargedNativeRootSelectionCandidate parameter target selection ≠ none |
      liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        computation ordinal context fuel table cache] := by
  have hdist := evalDist_chargedNativeRootTraceCutCandidate_eq_selection parameter root target ftsSecret computation ordinal
    context fuel table cache hconsistent hstarts
  have hprob := probEvent_congr' (fun _ _ => Iff.rfl) hdist (p := fun candidate => candidate ≠ none)
  simpa only [probEvent_map, Function.comp_def] using hprob

end SphincsSecurity.Concrete.OtsProbeSimulation
