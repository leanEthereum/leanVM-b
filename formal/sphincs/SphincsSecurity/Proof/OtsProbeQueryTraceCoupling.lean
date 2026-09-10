import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrehitQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def CanonicalQueryTraceRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  (match left.1 with
    | none => True
    | some result => result.table = table ∧ result.value.1 = right.1.1 ∧
        ResolvedContextInvariant parameter table result.context (ordinaryQueryCache result.value.2) right.1.2.1.cache ∧
        VisibleResolvedComputationsCached parameter table result.context right.1.2.1.cache ∧
        PublishedValues result.context.state ∧ DeferredComputationsClosed result.context) ∧
    List.Forall₂ (fun a b => CanonicalQuerySelectionRel parameter table (some a) (some b.actual))
      left.2 (right.2.take left.2.length)

theorem CanonicalQueryTraceRel.prepend
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (a : CanonicalQuerySelection) (b : PrehitQuerySnapshot)
    (hhead : CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) :
    CanonicalQueryTraceRel parameter table (left.1, a :: left.2) (right.1, b :: right.2) := by
  refine ⟨hrelation.1, ?_⟩
  simpa only [List.length_cons, List.take_succ_cons] using List.Forall₂.cons
    (R := fun (a : CanonicalQuerySelection) (b : PrehitQuerySnapshot) =>
      CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) hhead hrelation.2

theorem relTriple_empty_canonicalTrace_any
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (right : ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)) :
    RelTriple (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
      right (CanonicalQueryTraceRel parameter table) := by
  have hbase := relTriple_true
    (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)) right
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result = (none, [])) (by intro result hresult; simpa using hresult)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  exact ⟨trivial, List.Forall₂.nil⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
