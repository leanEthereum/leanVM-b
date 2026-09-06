import SphincsSecurity.Proof.FirstExceptionMonitor
import VCVio.ProgramLogic.Relational.Quantitative

namespace SphincsSecurity

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

variable (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (selected : ExceptionRecord → Prop)
  (detected : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (hdetect : ∀ cache input answer, exception cache input answer →
    selected ⟨cache, input, answer⟩ → detected cache input answer)

include hdetect

theorem retainFirstException_selected_implies_hit
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) (hit : Bool)
    (hprior : (∃ record ∈ saved, selected record) → hit = true)
    (query : OracleWorld.Domain) (answer : OracleWorld.Range query) :
    (∃ record ∈ retainFirstException exception saved cache query answer, selected record) →
      (hit || queryException detected cache query answer) = true := by
  classical
  cases saved with
  | some previous =>
      intro h
      have hh : hit = true := hprior (by simpa only [retainFirstException] using h)
      simp [hh]
  | none =>
      cases query with
      | inl sample => simp [retainFirstException, recordQueryException]
      | inr input =>
          intro h
          by_cases hfire : queryException exception cache (.inr input) answer = true
          · have hs : selected ⟨cache, input, answer⟩ := by
              obtain ⟨record, hrecord, hs⟩ := h
              have heq : (⟨cache, input, answer⟩ : ExceptionRecord) = record := by
                simpa only [retainFirstException, recordQueryException, hfire, if_true, Option.mem_some_iff] using hrecord
              exact heq.symm ▸ hs
            have hex : cache input = none ∧ exception cache input answer := by
              simpa only [queryException, decide_eq_true_eq] using hfire
            have hd := hdetect cache input answer hex.2 hs
            simp [queryException, hex.1, hd]
          · simp [retainFirstException, recordQueryException, hfire] at h

theorem relTriple_firstException_selected_monitor (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) (hit : Bool)
    (hprior : (∃ record ∈ saved, selected record) → hit = true) :
    RelTriple (runFirstException exception computation cache saved)
      (runExceptionMonitor detected computation cache hit)
      (fun left right => left.1 = right.1 ∧ ((∃ record ∈ left.2, selected record) → right.2 = true)) := by
  induction computation using OracleComp.inductionOn generalizing cache saved hit with
  | pure value =>
      simp only [runFirstException, runExceptionMonitor, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, hprior⟩
  | query_bind query next ih =>
      rw [runFirstException, OracleComp.construct_query_bind, runExceptionMonitor, OracleComp.construct_query_bind]
      apply relTriple_bind (relTriple_refl ((romImpl query).run cache))
      intro left right heq
      subst right
      exact ih left.1 left.2 _ _
        (retainFirstException_selected_implies_hit exception selected detected hdetect cache saved hit hprior query left.1)

theorem probEvent_firstException_selected_le_monitor (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ record ∈ result.2, selected record | runFirstException exception computation cache none] ≤
      Pr[fun result => result.2 = true | runExceptionMonitor detected computation cache false] := by
  exact probEvent_le_of_relTriple
    (relTriple_firstException_selected_monitor exception selected detected hdetect computation cache none false (by simp))
    (fun _ _ hrel => hrel.2)

end SphincsSecurity
