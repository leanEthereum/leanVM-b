import SphincsSecurity.Proof.FirstExceptionMonitor
import SphincsSecurity.Proof.OtsProbeRetainedPrehitTrace
import SphincsSecurity.Proof.OtsProbeStartErasureBound

namespace SphincsSecurity

open OracleComp OracleSpec

theorem runFirstException_support_cache_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord)
    {result : (α × QueryCache HashSpec) × Option ExceptionRecord}
    (hresult : result ∈ support (runFirstException exception computation cache saved)) : cache ≤ result.1.2 := by
  apply simulateQ_romImpl_cache_le computation cache result.1
  rw [← runFirstException_project exception computation cache saved, support_map]
  exact ⟨result, hresult, rfl⟩

namespace Concrete.OtsProbeSimulation

open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def ExceptionRecordQuerySource
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (secretKey : SecretKey)
    (record : ExceptionRecord) (snapshot : PrehitQuerySnapshot) (finalCache : QueryCache HashSpec) : Prop :=
  ∃ result : (OracleWorld + SigningSpec).Range snapshot.input × QueryCache HashSpec,
    (result, some record) ∈ support
      (runFirstException exception (expandedAdversaryImpl secretKey snapshot.input) snapshot.state.1.cache none) ∧
    result.2 ≤ finalCache

def ExceptionRecordTraceRel
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (saved : Option ExceptionRecord)
    (left : (α × QueryCache HashSpec) × Option ExceptionRecord)
    (right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  left.1.1 = right.1.1 ∧ left.1.2 = right.1.2.1.cache ∧ initialCache ≤ right.1.2.1.cache ∧
    ∀ record ∈ left.2, record ∈ saved ∨
      ∃ snapshot ∈ right.2, ExceptionRecordQuerySource exception secretKey record snapshot right.1.2.1.cache

theorem relTriple_firstException_outerQuery_prehit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (accountingKey secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState × Bool) (saved : Option ExceptionRecord) :
    RelTriple (runFirstException exception (expandedAdversaryImpl secretKey input) state.1.cache saved)
      ((encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state)
      (fun left right => left.1 = (right.1, right.2.1.cache) ∧
        left ∈ support (runFirstException exception (expandedAdversaryImpl secretKey input) state.1.cache saved)) := by
  classical
  have hright : (fun result => (result.1, result.2.1.cache)) <$>
      (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state =
      (simulateQ romImpl (expandedAdversaryImpl secretKey input)).run state.1.cache := by
    have h := encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey
      ((OracleWorld + SigningSpec).query input) state
    rw [simulateQ_unloggedMapped_eq_expanded] at h
    simpa only [simulateQ_spec_query] using h
  have hleft := runFirstException_project exception (expandedAdversaryImpl secretKey input) state.1.cache saved
  have h := relTriple_of_evalDist_map_eq_general
    (runFirstException exception (expandedAdversaryImpl secretKey input) state.1.cache saved)
    ((encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state)
    Prod.fst (fun result => (result.1, result.2.1.cache)) (congrArg evalDist (hleft.trans hright.symm))
  exact FtsProbeSimulation.relTriple_and_left_support h _ (fun _ hsupport => hsupport)

theorem relTriple_firstException_prehitQueryTrace
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) (saved : Option ExceptionRecord) :
    RelTriple (runFirstException exception (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache saved)
      (runPrehitQueryTrace accountingKey secretKey computation state)
      (ExceptionRecordTraceRel exception secretKey state.1.cache saved) := by
  induction computation using OracleComp.inductionOn generalizing state saved with
  | pure value =>
      simp only [simulateQ_pure, runFirstException, OracleComp.construct_pure, runPrehitQueryTrace]
      exact relTriple_pure_pure ⟨rfl, rfl, le_rfl, fun record hrecord => Or.inl hrecord⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, runFirstException_bind, runPrehitQueryTrace_query_bind]
      apply relTriple_bind (relTriple_firstException_outerQuery_prehit exception accountingKey secretKey input state saved)
      rintro ⟨⟨answer, cache⟩, currentSaved⟩ ⟨actualAnswer, actualState⟩ hquery
      have heq : answer = actualAnswer ∧ cache = actualState.1.cache := Prod.mk.inj hquery.1
      rcases heq with ⟨rfl, rfl⟩
      have htail := ih answer actualState currentSaved
      have hmap := relTriple_map (f := id)
        (g := fun tail : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
          (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2))
        (R := ExceptionRecordTraceRel exception secretKey state.1.cache saved)
        (relTriple_post_mono htail (by
          intro left right hrel
          refine ⟨hrel.1, hrel.2.1, ?_, ?_⟩
          · exact (runFirstException_support_cache_le exception _ _ saved hquery.2).trans hrel.2.2.1
          · intro record hrecord
            rcases hrel.2.2.2 record hrecord with hprior | ⟨snapshot, hsnapshot, hsource⟩
            · cases saved with
              | none =>
                  have heq : currentSaved = some record := Option.mem_def.mp hprior
                  refine Or.inr ⟨⟨input, state⟩, List.mem_cons_self, (answer, actualState.1.cache), ?_, hrel.2.2.1⟩
                  simpa only [heq] using hquery.2
              | some previous =>
                  have hsupport := hquery.2
                  rw [runFirstException_some, support_map] at hsupport
                  obtain ⟨result, _, heq⟩ := hsupport
                  have hsaved : currentSaved = some previous := (congrArg Prod.snd heq).symm
                  exact Or.inl (by simpa only [hsaved] using hprior)
            · exact Or.inr ⟨snapshot, List.mem_cons_of_mem _ hsnapshot, hsource⟩))
      simpa only [id_map, map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure] using hmap

end Concrete.OtsProbeSimulation

end SphincsSecurity
