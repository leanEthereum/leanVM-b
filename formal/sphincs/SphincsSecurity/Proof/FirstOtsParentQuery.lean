import SphincsSecurity.Proof.FirstExceptionQueryTrace
import SphincsSecurity.Proof.FirstParentSettlementSigning
import SphincsSecurity.Proof.OtsProbeEarlyParentQuery

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem ExceptionRecordQuerySource.parent_input_initial
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop} {secretKey : SecretKey}
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    {record : ExceptionRecord} {snapshot : PrehitQuerySnapshot} {finalCache : QueryCache HashSpec}
    (hsource : ExceptionRecordQuerySource exception secretKey record snapshot finalCache) :
    ∃ child parent,
      AtPosition secretKey.parameter record.input child ∧ child.parentOf = some parent ∧
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret snapshot.state.1.cache child ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent ∧
      snapshot.state.1.cache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent) ≠ none := by
  rcases snapshot with ⟨input, state⟩
  obtain ⟨result, hresult, hle⟩ := hsource
  cases input with
  | inl query =>
      have hcache : record.cache = state.1.cache := firstExceptionRecord_query_cache exception query state.1.cache result record hresult
      have hvalid := runFirstException_none_valid exception (expandedAdversaryImpl secretKey (.inl query))
        state.1.cache hresult record (by simp)
      obtain ⟨child, parent, hat, hparentOf, hunsettled, _, _, hsettled, hcached, _⟩ :=
        (hparent _ _ _ hvalid.2.2.1).exists_full_parent_input secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (hvalid.2.2.2.trans hle)
      exact ⟨child, parent, hat, hparentOf, hcache ▸ hunsettled, hsettled, hcache ▸ hcached⟩
  | inr request =>
      exact firstExceptionRecord_sign_parent_input_initial secretKey exception hparent request state.1.cache result record hresult hle

def OtsExceptionRecord (parameter : PublicParameter) (record : ExceptionRecord) : Prop :=
  ∃ position, AtPosition parameter record.input position ∧ IsOtsPosition position

def FirstOtsParentRecord (parameter : PublicParameter)
    (result : (α × QueryCache HashSpec) × Option ExceptionRecord) : Prop :=
  ∃ record ∈ result.2, OtsExceptionRecord parameter record

theorem ExceptionRecordTraceRel.early_parent_of_ots_record
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop} {secretKey : SecretKey}
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    {initialCache : QueryCache HashSpec}
    {left : (α × QueryCache HashSpec) × Option ExceptionRecord}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrel : ExceptionRecordTraceRel exception secretKey initialCache none left right)
    (hrecord : FirstOtsParentRecord secretKey.parameter left) :
    EarlyOtsParentAtQuery secretKey.parameter secretKey.otsSecret secretKey.ftsSecret right := by
  obtain ⟨record, hrecord, position, hat, hots⟩ := hrecord
  rcases hrel.2.2.2 record hrecord with hnone | ⟨snapshot, hsnapshot, hsource⟩
  · simp at hnone
  · obtain ⟨child, parent, hchild, hparentOf, hunsettled, hsettled, hcached⟩ := hsource.parent_input_initial hparent
    have heq : position = child := atPosition_unique secretKey.parameter hat hchild
    refine ⟨snapshot, hsnapshot, child, parent, ?_, hparentOf, hunsettled, hsettled, hcached⟩
    exact (heq ▸ hots).parent hparentOf

theorem probEvent_firstOtsParentRecord_le_early_parent
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (accountingKey secretKey : SecretKey)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Pr[FirstOtsParentRecord secretKey.parameter |
      runFirstException exception (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache none] ≤
      Pr[EarlyOtsParentAtQuery secretKey.parameter secretKey.otsSecret secretKey.ftsSecret |
        runPrehitQueryTrace accountingKey secretKey computation state] := by
  exact probEvent_le_of_relTriple
    (relTriple_firstException_prehitQueryTrace exception accountingKey secretKey computation state none)
    (fun _ _ hrel hrecord => hrel.early_parent_of_ots_record hparent hrecord)

end SphincsSecurity.Concrete.OtsProbeSimulation
