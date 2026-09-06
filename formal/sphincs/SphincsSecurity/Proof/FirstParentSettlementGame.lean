import SphincsSecurity.Proof.AnswerChargeBound
import SphincsSecurity.Proof.ParentSettlementWitness
import SphincsSecurity.Proof.FirstExceptionMonitor

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def sampledFirstParentSettlementGame (adversary : Adversary) :
    ProbComp (SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)) := do
  let secrets ← sampleSecrets
  let result ← runFirstException (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ none
  pure (secrets, result)

theorem sampledFirstParentSettlementGame_flag_projection (adversary : Adversary) :
    (fun result => (result.1, result.2.1, result.2.2.isSome)) <$> sampledFirstParentSettlementGame adversary =
      sampledParentSettlementGame adversary := by
  rw [sampledFirstParentSettlementGame, sampledParentSettlementGame, map_bind]
  apply bind_congr
  intro secrets
  have hproject := runFirstException_flag_projection
    (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ none
  simp only [Option.isSome_none] at hproject
  rw [bind_pure_comp, bind_pure_comp, Functor.map_map, ← hproject, Functor.map_map]

def firstParentSettlementResidual
    (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  result.2.1.1 = true ∧ (result.2.2.isSome = true ∨
    ¬ Bad result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2)

theorem forgeAdvantage_le_answer_add_first_parent_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[firstParentSettlementResidual | sampledFirstParentSettlementGame adversary] := by
  have hbound := forgeAdvantage_le_answer_add_parent_residual adversary q hq
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbound
  exact hbound

theorem sampledFirstParentSettlementGame_support (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary)) :
    result.1 ∈ support sampleSecrets ∧
      result.2 ∈ support (runFirstException
        (CleanParentSettlement result.1.parameter result.1.otsSecret result.1.ftsSecret)
        (gameAfterSecrets adversary result.1.parameter result.1.otsSecret result.1.ftsSecret) ∅ none) := by
  rw [sampledFirstParentSettlementGame, mem_support_bind_iff] at hresult
  obtain ⟨secrets, hsecrets, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨output, houtput, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact ⟨hsecrets, houtput⟩

theorem sampledFirstParentSettlementGame_record_valid (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2) :
    record.Valid (CleanParentSettlement result.1.parameter result.1.otsSecret result.1.ftsSecret) ∅ result.2.1.2 := by
  have hsupport := (sampledFirstParentSettlementGame_support adversary hresult).2
  exact runFirstException_none_valid _ _ _ hsupport record hrecord

theorem sampledFirstParentSettlementGame_record_full_parent_input (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2) :
    ∃ child parent,
      AtPosition result.1.parameter record.input child ∧ child.parentOf = some parent ∧
      ¬ Settled result.1.parameter result.1.otsSecret result.1.ftsSecret record.cache child ∧
      OtherChildrenSettled result.1.parameter result.1.otsSecret result.1.ftsSecret record.cache child parent ∧
      Settled result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 child ∧
      Settled result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 parent ∧
      record.cache (cachedInput result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 parent) ≠ none ∧
      slotDigest (parent.children.idxOf child)
          (cachedInput result.1.parameter result.1.otsSecret result.1.ftsSecret result.2.1.2 parent) =
        honestValue (fromCache result.2.1.2) result.1.parameter result.1.otsSecret result.1.ftsSecret child ∧
      honestValue (fromCache result.2.1.2) result.1.parameter result.1.otsSecret result.1.ftsSecret child =
        truncateHash record.answer := by
  have hvalid := sampledFirstParentSettlementGame_record_valid adversary hresult hrecord
  exact hvalid.2.2.1.2.exists_full_parent_input result.1.parameter result.1.otsSecret result.1.ftsSecret hvalid.2.2.2

end SphincsSecurity.Concrete
