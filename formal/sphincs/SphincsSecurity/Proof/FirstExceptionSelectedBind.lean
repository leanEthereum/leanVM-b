import SphincsSecurity.Proof.FirstExceptionMonitor
import SphincsSecurity.Proof.InterleavedMass

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def firstExceptionSelectedProbability
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (selected : ExceptionRecord → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => ∃ record ∈ result.2, selected record | runFirstException exception computation cache none]

@[simp] theorem firstExceptionSelectedProbability_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (selected : ExceptionRecord → Prop)
    (value : α) (cache : QueryCache HashSpec) :
    firstExceptionSelectedProbability exception selected (pure value) cache = 0 := by
  simp [firstExceptionSelectedProbability, runFirstException]

theorem probEvent_firstException_selected_some
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (selected : ExceptionRecord → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (record : ExceptionRecord) :
    Pr[fun result => ∃ saved ∈ result.2, selected saved | runFirstException exception computation cache (some record)] =
      if selected record then 1 else 0 := by
  rw [runFirstException_some, probEvent_map, probEvent_eq_tsum_ite]
  simp only [Function.comp_def, Option.mem_some_iff, exists_eq_left']
  split_ifs
  · exact Concrete.simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass computation cache
  · exact tsum_zero

theorem firstExceptionSelectedProbability_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (selected : ExceptionRecord → Prop)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    firstExceptionSelectedProbability exception selected (computation >>= next) cache =
      firstExceptionSelectedProbability exception selected computation cache +
        ∑' result, Pr[= result | runExceptionMonitor exception computation cache false] *
          (if result.2 then 0 else firstExceptionSelectedProbability exception selected (next result.1.1) result.1.2) := by
  have hflag := runFirstException_flag_projection exception computation cache none
  simp only [Option.isSome_none] at hflag
  rw [← hflag, tsum_probOutput_map_mul]
  unfold firstExceptionSelectedProbability
  rw [runFirstException_bind, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  cases hs : result.2 with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, if_false, Option.not_mem_none, false_and,
      exists_false, zero_add]
  | some record =>
      rw [probEvent_firstException_selected_some]
      simp only [Option.isSome_some, if_true, mul_zero, add_zero, Option.mem_some_iff, exists_eq_left', mul_ite, mul_one, mul_zero]

end SphincsSecurity
