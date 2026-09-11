import SphincsSecurity.Proof.AdaptiveChainCheckpointContact
import SphincsSecurity.Proof.AdaptiveChainCapObservation
import SphincsSecurity.Proof.AdaptiveChainActualBudget

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Memory Result : Type}

theorem lazyRun_pause_budget (auxiliary : QueryImpl auxSpec PMF)
    (stop : Memory → Prop) (step : (input : (auxSpec + PrefixSpec n State).Domain) →
      (auxSpec + PrefixSpec n State).Range input → Memory → Memory)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (memory : Memory)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget)
    (middle : ((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State))
    (hmiddle : middle ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery (QueryPause.run stop step computation memory)) (fun _ _ => none)).support)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery middle.1.1.2) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ budget ∧ queryCount result.2 ≤ budget := by
  have hsplit := QueryPause.counted_bound stop step IsPrefixQuery computation memory budget hbound middle.1
    (lazyRun_result_mem auxiliary (QueryCap.counted IsPrefixQuery (QueryPause.run stop step computation memory)) (fun _ _ => none) middle hmiddle)
  have hpast := lazyRun_counted_queryCount_le auxiliary (QueryPause.run stop step computation memory) (fun _ _ => none) middle hmiddle
  simp only [queryCount_empty, Nat.zero_add] at hpast
  have hfuture := lazyRun_counted_budget_le auxiliary middle.1.1.2 middle.2 (budget - middle.1.2) hsplit.2 result hresult
  have hrows := lazyRun_counted_queryCount_le auxiliary middle.1.1.2 middle.2 result hresult
  omega

variable (auxiliary : State → QueryImpl auxSpec PMF)
  (stop : State → Memory → Prop)
  (step : State → (input : (auxSpec + PrefixSpec n State).Domain) →
    (auxSpec + PrefixSpec n State).Range input → Memory → Memory)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (memory : State → Memory)

noncomputable def pausedRun :
    PMF (State × (((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State)) ×
      ((Result × Nat) × (Fin n → State → Option State))) :=
  realCheckpointRun auxiliary
    (fun endpoint => QueryCap.counted IsPrefixQuery (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint)))
    (fun _ middle => middle.1.1.2) (fun _ _ => none)

theorem pausedRun_resume :
    (pausedRun auxiliary stop step computation memory).map (fun result => (result.1, result.2.2.1.1, result.2.2.2)) =
      realRun auxiliary computation (fun _ _ => none) := by
  have hbind {First Last : Type} (aux : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
      (first : OracleComp (auxSpec + PrefixSpec n State) First)
      (next : First → OracleComp (auxSpec + PrefixSpec n State) Last) (observed : Fin n → State → Option State) :
      observedRun aux tables (first >>= next) observed =
        (observedRun aux tables first observed).bind (fun middle => observedRun aux tables (next middle.1) middle.2) := by
    simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
  have hforget {Value : Type} (aux : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
      (program : OracleComp (auxSpec + PrefixSpec n State) Value) (observed : Fin n → State → Option State) :
      (observedRun aux tables (QueryCap.counted IsPrefixQuery program) observed).map (fun result => (result.1.1, result.2)) =
        observedRun aux tables program observed := by
    rw [← observedRun_map, QueryCap.counted_forget]
  have hlocal (endpoint : State) (tables : Fin n → State → State) :
      (checkpointObservedRun (auxiliary endpoint) tables
        (QueryCap.counted IsPrefixQuery (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint)))
        (fun middle => middle.1.1.2) (fun _ _ => none)).map (fun result => (result.2.1.1, result.2.2)) =
        observedRun (auxiliary endpoint) tables (computation endpoint) (fun _ _ => none) := by
    simp only [checkpointObservedRun, PMF.map_bind, PMF.map_comp, Function.comp_def, hforget]
    rw [← hbind (auxiliary endpoint) tables
      (QueryCap.counted IsPrefixQuery (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint)))
      (fun paused => paused.1.2) (fun _ _ => none)]
    congr 1
    rw [← bind_map_left, QueryCap.counted_forget, QueryPause.resume]
  simp only [pausedRun, realCheckpointRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables (fun (_ : Fin n) (_ : State) => none)) evaluate).bind
  funext pair
  rw [← hlocal pair.2 pair.1, PMF.map_comp]
  rfl

theorem pausedRun_newContact_le
    (marked : State → (((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State)) → Prop)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => (marked result.1 result.2.1 ∧ ¬Contact result.2.1.2 result.1) ∧ Contact result.2.2.2 result.1 |
        pausedRun auxiliary stop step computation memory]) ≤
      (2 * budget : Nat) * Pr[fun result => marked result.1 result.2 |
        realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery
          (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint))) (fun _ _ => none)] := by
  let before := fun endpoint => QueryCap.counted IsPrefixQuery (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint))
  let after := fun (_ : State) (middle : ((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State)) => middle.1.1.2
  have h := realCheckpointRun_contact_le_mark auxiliary before after (fun _ _ => none)
    (fun endpoint middle => marked endpoint middle ∧ ¬Contact middle.2 endpoint) budget (fun _ _ h => h.2) ?_ ?_
  · apply h.trans
    apply mul_le_mul' le_rfl
    simp only [probEvent_eq_tsum_ite]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hm : marked result.1 result.2
    · simp only [hm, if_true, true_and]
      split
      · exact le_rfl
      · exact bot_le
    · simp only [hm, false_and, if_false, le_refl]
  · intro endpoint middle hmiddle _ result hresult
    exact (lazyRun_pause_budget (auxiliary endpoint) (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint)
      budget (hbound endpoint) middle hmiddle result hresult).2
  · intro result hresult _
    have hs := realCheckpointRun_support auxiliary before after (fun _ _ => none) result hresult
    exact (lazyRun_pause_budget (auxiliary result.1) (stop result.1) (step result.1) (computation result.1) (memory result.1)
      budget (hbound result.1) result.2.1 hs.1 result.2.2 hs.2).1


theorem pausedRun_newContact_charge_of_real
    (marked : State → (((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State)) → Prop)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => (marked result.1 result.2.1 ∧ ¬Contact result.2.1.2 result.1) ∧ Contact result.2.2.2 result.1 |
        pausedRun auxiliary stop step computation memory]) ≤
      ∑' result, pausedRun auxiliary stop step computation memory result *
        (((queryCount result.2.1.2 + 2 * result.2.2.1.2 : Nat) : ENNReal) *
          if marked result.1 result.2.1 ∧ ¬Contact result.2.1.2 result.1 then 1 else 0) := by
  have h := realCheckpointRun_contact_charge auxiliary
    (fun endpoint => QueryCap.counted IsPrefixQuery (QueryPause.run (stop endpoint) (step endpoint) (computation endpoint) (memory endpoint)))
    (fun _ middle => middle.1.1.2) (fun _ _ => none)
    (fun endpoint middle => marked endpoint middle ∧ ¬Contact middle.2 endpoint) budget (fun _ _ h => h.2)
    (fun endpoint middle hmiddle _ result hresult =>
      (lazyRun_pause_budget_of_real auxiliary computation cost budget hcharge hreal hsmall endpoint
        (stop endpoint) (step endpoint) (memory endpoint) middle hmiddle result hresult).2)
  apply h.trans_eq
  apply tsum_congr
  intro result
  by_cases hm : marked result.1 result.2.1 ∧ ¬Contact result.2.1.2 result.1
  · simp only [pausedRun, if_pos hm]
  · simp only [pausedRun, if_neg hm]

end SphincsSecurity.Concrete.PartialChainEndpoint
