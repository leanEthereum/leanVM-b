import SphincsSecurity.Proof.AdaptiveChainEndpoint
import SphincsSecurity.Proof.QueryCap

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State AuxIndex ExtraIndex : Type} {auxSpec : OracleSpec AuxIndex} {extraSpec : OracleSpec ExtraIndex} {n : Nat} {Result : Type}

noncomputable def extendAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id) : QueryImpl (auxSpec + extraSpec) PMF
  | .inl input => auxiliary input
  | .inr input => PMF.pure (extra input)

noncomputable def eraseAux (extra : QueryImpl extraSpec Id) :
    QueryImpl ((auxSpec + extraSpec) + PrefixSpec n State) (OracleComp (auxSpec + PrefixSpec n State))
  | .inl (.inl input) => liftM ((auxSpec + PrefixSpec n State).query (.inl input))
  | .inl (.inr input) => pure (extra input)
  | .inr query => liftM ((auxSpec + PrefixSpec n State).query (.inr query))

variable [Fintype State] [DecidableEq State] [Nonempty State]

theorem lazyRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    lazyRun auxiliary (simulateQ (eraseAux extra) computation) observed = lazyRun (extendAux auxiliary extra) computation observed := by
  have himpl : (lazyImpl auxiliary).compose (eraseAux extra) = lazyImpl (n := n) (State := State) (extendAux auxiliary extra) := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, lazyImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [lazyRun, ← QueryImpl.simulateQ_compose, himpl]

omit [Fintype State] [Nonempty State] in
theorem observedRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (tables : Fin n → State → State) (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (simulateQ (eraseAux extra) computation) observed = observedRun (extendAux auxiliary extra) tables computation observed := by
  have himpl : (observedImpl auxiliary tables).compose (eraseAux extra) = observedImpl (extendAux auxiliary extra) tables := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, observedImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [observedRun, ← QueryImpl.simulateQ_compose, himpl]

omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem counted_eraseAux (extra : QueryImpl extraSpec Id)
    (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result) :
    simulateQ (eraseAux extra) (QueryCap.counted IsPrefixQuery computation) =
      QueryCap.counted IsPrefixQuery (simulateQ (eraseAux extra) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [QueryCap.counted_pure, simulateQ_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          cases input <;> simp only [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query,
            eraseAux, pure_bind, QueryCap.counted_query_bind, ih, IsPrefixQuery, if_false, Nat.zero_add, Prod.mk.eta, bind_pure]
          rfl
      | inr query =>
          simp only [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
            eraseAux, QueryCap.counted_query_bind, ih, IsPrefixQuery, if_true]
          rfl

omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem cap_eraseAux (extra : QueryImpl extraSpec Id)
    (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result) (budget : Nat) :
    simulateQ (eraseAux extra) (QueryCap.run IsPrefixQuery computation budget) =
      QueryCap.run IsPrefixQuery (simulateQ (eraseAux extra) computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure result => simp only [QueryCap.run_pure, simulateQ_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          cases input <;> simp only [QueryCap.run_query_bind, simulateQ_bind, simulateQ_spec_query,
            eraseAux, pure_bind, QueryCap.run_query_bind, ih, IsPrefixQuery, if_false]
          rfl
      | inr query =>
          cases budget with
          | zero => simp only [QueryCap.run_query_bind, IsPrefixQuery, if_true, simulateQ_pure, simulateQ_bind,
              simulateQ_spec_query, eraseAux, QueryCap.run_query_bind]
          | succ budget =>
              simp only [QueryCap.run_query_bind, IsPrefixQuery, if_true, simulateQ_bind, simulateQ_spec_query, eraseAux, ih,
                QueryCap.run_query_bind]
              rfl
theorem realRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      realRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [realRun, observedRun_eraseAux]

theorem idealRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    idealRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      idealRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [idealRun, lazyRun_eraseAux]

end SphincsSecurity.Concrete.PartialChainEndpoint
