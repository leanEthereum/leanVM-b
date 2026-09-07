import SphincsSecurity.Proof.QueryBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

noncomputable def beforeQueryOccurrence {ι : Type} {spec : OracleSpec ι}
    (select : spec.Domain → Prop) (computation : OracleComp spec α) : Nat → OracleComp spec Bool :=
  OracleComp.construct (C := fun _ => Nat → OracleComp spec Bool) (fun _ _ => pure false)
    (fun input _ next ordinal =>
      if select input then
        match ordinal with
        | 0 => pure true
        | ordinal + 1 => (OracleSpec.query input : OracleComp spec _) >>= fun reply => next reply ordinal
      else (OracleSpec.query input : OracleComp spec _) >>= fun reply => next reply ordinal) computation

@[simp] theorem beforeQueryOccurrence_pure {ι : Type} {spec : OracleSpec ι}
    (select : spec.Domain → Prop) (value : α) (ordinal : Nat) :
    beforeQueryOccurrence select (pure value : OracleComp spec α) ordinal = pure false := rfl

theorem beforeQueryOccurrence_query_bind {ι : Type} {spec : OracleSpec ι}
    (select : spec.Domain → Prop) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (ordinal : Nat) :
    beforeQueryOccurrence select (OracleSpec.query input >>= next) ordinal =
      if select input then
        match ordinal with
        | 0 => pure true
        | ordinal + 1 => (OracleSpec.query input : OracleComp spec _) >>= fun reply => beforeQueryOccurrence select (next reply) ordinal
      else (OracleSpec.query input : OracleComp spec _) >>= fun reply => beforeQueryOccurrence select (next reply) ordinal := rfl

theorem beforeQueryOccurrence_queryBound {ι : Type} {spec : OracleSpec ι}
    (select counted : spec.Domain → Prop) [DecidablePred counted] (computation : OracleComp spec α) (q ordinal : Nat)
    (hbound : computation.IsQueryBoundP counted q) :
    (beforeQueryOccurrence select computation ordinal).IsQueryBoundP counted q := by
  induction computation using OracleComp.inductionOn generalizing q ordinal with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [beforeQueryOccurrence_query_bind]
      by_cases hs : select input
      · rw [if_pos hs]
        cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [isQueryBoundP_query_bind_iff]
            exact ⟨hbound.1, fun reply => ih reply _ ordinal (hbound.2 reply)⟩
      · rw [if_neg hs, isQueryBoundP_query_bind_iff]
        exact ⟨hbound.1, fun reply => ih reply _ ordinal (hbound.2 reply)⟩

end SphincsSecurity.Concrete
