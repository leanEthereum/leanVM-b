import SphincsSecurity.Proof.OuterQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def outerHashQueryCutAt (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      if IsOuterHash input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output => recursivelyCut output ordinal
      else (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output => recursivelyCut output ordinal) computation

theorem outerHashQueryCutAt_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    outerHashQueryCutAt ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= next) ordinal =
      (if IsOuterHash input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output => outerHashQueryCutAt (next output) ordinal
      else (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output => outerHashQueryCutAt (next output) ordinal) := by
  rfl

theorem outerHashQueryCutAt_resume (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    outerHashQueryCutAt computation ordinal >>= OuterQueryCut.resume = computation := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      rw [outerHashQueryCutAt_query_bind]
      split_ifs
      · cases ordinal with
        | zero => rfl
        | succ ordinal =>
            rw [bind_assoc]
            exact bind_congr fun output => ih output ordinal
      · rw [bind_assoc]
        exact bind_congr fun output => ih output ordinal

theorem outerHashQueryCutAt_hashBound (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    (outerHashQueryCutAt computation ordinal).IsQueryBoundP IsOuterHash ordinal := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [outerHashQueryCutAt]
  | query_bind input next ih =>
      rw [outerHashQueryCutAt_query_bind]
      by_cases hhash : IsOuterHash input
      · rw [if_pos hhash]
        cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [OracleComp.isQueryBoundP_query_bind_iff]
            exact ⟨Or.inr (by omega), fun output => by simpa only [if_pos hhash, Nat.add_sub_cancel] using ih output ordinal⟩
      · rw [if_neg hhash, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hhash, fun output => by simpa only [if_neg hhash] using ih output ordinal⟩

noncomputable def hashCutCandidate (parameter : PublicParameter) (context : DeferredContext)
    (result : OuterQueryCut α × SplitHashCache) : Option Probe :=
  match result.1.input? with
  | some (.inl (.inr input)) => (purePlanProbingHashQuery parameter input context.state).candidate?
  | _ => none

end SphincsSecurity.Concrete.OtsProbeSimulation
