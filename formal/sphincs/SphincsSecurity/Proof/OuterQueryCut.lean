import SphincsSecurity.Proof.OtsProbeCanonicalSelectionCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

inductive OuterQueryCut (α : Type) where
  | done (value : α)
  | query (input : (OracleWorld + SigningSpec).Domain)
      (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)

def OuterQueryCut.resume : OuterQueryCut α → OracleComp (OracleWorld + SigningSpec) α
  | .done value => pure value
  | .query input next => OracleSpec.query input >>= next

def OuterQueryCut.input? : OuterQueryCut α → Option (OracleWorld + SigningSpec).Domain
  | .done _ => none
  | .query input _ => some input

noncomputable def outerQueryCutAt (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      match ordinal with
      | 0 => pure (.query input next)
      | ordinal + 1 => OracleSpec.query input >>= fun output => recursivelyCut output ordinal) computation

theorem outerQueryCutAt_resume (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat) :
    outerQueryCutAt computation ordinal >>= OuterQueryCut.resume = computation := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      cases ordinal with
      | zero => rfl
      | succ ordinal =>
          change (((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>=
              fun output => outerQueryCutAt (next output) ordinal) >>=
            OuterQueryCut.resume) = _
          rw [bind_assoc]
          exact bind_congr fun output => ih output ordinal

theorem actualQuerySelection_eq_cut_projection
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (cache : QueryCache HashSpec) :
    actualQuerySelection secretKey computation ordinal cache =
      (fun result : OuterQueryCut α × QueryCache HashSpec =>
        result.1.input?.map (fun input => (⟨input, result.2⟩ : ActualQuerySelection))) <$>
        (simulateQ (unloggedMappedAdversaryImpl secretKey) (outerQueryCutAt computation ordinal)).run cache := by
  induction computation using OracleComp.inductionOn generalizing ordinal cache with
  | pure value => simp [actualQuerySelection, outerQueryCutAt, OuterQueryCut.input?]
  | query_bind input next ih =>
      cases ordinal with
      | zero => simp [actualQuerySelection, outerQueryCutAt, OuterQueryCut.input?]
      | succ ordinal =>
          change ((unloggedMappedAdversaryImpl secretKey input).run cache >>= fun result =>
            actualQuerySelection secretKey (next result.1) ordinal result.2) = _
          rw [outerQueryCutAt, OracleComp.construct_query_bind]
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
          exact bind_congr fun result => ih result.1 ordinal result.2

theorem mem_support_run_cut_resume_iff
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (initialState : σ) (result : α × σ) :
    result ∈ support ((simulateQ impl computation).run initialState) ↔
      ∃ cut : OuterQueryCut α, ∃ middleState : σ,
        (cut, middleState) ∈ support ((simulateQ impl (outerQueryCutAt computation ordinal)).run initialState) ∧
        result ∈ support ((simulateQ impl cut.resume).run middleState) := by
  conv_lhs => rw [← outerQueryCutAt_resume computation ordinal]
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  constructor
  · rintro ⟨⟨cut, state⟩, hprefix, hsuffix⟩
    exact ⟨cut, state, hprefix, hsuffix⟩
  · rintro ⟨cut, state, hprefix, hsuffix⟩
    exact ⟨(cut, state), hprefix, hsuffix⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
