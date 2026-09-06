import SphincsSecurity.Proof.OuterHashQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def OuterQueryCut.value? : OuterQueryCut α → Option α
  | .done value => some value
  | .query _ _ => none

noncomputable def capOuterHashQueries (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat) :
    OracleComp (OracleWorld + SigningSpec) (Option α) :=
  OuterQueryCut.value? <$> outerHashQueryCutAt computation q

theorem capOuterHashQueries_hashBound (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat) :
    (capOuterHashQueries computation q).IsQueryBoundP IsOuterHash q := by
  rw [capOuterHashQueries, isQueryBoundP_map_iff]
  exact outerHashQueryCutAt_hashBound computation q

theorem capOuterHashQueries_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (q : Nat) :
    capOuterHashQueries ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= next) q =
      (if IsOuterHash input then
        match q with
        | 0 => pure none
        | q + 1 => (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun reply => capOuterHashQueries (next reply) q
      else (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun reply => capOuterHashQueries (next reply) q) := by
  unfold capOuterHashQueries
  rw [outerHashQueryCutAt_query_bind]
  split_ifs
  · cases q <;> simp [map_bind, OuterQueryCut.value?]
  · rw [map_bind]

end SphincsSecurity.Concrete.OtsProbeSimulation
