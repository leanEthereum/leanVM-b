import SphincsSecurity.Proof.JointProbeRawResolvedCore
import SphincsSecurity.Proof.JointProbeRetainedPublicationInvariant

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] expectedJointMaterializedCharge jointSourceOuterQuery
set_option backward.isDefEq.respectTransparency false

theorem expectedJointMaterializedCharge_computation_le
    (parameter : PublicParameter) (root : Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hinvariant : JointPublicationInvariant context cache) :
    expectedJointMaterializedCharge table ((jointSourceComputation parameter root computation).run cache) state ftsFuel context fuel otsTable ≤
      (q : ENNReal) * encodingExhaustionTotalPotential (ordinaryQueryCache cache.2) := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel otsTable cache with
  | pure value =>
      change expectedJointMaterializedCharge table ((jointSourceNativeBlock (pure value)).run cache) state ftsFuel context fuel otsTable ≤ _
      rw [expectedJointMaterializedCharge_eq_zero_of_probeFree table _
        (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.ProbeFree.pure value) cache) state ftsFuel context fuel otsTable]
      exact bot_le
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      let cost : Nat := if OtsProbeSimulation.IsOuterHash input then 1 else 0
      let restBudget : Nat := if OtsProbeSimulation.IsOuterHash input then q - 1 else q
      have hcost : cost + restBudget ≤ q := by
        by_cases hhash : OtsProbeSimulation.IsOuterHash input
        · have hpositive := hbound.1.resolve_left (not_not.mpr hhash)
          simp only [cost, restBudget, if_pos hhash]
          omega
        · simp [cost, restBudget, hhash]
      change expectedJointMaterializedCharge table
        ((jointSourceOuterQuery parameter root input >>= fun value => jointSourceComputation parameter root (next value)).run cache)
        state ftsFuel context fuel otsTable ≤ _
      apply le_trans (expectedJointMaterializedCharge_bind_le_potential encodingExhaustionTotalPotential _ _
        (cost : ENNReal) (restBudget : ENNReal)
        (jointCachePotentialBound_totalEncoding _ (fun encodingParameter position message =>
          jointCachePotentialBound_outerQuery_encoding encodingParameter parameter position message root input))
        table state ftsFuel context fuel otsTable cache hconsistent hstarts _ _)
      · exact mul_le_mul' (by rw [← Nat.cast_add]; exact Nat.cast_le.mpr hcost) le_rfl
      · simpa only [cost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
          expectedJointMaterializedCharge_outerQuery_le_encodingPotential table parameter root input state ftsFuel
            context fuel otsTable cache hconsistent hstarts hinvariant
      · intro finalState remaining entry hresult
        have hcore := resolvedCore_of_mem_jointRaw table _ state finalState ftsFuel remaining context fuel otsTable entry
          hconsistent hstarts hresult
        exact ih entry.value.1 restBudget (hbound.2 entry.value.1) finalState remaining entry.context entry.remaining entry.table entry.value.2
          hcore.2.1 (hcore.1 ▸ hcore.2.2)
          (jointPublicationInvariant_of_mem_outerQuery parameter root input table state finalState ftsFuel remaining
            context fuel otsTable cache entry hinvariant hresult)

end SphincsSecurity.Concrete.FtsProbeSimulation
