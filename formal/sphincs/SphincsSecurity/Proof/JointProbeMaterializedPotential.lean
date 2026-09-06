import SphincsSecurity.Proof.JointProbeEncodingExhaustion
import SphincsSecurity.Proof.JointProbeMaterializedBlocks

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointPublicationInvariant (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) : Prop :=
  OtsProbeSimulation.MaterializedChainsPublished context ∨ AnyEncodingInputsExhausted (ordinaryQueryCache cache.2)

theorem expectedJointMaterializedCharge_outerQuery_le_encodingPotential
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hinvariant : JointPublicationInvariant context cache) :
    expectedJointMaterializedCharge table ((jointSourceOuterQuery parameter root input).run cache) state ftsFuel context fuel otsTable ≤
      (if OtsProbeSimulation.IsOuterHash input then 1 else 0) * encodingExhaustionTotalPotential (ordinaryQueryCache cache.2) := by
  rcases hinvariant with hpublic | hexhausted
  · rw [expectedJointMaterializedCharge_outerQuery_eq_zero_of_chainsPublished
      table parameter root input state ftsFuel context fuel otsTable cache hconsistent hstarts hpublic]
    exact bot_le
  · apply (expectedJointMaterializedCharge_outerQuery_le_hashIndicator
      table parameter root input state ftsFuel context fuel otsTable cache hconsistent hstarts).trans
    exact le_mul_of_one_le_right bot_le (one_le_encodingExhaustionTotalPotential_of_exhausted hexhausted)

theorem expectedJointMaterializedCharge_bind_le_potential
    (potential : QueryCache HashSpec → ENNReal) (left : JointSource α) (next : α → JointSource β)
    (leftBudget nextBudget : ENNReal) (hpotential : JointCachePotentialBound potential left)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hleft : expectedJointMaterializedCharge table (left.run cache) state ftsFuel context fuel otsTable ≤
      leftBudget * potential (ordinaryQueryCache cache.2))
    (hnext : ∀ finalState remaining entry,
      AdaptiveRevealProbe.RawResult.done finalState remaining (some entry) ∈ support
        (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)) →
      expectedJointMaterializedCharge table ((next entry.value.1).run entry.value.2) finalState remaining
        entry.context entry.remaining entry.table ≤ nextBudget * potential (ordinaryQueryCache entry.value.2.2)) :
    expectedJointMaterializedCharge table ((left >>= next).run cache) state ftsFuel context fuel otsTable ≤
      (leftBudget + nextBudget) * potential (ordinaryQueryCache cache.2) := by
  rw [StateT.run_bind, expectedJointMaterializedCharge_bind _ _ _ _ _ _ _ _ hconsistent hstarts, add_mul]
  apply add_le_add hleft
  calc
    _ ≤ ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
        (runJointResolved (left.run cache) context fuel otsTable)] * (nextBudget * jointRawCachePotential potential result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hsupport : result ∈ support
          (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable))
      · apply mul_le_mul' le_rfl
        cases result with
        | stopped hit => simp [jointRawCachePotential]
        | done finalState remaining entry =>
            cases entry with
            | none => simp [jointRawCachePotential]
            | some entry => exact hnext finalState remaining entry hsupport
      · simp [probOutput_eq_zero_of_not_mem_support hsupport]
    _ = nextBudget * ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
        (runJointResolved (left.run cache) context fuel otsTable)] * jointRawCachePotential potential result := by
      simp only [mul_left_comm, ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul' le_rfl (hpotential table state ftsFuel context fuel otsTable cache)

end SphincsSecurity.Concrete.FtsProbeSimulation
