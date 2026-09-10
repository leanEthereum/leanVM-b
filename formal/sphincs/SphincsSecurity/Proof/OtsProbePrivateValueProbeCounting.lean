import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedResolvedQueryCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value result.context result.remaining result.table) computation

theorem expectedResolvedQueryCharge_query_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge charge ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context fuel table = charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table := rfl

noncomputable def privatePositionProbeQueryCharge (target : Position) (input : LazyRevealProbe.Query Coordinate) : ENNReal :=
  if IsPrivatePositionProbe target input then 1 else 0

noncomputable def structuralProbeQueryCharge : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe (.position _) _ => 1
  | _ => 0

theorem sum_privatePositionProbeQueryCharge_le_structural
    (targets : Finset Position) (input : LazyRevealProbe.Query Coordinate) :
    (∑ target ∈ targets, privatePositionProbeQueryCharge target input) ≤ structuralProbeQueryCharge input := by
  cases input with
  | uniform n => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | hashOutput => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | ensure coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | peek coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | publish coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | reveal coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | probe coordinate digest =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
      | position position =>
          simp only [privatePositionProbeQueryCharge, IsPrivatePositionProbe, Coordinate.position.injEq, structuralProbeQueryCharge]
          rw [Finset.sum_ite_eq]
          split_ifs <;> simp

theorem expectedResolvedQueryCharge_le_queryBound
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (predicate : LazyRevealProbe.Query Coordinate → Prop) [DecidablePred predicate]
    (hcharge : ∀ input, charge input ≤ if predicate input then 1 else 0)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP predicate bound) :
    expectedResolvedQueryCharge charge computation context fuel table ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing bound context fuel table with
  | pure value => simp [expectedResolvedQueryCharge]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [expectedResolvedQueryCharge_query_bind]
      let remaining := if predicate input then bound - 1 else bound
      have htail :
          (∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table) ≤ remaining := by
        calc
          _ ≤ ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] * (remaining : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            cases result with
            | none => exact bot_le
            | some result => exact ih result.value remaining result.context result.remaining result.table (hbound.2 result.value)
          _ = _ := by
            rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp [runResolvedFromTable]), one_mul]
      apply (add_le_add (hcharge input) htail).trans
      by_cases hquery : predicate input
      · have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hquery)
        cases bound with
        | zero => omega
        | succ bound => simp [remaining, hquery, Nat.cast_add, add_comm]
      · simp [remaining, hquery]

end SphincsSecurity.Concrete.OtsProbeSimulation
