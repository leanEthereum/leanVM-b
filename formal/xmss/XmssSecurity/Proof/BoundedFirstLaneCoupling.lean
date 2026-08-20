import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.MarginalCoupling
import XmssSecurity.Proof.CacheAgreement
import VCVio.ProgramLogic.Relational.FromUnary

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

set_option maxHeartbeats 2000000

theorem relTriple_simulateQ_bounded_firstLane
    {spec : OracleSpec ι}
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest)
    (leftImpl : QueryImpl spec (StateT σ₁ ProbComp))
    (rightImpl : QueryImpl spec
      (StateT σ₂ (OracleComp (FirstLaneOracleSimulation.World Index))))
    (cost : spec.Domain → Nat)
    (stateRel : σ₁ → σ₂ →
      FirstLaneOracleSimulation.ActionTrace Index → Prop)
    (accounted : σ₁ → Nat → Prop)
    (Budget : OracleComp spec α → Nat → Prop)
    (stepBudget : ∀ (input : spec.Domain)
      (next : spec.Range input → OracleComp spec α) (fuel : Nat)
      (leftState : σ₁) (result : spec.Range input × σ₁),
      Budget (liftM (spec.query input) >>= next) fuel →
      result ∈ support ((leftImpl input).run leftState) →
      cost input ≤ fuel ∧ Budget (next result.1) (fuel - cost input))
    (stepCoupling : ∀ (used : Nat) (input : spec.Domain)
      (leftState : σ₁) (rightState : σ₂)
      (trace : FirstLaneOracleSimulation.ActionTrace Index),
      stateRel leftState rightState trace →
      FirstLaneOracleSimulation.hazardCount trace ≤ used →
      accounted leftState used →
      RelTriple
        ((leftImpl input).run leftState)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((rightImpl input).run rightState)).run)
        (fun leftResult rightResult =>
          (leftResult.1 = rightResult.1.1 ∧
            stateRel leftResult.2 rightResult.1.2
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input ∧
            accounted leftResult.2 (used + cost input)) ∨
          (FirstLaneOracleSimulation.CombinedHit table
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input)))
    (countLimit hitLimit used fuel : Nat)
    (computation : OracleComp spec α)
    (hbudget : Budget computation fuel)
    (leftState : σ₁) (rightState : σ₂)
    (trace : FirstLaneOracleSimulation.ActionTrace Index)
    (hstate : stateRel leftState rightState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (haccounted : accounted leftState used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ leftImpl computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ rightImpl computation).run rightState)).run)
      (fun leftResult rightResult =>
        ((∃ spent, leftResult.1 = rightResult.1.1 ∧
          stateRel leftResult.2 rightResult.1.2
            (trace ++ rightResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ rightResult.2) ≤ spent ∧
          accounted leftResult.2 spent ∧ spent ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit table
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ rightResult.2)))) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState trace used fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      exact Or.inl ⟨used, rfl, by
        simpa [FirstLaneOracleSimulation.ActionTrace.chainActions] using hstate,
        by simpa [FirstLaneOracleSimulation.hazardCount] using hcount,
        haccounted, by omega⟩
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', simulateQ_spec_query]
      apply relTriple_bind (relTriple_with_support
        (stepCoupling used input leftState rightState trace hstate hcount
          haccounted))
      intro headLeft headRight hhead
      have hnextBudget := stepBudget input next fuel leftState headLeft hbudget
        hhead.2.1
      rcases hhead.1 with hgood | hhit
      · obtain ⟨hvalue, hnextState, hnextCount, hnextAccounted⟩ := hgood
        have hnextBudget' : Budget (next headRight.1.1)
            (fuel - cost input) := by
          rw [← hvalue]
          exact hnextBudget.2
        let appendTrace := fun result :
            ((α × σ₂) × FirstLaneOracleSimulation.ActionTrace Index) =>
          Prod.map id (fun tail => headRight.2 ++ tail) result
        have hrec := ih headRight.1.1 (used + cost input)
          (fuel - cost input) hnextBudget' headLeft.2 headRight.1.2
            (trace ++ headRight.2) hnextState hnextCount hnextAccounted
              (by omega)
        change RelTriple _ _ _ at hrec
        have hlifted : RelTriple
            (id <$> (simulateQ leftImpl (next headRight.1.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                ((simulateQ rightImpl (next headRight.1.1)).run
                  headRight.1.2)).run)
            (fun leftResult rightResult =>
              ((∃ spent, leftResult.1 = rightResult.1.1 ∧
                stateRel leftResult.2 rightResult.1.2
                  (trace ++ rightResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                    (trace ++ rightResult.2) ≤ spent ∧
                accounted leftResult.2 spent ∧ spent ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit table
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ rightResult.2)))) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro leftResult rightResult hresult
          simpa [appendTrace, Prod.map, List.append_assoc] using hresult
        rw [hvalue]
        change RelTriple _ (appendTrace <$> _) _
        simpa only [id_map] using hlifted
      · obtain ⟨hhit, hnextCount⟩ := hhit
        have hnextLimit : FirstLaneOracleSimulation.hazardCount
            (trace ++ headRight.2) ≤ hitLimit := hnextCount.trans (by omega)
        have henforced : FirstLaneOracleSimulation.CombinedHit table
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ headRight.2)) := by
          rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
            (trace ++ headRight.2) hitLimit hnextLimit]
          exact hhit
        let appendTrace := fun result :
            ((α × σ₂) × FirstLaneOracleSimulation.ActionTrace Index) =>
          Prod.map id (fun tail => headRight.2 ++ tail) result
        have hlifted : RelTriple
            (id <$> (simulateQ leftImpl (next headLeft.1)).run headLeft.2)
            (appendTrace <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                ((simulateQ rightImpl (next headRight.1.1)).run
                  headRight.1.2)).run)
            (fun _leftResult rightResult =>
              FirstLaneOracleSimulation.CombinedHit table
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ rightResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono
            (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro))
          intro _leftResult rightResult _hresults
          simpa [appendTrace, Prod.map, List.append_assoc] using
            FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
              table hitLimit (trace ++ headRight.2) rightResult.2 henforced
        change RelTriple _ (appendTrace <$> _) _
        apply relTriple_post_mono (by simpa only [id_map] using hlifted)
        intro _leftResult _rightResult hresult
        exact Or.inr hresult

end XmssSecurity
