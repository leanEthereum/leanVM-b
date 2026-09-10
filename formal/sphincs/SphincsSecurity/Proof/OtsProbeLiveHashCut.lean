import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveHashSelection
import SphincsSecurity.Proof.OuterHashQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveNativeHashCutSelection :
    Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) → Option CanonicalQuerySelection
  | none => none
  | some result =>
      if DeferredCompletable result.table result.context then
        match result.value.1.input? with
        | none => none
        | some input => some ⟨input, result.context, result.remaining, result.table, result.value.2⟩
      else none

theorem evalDist_liveNativeHashCutSelection_eq_none_of_not_completable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (OuterQueryCut α × SplitHashCache))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (liveNativeHashCutSelection <$> runResolvedFromTable context fuel table computation) =
      evalDist (pure none : ProbComp (Option CanonicalQuerySelection)) := by
  rw [map_eq_bind_pure_comp]
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
          have hstill := not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hresult hdoomed
          simp [liveNativeHashCutSelection, hcore.1, hstill]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp [runResolvedFromTable]) (pure none)

theorem evalDist_liveNativeHashQuerySelection_eq_cut
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (liveNativeHashQuerySelection impl computation ordinal context fuel table cache) =
      evalDist (liveNativeHashCutSelection <$> runResolvedFromTable context fuel table
        ((simulateQ impl (outerHashQueryCutAt computation ordinal)).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table cache with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [liveNativeHashQuerySelection_pure, outerHashQueryCutAt, runResolvedFromTable,
          liveNativeHashCutSelection, OuterQueryCut.input?, hcomplete]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [liveNativeHashQuerySelection_query_bind, if_pos hcomplete, outerHashQueryCutAt_query_bind]
        have hcontinue (remaining : Nat) :
            evalDist (do
              let result ← runResolvedFromTable context fuel table ((impl input).run cache)
              match result with
              | none => pure none
              | some result =>
                  liveNativeHashQuerySelection impl (next result.value.1) remaining
                    result.context result.remaining result.table result.value.2) =
            evalDist (liveNativeHashCutSelection <$> runResolvedFromTable context fuel table
              ((simulateQ impl ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>=
                fun output => outerHashQueryCutAt (next output) remaining)).run cache)) := by
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            runResolvedFromTable_bind, map_bind]
          apply evalDist_bind_congr
          intro result hresult
          cases result with
          | none => simp [liveNativeHashCutSelection]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable ((impl input).run cache) context fuel table result
                hconsistent hstarts hresult
              exact ih result.value.1 remaining result.context result.remaining result.table result.value.2 hcore.2.1
                (by rw [hcore.1]; exact hcore.2.2)
        by_cases hhash : IsOuterHash input
        · rw [if_pos hhash]
          cases ordinal with
          | zero =>
              simp [hhash, simulateQ_pure, StateT.run_pure, runResolvedFromTable,
                liveNativeHashCutSelection, OuterQueryCut.input?, hcomplete]
          | succ ordinal =>
              simp only [hhash, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
                Nat.add_sub_cancel]
              convert hcontinue ordinal using 1
              apply evalDist_bind_congr
              intro result _
              cases result <;> rfl
        · rw [if_neg hhash]
          simp only [hhash, false_and, ↓reduceIte]
          convert hcontinue ordinal using 1
          apply evalDist_bind_congr
          intro result _
          cases result <;> rfl
      · rw [liveNativeHashQuerySelection_query_bind, if_neg hcomplete]
        exact (evalDist_liveNativeHashCutSelection_eq_none_of_not_completable _ context fuel table hconsistent hstarts hcomplete).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
