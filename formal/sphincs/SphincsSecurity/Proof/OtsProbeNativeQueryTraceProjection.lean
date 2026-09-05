import SphincsSecurity.Proof.OtsProbeNativeQueryTraceSelection
import SphincsSecurity.Proof.OtsProbeHistoryCandidateSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem evalDist_retainCompletableResult_eq_none_of_not_completable
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (retainCompletableResult <$> runResolvedFromTable context fuel table computation) =
      evalDist (pure none : ProbComp (Option (ResolvedRunResult α))) := by
  rw [map_eq_bind_pure_comp]
  exact evalDist_runResolved_observe_of_not_completable context fuel table computation (pure none)
    (fun result => pure (retainCompletableResult result)) rfl
    (fun result _ _ hnot => by simp [retainCompletableResult, hnot]) hconsistent hstarts hdoomed

theorem runNativeQueryTrace_result_projection
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (Prod.fst <$> runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) =
      evalDist (retainCompletableResult <$> runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure, simulateQ_pure, StateT.run_pure,
        runResolvedFromTable]
      split_ifs with hcomplete <;> simp [retainCompletableResult, hcomplete]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [runNativeQueryTrace_query_bind, if_pos hcomplete]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          runResolvedFromTable_bind, map_bind]
        apply evalDist_bind_congr
        intro result hresult
        cases result with
        | none => simp [retainCompletableResult]
        | some result =>
            simp only
            have hcore := resolvedCore_of_mem_runResolvedFromTable
              ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
              context fuel table result hconsistent hstarts hresult
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
              ih result.value.1 result.context result.remaining result.table result.value.2
                hcore.2.1 (by rw [hcore.1]; exact hcore.2.2)
      · rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret _ context fuel table cache hcomplete]
        simp only [map_pure]
        exact (evalDist_retainCompletableResult_eq_none_of_not_completable context fuel table _
          hconsistent hstarts hcomplete).symm

theorem expectedNativeTraceCharge_eq
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' result, Pr[= result | runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] *
      canonicalTraceCharge charge result.2) =
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        charge computation context fuel table cache := by
  simp_rw [canonicalTraceCharge_eq_tsum_selection, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ← tsum_liveNativeQuerySelection_charge]
  apply tsum_congr
  intro ordinal
  calc
    _ = ∑' selection, Pr[= selection | (fun result => result.2[ordinal]?) <$>
        runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] *
          CanonicalQuerySelection.charge charge selection := (tsum_probOutput_map_mul _ _ _).symm
    _ = _ := tsum_congr fun selection => congrArg (· * CanonicalQuerySelection.charge charge selection)
      (_root_.OracleComp.probOutput_congr rfl (runNativeQueryTrace_selection_projection
        parameter root ftsSecret computation context fuel table cache ordinal))

end SphincsSecurity.Concrete.OtsProbeSimulation
