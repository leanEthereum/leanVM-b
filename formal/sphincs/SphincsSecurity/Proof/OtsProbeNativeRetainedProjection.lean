import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalRetainedTrace
import SphincsSecurity.Proof.OtsProbeChronologicalProbability
import SphincsSecurity.Proof.OtsProbeEnsuredExecution
import SphincsSecurity.Proof.OtsProbeNativeTerminalExperiment

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_chronological_retainedGameRestComputation
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (retainedGameRestComputation adversary ⟨root, parameter⟩) = (do
      let (forgery, log) ← simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩))
      let verified ← simulateQ (probingRomImpl parameter)
        (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
      pure ((forgery, log), verified)) := by
  unfold retainedGameRestComputation
  rw [simulateQ_bind]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind]
  change (simulateQ (probingRomImpl parameter + maskedChronologicalSigningImpl parameter root ftsSecret)
      (liftOracleWorldLeft _) >>= _) = _
  rw [simulateQ_liftOracleWorldLeft]
  simp

theorem nativeChronologicalRetainedComputation_eq_chronological_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    nativeChronologicalRetainedComputation adversary parameter ftsSecret =
      (fun result => (result.1.2, result.2)) <$>
        (maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache := by
  simp only [nativeChronologicalRetainedComputation, simulateQ_chronological_retainedGameRestComputation,
    maskedChronologicalRetainedGameAfterFtsSecrets, maskedChronologicalRetainedPrefixAfterFtsSecrets,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]

theorem finishResolvedRunIsNone_retainCompletableResult
    (result : Option (ResolvedRunResult α)) :
    finishResolvedRunIsNone (retainCompletableResult result) = finishResolvedRunIsNone result := by
  cases result with
  | none => rfl
  | some result =>
      by_cases hcomplete : DeferredCompletable result.table result.context
      · simp [retainCompletableResult, hcomplete]
      · rw [show retainCompletableResult (some result) = none from if_neg hcomplete]
        simp [finishResolvedRunIsNone, finishResolvedRun, hcomplete]

theorem evalDist_nativeQueryTrace_finish_eq_raw
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache >>=
        fun trace => finishResolvedRunIsNone trace.1) =
      evalDist (runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) >>=
          finishResolvedRunIsNone) := by
  have hprojection := runNativeQueryTrace_result_projection parameter root ftsSecret computation
    context fuel table cache hconsistent hstarts
  calc
    _ = evalDist ((Prod.fst <$> runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) >>=
        finishResolvedRunIsNone) := by simp only [bind_map_left]
    _ = evalDist ((retainCompletableResult <$> runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)) >>=
          finishResolvedRunIsNone) := by rw [evalDist_bind, hprojection, ← evalDist_bind]
    _ = _ := by simp only [bind_map_left, finishResolvedRunIsNone_retainCompletableResult]

theorem evalDist_nativeTerminalFailureAfterRoot_eq_raw
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel) =
      evalDist (runResolvedFromTable (ensuredInitialContext targets) fuel table
        (nativeChronologicalRetainedComputation adversary parameter ftsSecret) >>= finishResolvedRunIsNone) := by
  simp only [nativeTerminalFailureAfterRoot, nativeChainTraceAfterRoot,
    nativeChronologicalRetainedComputation, runResolvedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => simp
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable _ _ fuel table result
        (ensuredInitialContext_valid targets).valuesConsistent
        (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hresult
      exact evalDist_nativeQueryTrace_finish_eq_raw parameter result.value.1 ftsSecret _
        result.context result.remaining result.table result.value.2 hcore.2.1 (by rw [hcore.1]; exact hcore.2.2)

theorem runResolved_finish_map_value
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (project : α → β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (runResolvedFromTable context fuel table (project <$> computation) >>= finishResolvedRunIsNone) =
      (runResolvedFromTable context fuel table computation >>= finishResolvedRunIsNone) := by
  rw [map_eq_bind_pure_comp, runResolvedFromTable_bind, bind_assoc]
  apply bind_congr
  intro result
  cases result with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      simpa only [Function.comp_def, runResolvedFromTable, OracleComp.construct_pure, pure_bind] using
        finishResolvedRunIsNone_value_eq result.context result.remaining result.table (project result.value) result.value

theorem evalDist_nativeTerminalFailureAfterRoot_eq_chronological
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel) =
      evalDist (runResolvedFromTable
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel table ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache) >>=
          finishResolvedRunIsNone) := by
  rw [evalDist_nativeTerminalFailureAfterRoot_eq_raw,
    nativeChronologicalRetainedComputation_eq_chronological_projection, runResolved_finish_map_value]
  have hinitial : ensuredInitialContext targets =
      ({ state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } : DeferredContext).enlargeEnsured
        (targets.image Coordinate.position) := by
    simp [ensuredInitialContext, DeferredContext.enlargeEnsured, LazyRevealProbe.State.empty]
  rw [hinitial]
  exact evalDist_runResolved_finish_enlargeEnsured _ _ fuel table _ DeferredContext.valid_empty.valuesConsistent
    (startTableAgrees_empty table)

theorem probEvent_winningRetainedVerifyProbe_le_nativeTerminalFailure
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel] := by
  have hfailure := probEvent_winningRetainedVerifyProbe_le_finishedResolvedRun_none adversary parameter table ftsSecret fuel
  have heq := evalDist_nativeTerminalFailureAfterRoot_eq_chronological targets adversary parameter table ftsSecret fuel
  rw [_root_.OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) heq]
  unfold finishResolvedRunIsNone
  rw [← map_bind, probEvent_map]
  simpa only [Function.comp_def, Option.isNone_iff_eq_none] using hfailure

end SphincsSecurity.Concrete.OtsProbeSimulation
