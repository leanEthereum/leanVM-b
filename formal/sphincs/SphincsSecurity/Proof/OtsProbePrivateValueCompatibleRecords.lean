import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueRecordReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def PrivateRecordCompatible (target : Position) (before after : HashOutput) (record : ResolvedRunResult α) : Prop :=
  ¬record.context.state.hitAt (.position target) before ∧ ¬record.context.state.hitAt (.position target) after

noncomputable def privateCompatibleRecordedResult
    (target : Position) (before after : HashOutput) (result : Option (ResolvedRunResult α)) : Option (ResolvedRunResult α) :=
  (privateRecordedResult target result).filter (fun record => decide (PrivateRecordCompatible target before after record))

noncomputable def runPrivateCompatibleRecords
    (target : Position) (before after : HashOutput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (ResolvedRunResult α)) :=
  privateCompatibleRecordedResult target before after <$> runResolvedFromTable context fuel table computation

theorem privateCompatibleRecordedResult_eq_none_of_initial_hit
    (target : Position) (output before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (bound : Nat)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound)
    (hhit : truncateHash before ∈ pending ∨ truncateHash after ∈ pending)
    (result : Option (ResolvedRunResult α)) (hresult : result ∈ support (runResolvedFromTable context fuel table computation)) :
    privateCompatibleRecordedResult target before after result = none := by
  cases result with
  | none => rfl
  | some result =>
      have hhistory := h.history_of_mem_runResolved computation context fuel table pending bound result hsafe hcount hresult
      have hincompatible : ¬PrivateRecordCompatible target before after (replacePrivateRunResult target 0 result) := by
        intro hcompatible
        rcases hhit with hhit | hhit
        · apply hcompatible.1
          exact hhistory.2.1 hhit
        · apply hcompatible.2
          exact hhistory.2.1 hhit
      by_cases hcomplete : DeferredCompletable result.table result.context <;>
        simp [privateCompatibleRecordedResult, privateRecordedResult, retainCompletableResult, hcomplete]
      exact hincompatible

theorem evalDist_runPrivateCompatibleRecords_eq_none_of_initial_hit
    (target : Position) (output before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (bound : Nat)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound)
    (hhit : truncateHash before ∈ pending ∨ truncateHash after ∈ pending) :
    evalDist (runPrivateCompatibleRecords target before after context fuel table computation) =
      evalDist (pure none : ProbComp (Option (ResolvedRunResult α))) := by
  unfold runPrivateCompatibleRecords
  rw [map_eq_bind_pure_comp]
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro result hresult
      simp only [Function.comp_apply, privateCompatibleRecordedResult_eq_none_of_initial_hit target output before after
        computation context fuel table pending bound h hsafe hcount hhit result hresult]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runResolvedFromTable context fuel table computation) (by simp [runResolvedFromTable]) (pure none)

def privateExposureDoneResult : Option (ResolvedRunResult (PrivateValueCut α)) → Option (ResolvedRunResult α)
  | none => none
  | some result =>
      match result.value with
      | .done value => some ⟨result.context, result.remaining, value, result.table⟩
      | .query _ _ => none

theorem privateExposureDoneResult_recorded
    (target : Position) (result : Option (ResolvedRunResult (PrivateValueCut α))) :
    privateExposureDoneResult (privateRecordedResult target result) =
      privateRecordedResult target (privateExposureDoneResult result) := by
  cases result with
  | none => rfl
  | some result =>
      cases hvalue : result.value with
      | done value =>
          by_cases hcomplete : DeferredCompletable result.table result.context <;>
            simp [privateExposureDoneResult, privateRecordedResult, retainCompletableResult, hcomplete, replacePrivateRunResult, hvalue]
      | query input next =>
          by_cases hcomplete : DeferredCompletable result.table result.context <;>
            simp [privateExposureDoneResult, privateRecordedResult, retainCompletableResult, hcomplete, replacePrivateRunResult, hvalue]

theorem privateExposureDoneResult_compatible
    (target : Position) (before after : HashOutput) (result : Option (ResolvedRunResult (PrivateValueCut α))) :
    privateExposureDoneResult (privateCompatibleRecordedResult target before after result) =
      privateCompatibleRecordedResult target before after (privateExposureDoneResult result) := by
  unfold privateCompatibleRecordedResult
  rw [← privateExposureDoneResult_recorded target result]
  cases privateRecordedResult target result with
  | none => rfl
  | some record =>
      cases hvalue : record.value with
      | done value =>
          conv_rhs => rw [privateExposureDoneResult, hvalue]
          dsimp only
          simp only [Option.filter]
          have heq : PrivateRecordCompatible target before after
              (⟨record.context, record.remaining, value, record.table⟩ : ResolvedRunResult α) =
              PrivateRecordCompatible target before after record := rfl
          simp only [heq]
          by_cases hcompatible : PrivateRecordCompatible target before after record <;>
            simp [hcompatible, privateExposureDoneResult, hvalue]
      | query input next =>
          simp only [Option.filter]
          by_cases hcompatible : PrivateRecordCompatible target before after record <;>
            simp [hcompatible, privateExposureDoneResult, hvalue]

theorem runPrivateCompatibleRecords_eq_filter
    (target : Position) (before after : HashOutput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivateCompatibleRecords target before after context fuel table computation =
      (fun result => result.filter (fun record => decide (PrivateRecordCompatible target before after record))) <$>
        runPrivateRecords target context fuel table computation := by
  unfold runPrivateCompatibleRecords runPrivateRecords privateCompatibleRecordedResult
  rw [Functor.map_map]

theorem evalDist_runPrivateCompatibleRecords_eq_exposure_cut
    (target : Position) (output before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (bound : Nat)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    evalDist (runPrivateCompatibleRecords target before after context fuel table computation) =
      evalDist (privateExposureDoneResult <$>
        runPrivateCompatibleRecords target before after context fuel table (privateValueExposureCut target before after computation)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel pending bound with
  | pure value =>
      change evalDist (pure (privateCompatibleRecordedResult target before after
          (some ⟨context, fuel, value, table⟩))) = evalDist (pure (privateExposureDoneResult
          (privateCompatibleRecordedResult target before after (some ⟨context, fuel, .done value, table⟩))))
      rw [privateExposureDoneResult_compatible]
      rfl
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe hcount
      have hquery : ¬IsPrivatePositionDisclosure target query := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        intro reply
        simpa using hsafe.2 reply
      rw [privateValueExposureCut_query_bind]
      by_cases hexposure : IsPrivateValueExposure target before after query
      · rw [if_pos hexposure]
        have hright : evalDist (privateExposureDoneResult <$>
            runPrivateCompatibleRecords target before after context fuel table (pure (.query query next))) =
            evalDist (pure none : ProbComp (Option (ResolvedRunResult α))) := by
          change evalDist (pure (privateExposureDoneResult (privateCompatibleRecordedResult target before after
            (some ⟨context, fuel, .query query next, table⟩)))) = _
          rw [privateExposureDoneResult_compatible]
          rfl
        rw [hright]
        cases query with
        | uniform n => simp [IsPrivateValueExposure] at hexposure
        | hashOutput => simp [IsPrivateValueExposure] at hexposure
        | ensure coordinate => simp [IsPrivateValueExposure] at hexposure
        | peek coordinate => simp [IsPrivateValueExposure] at hexposure
        | publish coordinate => exact False.elim (hquery hexposure)
        | reveal coordinate => exact False.elim (hquery hexposure)
        | probe coordinate digest =>
            obtain ⟨rfl, hmatch⟩ := hexposure
            cases fuel with
            | zero => simp [runPrivateCompatibleRecords, runResolvedFromTable_probe_query_bind,
                privateCompatibleRecordedResult, privateRecordedResult, retainCompletableResult]
            | succ remaining =>
                have hhit : truncateHash before ∈ insert digest pending ∨ truncateHash after ∈ insert digest pending := by
                  rcases hmatch with hmatch | hmatch <;> simp [← hmatch]
                have hzero := evalDist_runPrivateCompatibleRecords_eq_none_of_initial_hit target output before after (next ())
                  { context with state := context.state.addPending (.position target) digest } remaining table (insert digest pending) _
                  (h.probe_target digest) (hnext ()) (hcount.2 ()) hhit
                simpa only [runPrivateCompatibleRecords, runResolvedFromTable_probe_query_bind, if_neg h.2.2.1] using hzero
      · rw [if_neg hexposure]
        cases query with
        | uniform n =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_uniform_query_bind, map_bind]
            apply evalDist_bind_congr
            intro reply _
            exact ih reply context fuel pending bound h (hnext reply) (by simpa [IsPrivatePositionProbe] using hcount.2 reply)
        | hashOutput =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_hashOutput_query_bind, map_bind]
            apply evalDist_bind_congr
            intro reply _
            exact ih reply context fuel pending bound h (hnext reply) (by simpa [IsPrivatePositionProbe] using hcount.2 reply)
        | ensure coordinate =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_ensure_query_bind]
            exact ih () { context with state := context.state.ensure coordinate } fuel pending bound h (hnext ())
              (by simpa [IsPrivatePositionProbe] using hcount.2 ())
        | peek coordinate =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_peek_query_bind]
            exact ih _ context fuel pending bound h (hnext _) (by simpa [IsPrivatePositionProbe] using hcount.2 _)
        | publish coordinate =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_publish_query_bind]
            exact ih () _ fuel pending bound (h.publish_other coordinate hquery) (hnext ())
              (by simpa [IsPrivatePositionProbe] using hcount.2 ())
        | probe coordinate digest =>
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_probe_query_bind]
            cases fuel with
            | zero => simp [privateCompatibleRecordedResult, privateRecordedResult,
                retainCompletableResult, privateExposureDoneResult]
            | succ remaining =>
                dsimp only
                split_ifs
                · exact ih () context remaining pending _ h (hnext ()) (hcount.2 ())
                · by_cases htarget : coordinate = .position target
                  · subst coordinate
                    exact ih () _ remaining (insert digest pending) _ (h.probe_target digest) (hnext ()) (hcount.2 ())
                  · exact ih () _ remaining pending _ (h.probe_other coordinate digest htarget) (hnext ()) (hcount.2 ())
        | reveal coordinate =>
            have hbound (reply) : (next reply).IsQueryBoundP (IsPrivatePositionProbe target) bound := by
              simpa [IsPrivatePositionProbe] using hcount.2 reply
            simp only [runPrivateCompatibleRecords, runResolvedFromTable_reveal_query_bind]
            cases coordinate with
            | chainStart lay tree leafIdx chainIdx =>
                simp only [pure_bind]
                cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
                | none => simp [privateCompatibleRecordedResult, privateRecordedResult,
                    retainCompletableResult, privateExposureDoneResult]
                | some middle =>
                    have hvalues := resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩ context middle hresolved
                    exact ih middle.output _ fuel pending bound
                      (h.materialize_other _ middle.output middle.values (by simp) (hvalues ▸ h.2.1))
                      (hnext middle.output) (hbound middle.output)
            | position position =>
                dsimp only
                simp only [map_bind]
                apply evalDist_bind_congr
                intro option hresolve
                cases option with
                | none => simp [privateCompatibleRecordedResult, privateRecordedResult,
                    retainCompletableResult, privateExposureDoneResult]
                | some middle =>
                    have hvalue := privateValue_preserved_by_resolveDeferredReveal target position output table context middle h.1 h.2.1 hresolve
                    exact ih middle.output _ fuel pending bound (h.materialize_other _ middle.output middle.values hquery hvalue)
                      (hnext middle.output) (hbound middle.output)

theorem evalDist_runPrivateCompatibleRecords_preload_eq
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (bound : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hbefore : ¬context.state.hitAt (.position target) before) (hafter : ¬context.state.hitAt (.position target) after)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    evalDist (runPrivateCompatibleRecords target before after (replacePrivatePosition target before context) fuel table computation) =
      evalDist (runPrivateCompatibleRecords target before after (replacePrivatePosition target after context) fuel table computation) := by
  have hinitial (output : HashOutput) : PrivateTargetState target output (context.state.pendingAt (.position target))
      (replacePrivatePosition target output context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
  rw [evalDist_runPrivateCompatibleRecords_eq_exposure_cut target before before after computation _ fuel table _ bound
    (hinitial before) hsafe hcount,
    evalDist_runPrivateCompatibleRecords_eq_exposure_cut target after before after computation _ fuel table _ bound
      (hinitial after) hsafe hcount]
  apply evalDist_map_eq_of_evalDist_eq
  simp only [runPrivateCompatibleRecords_eq_filter]
  apply evalDist_map_eq_of_evalDist_eq
  have hdist := evalDist_privateExposureRecords_preload_swap target before after computation context fuel table hstate hbefore hafter
  rwa [privateValueExposureCut_swap target after before computation] at hdist

end SphincsSecurity.Concrete.OtsProbeSimulation
