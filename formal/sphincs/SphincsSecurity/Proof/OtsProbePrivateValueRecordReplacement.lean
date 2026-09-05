import SphincsSecurity.Proof.OtsProbePrivateValueProbeRecords

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem PrivatePositionReplaceable.of_mem_runResolved_no_exposure
    {target : Position} {before after : HashOutput}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (h : PrivatePositionReplaceable target before after context)
    (hsafe : computation.IsQueryBoundP (IsPrivateValueExposure target before after) 0)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    PrivatePositionReplaceable target before after result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact h
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivateValueExposure target before after query := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivateValueExposure target before after) 0 := by
        intro reply
        simpa using hsafe.2 reply
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel h (hnext reply) htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, htail⟩ := hresult
          exact ih reply context fuel h (hnext reply) htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel h (hnext ()) hresult
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih _ context fuel h (hnext _) hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel h (hnext ()) hresult
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              split_ifs at hresult
              · exact ih () context remaining h (hnext ()) hresult
              · exact ih () _ remaining (h.addPending coordinate digest hquery) (hnext ()) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [pure_bind] at hresult
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp [hresolved] at hresult
              | some middle =>
                  simp only [hresolved] at hresult
                  have hvalues := resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩ context middle hresolved
                  exact ih middle.output _ fuel (h.materialize_other _ middle.output middle.values (by simp) (hvalues ▸ h.2.1))
                    (hnext middle.output) hresult
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨option, hresolve, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some middle =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position before table context middle h.1 h.2.1 hresolve
                  exact ih middle.output _ fuel (h.materialize_other _ middle.output middle.values hquery hvalue)
                    (hnext middle.output) htail

theorem privateRecordedResult_replace
    (target : Position) (before after : HashOutput) (result : ResolvedRunResult α)
    (h : PrivatePositionReplaceable target before after result.context) :
    privateRecordedResult target (some (replacePrivateRunResult target after result)) = privateRecordedResult target (some result) := by
  unfold privateRecordedResult
  rw [retainCompletableResult_replacePrivateRunResult target before after result h, Option.map_map]
  cases retainCompletableResult (some result) with
  | none => rfl
  | some kept => simp [replacePrivateRunResult, replacePrivatePosition, DeferredStructuralValues.install]

theorem evalDist_runPrivateRecords_replace
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivatePositionReplaceable target before after context)
    (hsafe : computation.IsQueryBoundP (IsPrivateValueExposure target before after) 0) :
    evalDist (runPrivateRecords target (replacePrivatePosition target after context) fuel table computation) =
      evalDist (runPrivateRecords target context fuel table computation) := by
  have hdist := evalDist_runResolved_replacePrivatePosition target before after computation context fuel table h hsafe
  unfold runPrivateRecords
  calc
    _ = evalDist (privateRecordedResult target <$> (Option.map (replacePrivateRunResult target after) <$>
        runResolvedFromTable context fuel table computation)) := evalDist_map_eq_of_evalDist_eq hdist _
    _ = _ := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          simp only [pure_bind, Function.comp_apply, Option.map_some]
          rw [privateRecordedResult_replace target before after result
            (h.of_mem_runResolved_no_exposure computation context fuel table result hsafe hresult)]

theorem evalDist_privateExposureRecords_preload_swap
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hbefore : ¬context.state.hitAt (.position target) before) (hafter : ¬context.state.hitAt (.position target) after) :
    evalDist (runPrivateRecords target (replacePrivatePosition target before context) fuel table
      (privateValueExposureCut target before after computation)) =
      evalDist (runPrivateRecords target (replacePrivatePosition target after context) fuel table
        (privateValueExposureCut target after before computation)) := by
  have hinitial : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hbefore, hafter⟩
  have hdist := evalDist_runPrivateRecords_replace target before after (privateValueExposureCut target before after computation)
    (replacePrivatePosition target before context) fuel table hinitial (privateValueExposureCut_no_exposure target before after computation)
  rw [privateValueExposureCut_swap target after before computation]
  simpa [replacePrivatePosition, DeferredStructuralValues.install] using hdist.symm

end SphincsSecurity.Concrete.OtsProbeSimulation
