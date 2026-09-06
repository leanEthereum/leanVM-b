import SphincsSecurity.Proof.OtsProbeEraseQueries
import SphincsSecurity.Proof.OtsProbeCanonicalStopping

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateViewResultValue (result : Option (DeferredContext × Nat × α)) : Option (Nat × α) :=
  result.map Prod.snd

def rawResolvedResultValue (result : Option (ResolvedRunResult α)) : Option (Nat × α) :=
  result.map (fun result => (result.remaining, result.value))

theorem not_hitAt_of_pendingCovered_nil
    (context : DeferredContext) (h : PendingCovered [] context) (coordinate : Coordinate) (output : HashOutput) :
    ¬context.state.hitAt coordinate output := by
  intro hhit
  rw [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] at hhit
  exact List.not_mem_nil (h _ hhit)

theorem evalDist_privateResolutionResult_value_of_no_pending
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat) (value : α)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table) (hcovered : PendingCovered [] context) :
    evalDist (privateViewResultValue <$> privateResolutionResult target table context fuel value) =
      evalDist (pure (some (fuel, value)) : ProbComp (Option (Nat × α))) := by
  have hcomplete := deferredCompletable_of_no_pending table context hvalid.valuesConsistent hstarts hcovered
  have hnone : none ∉ support (resolveDeferredPositionValue target context) := by
    rw [resolveDeferredPositionValue_eq_bind_output, mem_support_bind_iff]
    rintro ⟨output, _, hresult⟩
    simpa [resolvePrivatePositionWithOutput, not_hitAt_of_pendingCovered_nil context hcovered] using hresult
  unfold privateResolutionResult
  rw [map_bind]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun _ => pure (some (fuel, value))) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => exact False.elim (hnone hresult)
      | some result =>
          have hc := hcomplete.of_resolveDeferredPositionValue hvalid target result hresult
          simp only [if_pos hc, map_pure, privateViewResultValue, Option.map_some]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolveDeferredPositionValue target context) (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput]) _

theorem evalDist_runPrivateResolvedView_value_of_probeFree
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table) (hcovered : PendingCovered [] context)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    evalDist (privateViewResultValue <$> runPrivateResolvedView target table context fuel computation) =
      evalDist (rawResolvedResultValue <$> runResolvedFromTable context fuel table computation) := by
  unfold runPrivateResolvedView
  rw [map_bind, map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hvalid.valuesConsistent hstarts hresult
      have hfinal := valid_pendingCovered_of_mem_runResolvedFromTable_of_probeFree computation context fuel table result []
        hfree hvalid hcovered hresult
      exact evalDist_privateResolutionResult_value_of_no_pending target table result.context result.remaining result.value
        hfinal.1 hcore.2.2 hfinal.2

theorem isQueryBoundP_no_exposure_of_no_access
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (h : computation.IsQueryBoundP (IsPrivatePositionAccess target) 0) :
    computation.IsQueryBoundP (IsPrivateValueExposure target before after) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h ⊢
      have hn : ¬IsPrivatePositionAccess target input := by simpa using h.1
      have he : ¬IsPrivateValueExposure target before after input := by
        cases input <;> simp_all [IsPrivatePositionAccess, IsPrivateValueExposure]
      exact ⟨Or.inl he, fun output => by simpa using ih output (by simpa using h.2 output)⟩

theorem evalDist_rawResolvedValue_preload_eq
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hcovered : PendingCovered [] context)
    (haccess : computation.IsQueryBoundP (IsPrivatePositionAccess target) 0) :
    evalDist (rawResolvedResultValue <$> runResolvedFromTable (replacePrivatePosition target before context) fuel table computation) =
      evalDist (rawResolvedResultValue <$> runResolvedFromTable (replacePrivatePosition target after context) fuel table computation) := by
  have hreplace : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) := by
    refine ⟨hstate, ?_, ?_, ?_⟩
    · simp [replacePrivatePosition, DeferredStructuralValues.install]
    · exact not_hitAt_of_pendingCovered_nil context hcovered _ _
    · exact not_hitAt_of_pendingCovered_nil context hcovered _ _
  have hd := evalDist_runResolved_replacePrivatePosition target before after computation
    (replacePrivatePosition target before context) fuel table hreplace
    (isQueryBoundP_no_exposure_of_no_access target before after computation haccess)
  have hd' : evalDist (runResolvedFromTable (replacePrivatePosition target after context) fuel table computation) =
      evalDist (Option.map (replacePrivateRunResult target after) <$>
        runResolvedFromTable (replacePrivatePosition target before context) fuel table computation) := by
    simpa [replacePrivatePosition, DeferredStructuralValues.install] using hd
  rw [evalDist_map, evalDist_map, hd', evalDist_map, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

theorem evalDist_rawResolvedValue_probeFree_preload
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table) (hcovered : PendingCovered [] context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (haccess : computation.IsQueryBoundP (IsPrivatePositionAccess target) 0) :
    evalDist (rawResolvedResultValue <$> runResolvedFromTable (replacePrivatePosition target output context) fuel table computation) =
      evalDist (rawResolvedResultValue <$> runResolvedFromTable context fuel table computation) := by
  have hcomplete := deferredCompletable_of_no_pending table context hvalid.valuesConsistent hstarts hcovered
  have hpending : context.state.pendingAt (.position target) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro digest hdigest
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hdigest
    exact List.not_mem_nil (hcovered _ hdigest)
  have huniform := evalDist_runPrivateResolvedView_eq_uniform target computation context fuel table hvalid hcomplete hensured hstate hvalue
  have hproject := evalDist_map_eq_of_evalDist_eq huniform (@privateViewResultValue α)
  rw [evalDist_runPrivateResolvedView_value_of_probeFree target table context fuel computation hvalid hstarts hcovered hfree] at hproject
  symm
  apply hproject.trans
  rw [map_bind]
  calc
    _ = evalDist (LazyRevealProbe.sampleHashOutput >>= fun _ =>
        rawResolvedResultValue <$> runResolvedFromTable (replacePrivatePosition target output context) fuel table computation) := by
      apply evalDist_bind_congr
      intro sampled _
      have hclean := not_hitAt_of_pendingCovered_nil context hcovered (.position target) sampled
      have hc : (completePrivatePosition target context sampled).toDeferredContext = replacePrivatePosition target sampled context := by
        simp [completePrivatePosition, replacePrivatePosition,
          clearPending_eq_self_of_pendingAt_empty context.state (.position target) hpending]
      rw [if_neg hclean, hc]
      rw [evalDist_runPrivateResolvedView_value_of_probeFree target table _ fuel computation
        (hvalid.replacePrivatePosition target sampled hstate) hstarts hcovered hfree]
      exact evalDist_rawResolvedValue_preload_eq target sampled output computation context fuel table hstate hcovered haccess
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails LazyRevealProbe.sampleHashOutput (by simp [LazyRevealProbe.sampleHashOutput]) _

end SphincsSecurity.Concrete.OtsProbeSimulation
