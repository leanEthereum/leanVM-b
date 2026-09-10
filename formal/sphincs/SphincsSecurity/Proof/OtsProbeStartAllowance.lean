import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk
import SphincsSecurity.Proof.OtsProbeLiveStartCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def startProbeInputAllowance (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    LazyRevealProbe.Query Coordinate → ENNReal
  | .probe coordinate digest => unresolvedStartCandidateAllowance table context (some ⟨coordinate, digest⟩)
  | _ => 0

theorem startProbeInputAllowance_of_not_probe (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : LazyRevealProbe.Query Coordinate) (hprobe : ¬LazyRevealProbe.IsProbe input) :
    startProbeInputAllowance table context input = 0 := by
  cases input <;> simp_all [startProbeInputAllowance, LazyRevealProbe.IsProbe]

noncomputable def liveStartProbeAllowance (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        startProbeInputAllowance table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

theorem liveStartProbeAllowance_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveStartProbeAllowance ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        startProbeInputAllowance table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => liveStartProbeAllowance (next result.value) result.context result.remaining result.table
      else 0) := rfl

noncomputable def expectedLiveStartCutAllowance
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable context fuel table computation] *
    historyUnresolvedStartAllowance nativeCutCandidate (retainCompletableResult result)

theorem expectedLiveStartCutAllowance_eq_hitProbability
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveStartCutAllowance computation context fuel table =
      Pr[LiveUnresolvedStartHit nativeCutCandidate | runResolvedFromTable context fuel table computation] :=
  (probEvent_liveUnresolvedStartHit_eq_expected _ _).symm

theorem expectedLiveStartCutAllowance_pure
    (value : PrivateValueCut α) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveStartCutAllowance (pure value) context fuel table =
      if DeferredCompletable table context then unresolvedStartCandidateAllowance table context (nativeCutCandidate context value) else 0 := by
  by_cases hcomplete : DeferredCompletable table context <;>
    simp [expectedLiveStartCutAllowance, runResolvedFromTable, historyUnresolvedStartAllowance, retainCompletableResult, hcomplete]

theorem expectedLiveStartCutAllowance_bind
    (computation : OracleComp (LazyRevealProbe.World Coordinate) β)
    (next : β → OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveStartCutAllowance (computation >>= next) context fuel table =
      ∑' result, Pr[= result | runResolvedFromTable context fuel table computation] *
        match result with
        | none => 0
        | some result => expectedLiveStartCutAllowance (next result.value) result.context result.remaining result.table := by
  unfold expectedLiveStartCutAllowance
  rw [runResolvedFromTable_bind, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  cases result with
  | none => simp [historyUnresolvedStartAllowance, retainCompletableResult]
  | some result => rfl

theorem expectedLiveStartCutAllowance_eq_zero_of_not_completable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    expectedLiveStartCutAllowance computation context fuel table = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable context fuel table computation)
  · cases result with
    | none => simp [historyUnresolvedStartAllowance, retainCompletableResult]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
        have hstill := not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult hdoomed
        simp [historyUnresolvedStartAllowance, retainCompletableResult, hcore.1, hstill]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
