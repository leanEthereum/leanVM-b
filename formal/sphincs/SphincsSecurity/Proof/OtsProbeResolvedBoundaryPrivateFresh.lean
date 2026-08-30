import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlan

/-!
# Fresh planned private probes

This file moves one planned structural draw immediately before its candidate and carries a clean miss through the probe-free hash suffix.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem canonicalizeMaterializedValues_eq_of_canonical
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hcanonical : CanonicalMaterializedValues table context) :
    canonicalizeMaterializedValues table context = context := by
  unfold CanonicalMaterializedValues at hcanonical
  cases context with
  | mk state values =>
      cases state with
      | mk pending stateValues revealed ensured =>
          simp only [canonicalizeMaterializedValues]
          rw [← hcanonical]

theorem publicMaterializedValues_addPending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate) (candidate : Digest) :
    publicMaterializedValues table
        { context with state := context.state.addPending coordinate candidate } =
      publicMaterializedValues table context := by
  funext other
  unfold publicMaterializedValues resolvedCompletionValue DeferredContext.positionValue
  rfl

theorem canonicalMaterializedValues_resolve_addPending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (candidate : Digest) (resolved : DeferredResolution)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue position context)) :
    CanonicalMaterializedValues table
      { resolved.toDeferredContext with
        state := resolved.state.addPending (.position position) candidate } := by
  unfold CanonicalMaterializedValues
  have hstate := resolveDeferredPositionValue_state_eq_clearPending position context resolved
    hresolved
  have hpublic := publicMaterializedValues_clearPending_values table context
    (.position position) resolved.values hpublished
  change (resolved.state.addPending (.position position) candidate).values =
    publicMaterializedValues table
      { state := resolved.state.addPending (.position position) candidate
        values := resolved.values }
  rw [hstate]
  change context.state.values = _
  rw [hcanonical]
  rw [publicMaterializedValues_addPending table
    { state := context.state.clearPending (.position position)
      values := resolved.values }
    (.position position) candidate]
  exact hpublic.symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularPrivateProbeFree_le
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (nextObserve : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (epsilon terminalBound : ℝ≥0∞)
    (hprobeFree : ProbeFree computation)
    (hrawClean : ¬PrivateStructuralHit context)
    (hcanonicalClean : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context))
    (hcontinuation : ∀ result : ResolvedRunResult (α × SplitHashCache),
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table (computation.run cache)) →
      PublishedValues result.context.state →
      DeferredCompletable table
        (canonicalizeMaterializedValues table result.context) →
      Pr[= true |
          nextObserve (canonicalizeMaterializedValues table result.context)
            result.remaining result.value] ≤
        (result.remaining : ℝ≥0∞) * epsilon + terminalBound) :
    Pr[= true |
      runDirectDetailedPrivateObserve
        (canonicalizeDirectDetailedPrivateObserve table nextObserve)
        context fuel table (computation.run cache)] ≤
      (fuel : ℝ≥0∞) * epsilon + terminalBound := by
  rw [← probEvent_eq_eq_probOutput]
  unfold runDirectDetailedPrivateObserve
  apply probEvent_bind_le_of_forall_le
  intro detailedResult hdetailed
  have hsafe := canonicalPrivateSafeResult_of_probeFree
    (computation.run cache) context fuel table (hprobeFree cache)
    hrawClean hcanonicalClean detailedResult hdetailed
  cases detailedResult with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hsafe
      | ordinaryHit => simp [finishDirectDetailedPrivateObserve]
      | fuelExhausted => simp [finishDirectDetailedPrivateObserve]
  | done result =>
      simp only [CanonicalPrivateSafeResult] at hsafe
      simp only [finishDirectDetailedPrivateObserve]
      unfold canonicalizeDirectDetailedPrivateObserve
      simp only [hsafe, ↓reduceIte]
      by_cases hpublished : PublishedValues result.context.state
      · simp only [hpublished, ↓reduceIte]
        unfold classifyDirectDetailedPrivateObserve
        simp only [hsafe, ↓reduceIte]
        by_cases hcompletable : DeferredCompletable table
            (canonicalizeMaterializedValues table result.context)
        · simp only [hcompletable, ↓reduceIte]
          have hnext := hcontinuation result hdetailed hpublished hcompletable
          rw [← probEvent_eq_eq_probOutput] at hnext
          refine hnext.trans ?_
          gcongr
          exact_mod_cast
            remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
              (computation.run cache) context fuel table result hdetailed
        · simp [hcompletable]
      · simp [hpublished]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_resolve_addPending_probeFreeSuffix_le
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (position : Position) (candidate : Digest)
    (suffix : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (nextObserve : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (fuel : Nat) (cache : SplitHashCache) (bound : ℝ≥0∞)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (hclean : ¬PrivateStructuralHit context)
    (hsuffix : ProbeFree suffix)
    (hcontinuation : ∀ resolved : DeferredResolution,
      let probeContext : DeferredContext :=
        { resolved.toDeferredContext with
          state := resolved.state.addPending (.position position) candidate }
      ¬PrivateStructuralHit probeContext → DeferredCompletable table probeContext →
      ∀ result : ResolvedRunResult (α × SplitHashCache),
        DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable probeContext fuel table (suffix.run cache)) →
        PublishedValues result.context.state →
        DeferredCompletable table
          (canonicalizeMaterializedValues table result.context) →
        Pr[= true |
            nextObserve (canonicalizeMaterializedValues table result.context)
              result.remaining result.value] ≤ bound) :
    Pr[= true | do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure false
      | some resolved =>
          let probeContext : DeferredContext :=
            { resolved.toDeferredContext with
              state := resolved.state.addPending (.position position) candidate }
          classifyDirectDetailedPrivateObserve table
            (fun nextContext remaining _ =>
              runDirectDetailedPrivateObserve
                (canonicalizeDirectDetailedPrivateObserve table nextObserve)
                nextContext remaining table (suffix.run cache))
            probeContext fuel cache] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ + bound := by
  apply probEvent_resolve_then_classifyDirectDetailedPrivateObserve_le table context position
    candidate
    (fun nextContext remaining _ =>
      runDirectDetailedPrivateObserve
        (canonicalizeDirectDetailedPrivateObserve table nextObserve)
        nextContext remaining table (suffix.run cache))
    fuel cache bound hclean hhidden hprivate
  intro resolved hresolved
  dsimp only
  intro hnextClean hnextCompletable
  have hnextCanonical := canonicalMaterializedValues_resolve_addPending table context position
    candidate resolved hpublished hcanonical hresolved
  have hcanonicalContext : canonicalizeMaterializedValues table
      { resolved.toDeferredContext with
        state := resolved.state.addPending (.position position) candidate } =
      { resolved.toDeferredContext with
        state := resolved.state.addPending (.position position) candidate } := by
    exact canonicalizeMaterializedValues_eq_of_canonical table _ hnextCanonical
  have hsuffixBound := probEvent_granularPrivateProbeFree_le suffix
    { resolved.toDeferredContext with
      state := resolved.state.addPending (.position position) candidate }
    fuel table cache nextObserve 0 bound hsuffix hnextClean
    (by simpa [hcanonicalContext] using hnextClean) (by
      intro result hresult hresultPublished hresultCompletable
      simpa using hcontinuation resolved hnextClean hnextCompletable result hresult
        hresultPublished hresultCompletable)
  simpa using hsuffixBound

end SphincsSecurity.Concrete.OtsProbeSimulation
