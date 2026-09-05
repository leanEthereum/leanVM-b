import SphincsSecurity.Proof.OtsProbePrivateValueFirstAccessRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def PrivateTargetState (target : Position) (output : HashOutput) (pending : Finset Digest)
    (context : DeferredContext) : Prop :=
  context.state.values (.position target) = none ∧ context.values target = some output ∧
    .position target ∉ context.state.revealed ∧ context.state.pendingAt (.position target) = pending

theorem PrivateTargetState.probe_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (digest : Digest)
    (hne : coordinate ≠ .position target) :
    PrivateTargetState target output pending { context with state := context.state.addPending coordinate digest } := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [← h.2.2.2]
  ext candidate
  simp [LazyRevealProbe.State.mem_pendingAt_iff, LazyRevealProbe.State.addPending, Ne.symm hne]

theorem PrivateTargetState.publish_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    PrivateTargetState target output pending { context with state := context.state.publish coordinate } := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  simpa [LazyRevealProbe.State.publish, Ne.symm hne] using h.2.2.1

theorem PrivateTargetState.materialize_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (value : HashOutput)
    (values : DeferredStructuralValues) (hne : coordinate ≠ .position target) (hvalue : values target = some output) :
    PrivateTargetState target output pending { state := context.state.materialize coordinate value, values := values } := by
  refine ⟨?_, hvalue, h.2.2.1, ?_⟩
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne (Ne.symm hne)] using h.1
  · rw [← h.2.2.2]
    ext candidate
    simp [LazyRevealProbe.State.mem_pendingAt_iff, LazyRevealProbe.State.materialize,
      LazyRevealProbe.State.pendingAway, Ne.symm hne]

theorem PrivateTargetState.of_mem_runResolved_no_access
    {target : Position} {output : HashOutput} {pending : Finset Digest}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionAccess target) 0)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    PrivateTargetState target output pending result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact h
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivatePositionAccess target query := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionAccess target) 0 := by
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
          exact ih () _ fuel (h.publish_other coordinate hquery) (hnext ()) hresult
      | probe coordinate digest =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              split_ifs at hresult
              · exact ih () context remaining h (hnext ()) hresult
              · exact ih () _ remaining (h.probe_other coordinate digest hquery) (hnext ()) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [pure_bind] at hresult
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp [hresolved] at hresult
              | some middle =>
                  simp only [hresolved] at hresult
                  have hvalues := resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩
                    context middle hresolved
                  exact ih middle.output _ fuel
                    (h.materialize_other _ middle.output middle.values (by simp) (hvalues ▸ h.2.1))
                    (hnext middle.output) hresult
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨option, hresolve, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some middle =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position output table context middle
                    h.1 h.2.1 hresolve
                  exact ih middle.output _ fuel (h.materialize_other _ middle.output middle.values hquery hvalue)
                    (hnext middle.output) htail

theorem PrivateTargetState.materializedCandidateCharge_eq
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (digest : Digest) :
    materializedCandidateCharge (materializedDeferredState context) (some ⟨.position target, digest⟩) =
      if digest ∈ pending then 0 else 1 := by
  have hpending : (.position target, digest) ∈ context.state.pending ↔ digest ∈ pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff, h.2.2.2]
  simp [materializedCandidateCharge, h.2.2.1, hpending, DeferredContext.positionValue, h.1, h.2.1]

noncomputable def privatePositionCutCharge (target : Position) :
    Option (ResolvedRunResult (PrivateValueCut α)) → ENNReal
  | none => 0
  | some result =>
      match privatePositionAccessCandidate target (some result.value) with
      | none => 0
      | some digest => materializedCandidateCharge (materializedDeferredState result.context) (some ⟨.position target, digest⟩)

theorem privatePositionCutCharge_eq_indicator
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (result : Option (ResolvedRunResult (PrivateValueCut α)))
    (hresult : result ∈ support (runResolvedFromTable (replacePrivatePosition target output context) fuel table
      (privatePositionAccessCut target computation))) :
    privatePositionCutCharge target result =
      if (privatePositionAccessCandidate target (result.map ResolvedRunResult.value)).filter
        (fun digest => digest ∉ context.state.pendingAt (.position target)) ≠ none then 1 else 0 := by
  cases result with
  | none => simp [privatePositionCutCharge, privatePositionAccessCandidate]
  | some result =>
      have hinitial : PrivateTargetState target output (context.state.pendingAt (.position target))
          (replacePrivatePosition target output context) :=
        ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
      have hfinal := PrivateTargetState.of_mem_runResolved_no_access (privatePositionAccessCut target computation)
        (replacePrivatePosition target output context) fuel table result hinitial
        (privatePositionAccessCut_no_access target computation) hresult
      have hcandidate (candidate : Option Digest) :
          (match candidate with
          | none => (0 : ENNReal)
          | some digest => (materializedCandidateCharge (materializedDeferredState result.context)
              (some ⟨.position target, digest⟩) : ENNReal)) =
            if candidate.filter (fun digest => digest ∉ context.state.pendingAt (.position target)) ≠ none then 1 else 0 := by
        cases candidate with
        | none => simp
        | some digest =>
            dsimp only
            rw [hfinal.materializedCandidateCharge_eq]
            by_cases hfresh : digest ∈ context.state.pendingAt (.position target) <;> simp [hfresh]
      exact hcandidate (privatePositionAccessCandidate target (some result.value))

theorem probEvent_privatePositionFirstCandidate_eq_expected_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun candidate => candidate ≠ none | privatePositionFirstCandidate target computation context fuel table output] =
      ∑' result, Pr[= result | runResolvedFromTable (replacePrivatePosition target output context) fuel table
        (privatePositionAccessCut target computation)] * privatePositionCutCharge target result := by
  unfold privatePositionFirstCandidate
  rw [probEvent_map, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable (replacePrivatePosition target output context) fuel table
      (privatePositionAccessCut target computation))
  · rw [privatePositionCutCharge_eq_indicator target computation context fuel table output hstate hhidden result hresult]
    split_ifs <;> simp_all
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

noncomputable def sampledPrivatePositionFirstCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ENNReal :=
  ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] *
    if context.state.hitAt (.position target) output then 0
    else ∑' result, Pr[= result | runResolvedFromTable (replacePrivatePosition target output context) fuel table
      (privatePositionAccessCut target computation)] * privatePositionCutCharge target result

theorem probEvent_sampledPrivatePositionFirstCandidate_eq_expected_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair.2 ≠ none | sampledPrivatePositionFirstCandidate target computation context fuel table] =
      sampledPrivatePositionFirstCharge target computation context fuel table := by
  unfold sampledPrivatePositionFirstCandidate sampledPrivatePositionFirstCharge
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  by_cases hhit : context.state.hitAt (.position target) output
  · simp [hhit]
  · rw [if_neg hhit]
    have hmap : Pr[fun pair : HashOutput × Option Digest => pair.2 ≠ none |
        privatePositionFirstCandidate target computation context fuel table output >>= fun candidate => pure (output, candidate)] =
        Pr[fun candidate => candidate ≠ none | privatePositionFirstCandidate target computation context fuel table output] :=
      probEvent_bind_pure_comp (privatePositionFirstCandidate target computation context fuel table output)
        (fun candidate => (output, candidate)) (fun pair => pair.2 ≠ none)
    rw [hmap, probEvent_privatePositionFirstCandidate_eq_expected_charge target computation context fuel table output hstate hhidden,
      if_neg hhit]

theorem probEvent_sampledPrivatePositionFirstCandidate_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : context.state.pending.card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampledPrivatePositionFirstCandidate target computation context fuel table] ≤
      sampledPrivatePositionFirstCharge target computation context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [← probEvent_sampledPrivatePositionFirstCandidate_eq_expected_charge target computation context fuel table hstate hhidden]
  exact probEvent_sampledPrivatePositionFirstCandidate_hit_le_four_thirds target computation context fuel table hstate hcard

theorem probEvent_sampledPrivatePositionFirstCandidate_hit_le_charge_of_no_pending
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hpending : context.state.pendingAt (.position target) = ∅) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampledPrivatePositionFirstCandidate target computation context fuel table] ≤
      sampledPrivatePositionFirstCharge target computation context fuel table * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [← probEvent_sampledPrivatePositionFirstCandidate_eq_expected_charge target computation context fuel table hstate hhidden]
  exact probEvent_sampledPrivatePositionFirstCandidate_hit_le_of_no_pending target computation context fuel table hstate hpending

end SphincsSecurity.Concrete.OtsProbeSimulation
