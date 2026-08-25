import SphincsSecurity.Proof.FewTimeOriginPotential

/-!
# One-step invariant for the few-time origin monitor

The partial-observation potential is a supermartingale for every query handled by the monitored
adversary implementation. Configured direct sources and signer calls use the local probabilistic
bounds; unconfigured calls preserve the potential exactly.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def OriginMonitorState.afterDirect {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput) :
    OriginMonitorState configuration :=
  let monitored := monitorDirectSource state input output
  { state with
    observation := monitored.1
    directOrdinal := state.directOrdinal + 1
    valid := monitored.2 }

noncomputable def OriginMonitorState.afterSigner {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
    OriginMonitorState configuration :=
  let monitored := monitorSigner secretKey request state result
  { state with
    observation := monitored.1
    signerOrdinal := state.signerOrdinal + 1
    valid := monitored.2 }

theorem OriginMonitorState.potential_afterDirect_of_sourceAt?_eq_none
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = none) :
    (state.afterDirect input output).potential event = state.potential event := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource,
    OriginMonitorState.potential, OriginMonitorState.pendingSources,
    OriginMonitorState.pendingReuses, OriginMonitorState.completionMass]

theorem OriginMonitorState.potential_afterDirect_eq_zero_of_invalid
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hinvalid : state.valid = false) :
    (state.afterDirect input output).potential event = 0 := by
  classical
  have hafter : (state.afterDirect input output).valid = false := by
    cases hsource : configuration.sourceAt? state.directOrdinal with
    | none =>
        simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hinvalid]
    | some selected =>
        by_cases hcondition : state.viewed.cache input = none ∧
          signAttemptResultOfOutput output ≠ none
        · simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcondition,
            hinvalid]
        · simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcondition]
  simp [OriginMonitorState.potential, hafter]

theorem OriginMonitorState.potential_afterDirect_eq_zero_of_source_failure
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected)
    (hfailure : ¬ (state.viewed.cache input = none ∧
      signAttemptResultOfOutput output ≠ none)) :
    (state.afterDirect input output).potential event = 0 := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hfailure,
    OriginMonitorState.potential]

theorem OriginMonitorState.potential_afterDirect_eq_recordSourceState
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected)
    (hcache : state.viewed.cache input = none)
    (hsuccess : signAttemptResultOfOutput output ≠ none) :
    (state.afterDirect input output).potential event =
      (state.recordSourceState selected input (hashOutputFewTimeView output)).potential event := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcache, hsuccess,
    OriginMonitorState.recordSourceState, OriginMonitorState.potential,
    OriginMonitorState.pendingSources, OriginMonitorState.pendingReuses,
    OriginMonitorState.completionMass]

theorem OriginMonitorState.expected_potential_afterDirect_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result, Pr[= result | (randomOracle input).run state.viewed.cache] *
      (state.afterDirect input result.1).potential event) ≤ state.potential event := by
  classical
  cases hsource : configuration.sourceAt? state.directOrdinal with
  | none =>
      simp_rw [state.potential_afterDirect_of_sourceAt?_eq_none input _ event hsource]
      rw [ENNReal.tsum_mul_right]
      calc
        (∑' result, Pr[= result | (randomOracle input).run state.viewed.cache]) *
            state.potential event ≤ 1 * state.potential event := by
          gcongr
          exact tsum_probOutput_le_one
        _ = _ := one_mul _
  | some selected =>
      cases hvalid : state.valid with
      | false =>
          simp_rw [state.potential_afterDirect_eq_zero_of_invalid input _ event hvalid]
          simp [OriginMonitorState.potential, hvalid]
      | true =>
          by_cases hcache : state.viewed.cache input = none
          · calc
              (∑' result,
                  Pr[= result | (randomOracle input).run state.viewed.cache] *
                    (state.afterDirect input result.1).potential event) ≤
                  ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
                    ∑ view, Pr[fun value : FewTimeView => value = view |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (state.recordSourceState selected input view).potential event := by
                apply tsum_probOutput_randomOracle_fresh_admissible_view_mul_le_expected
                  input state.viewed.cache hcache
                    (fun result => (state.afterDirect input result.1).potential event)
                    (fun view => (state.recordSourceState selected input view).potential event)
                · intro result _ hfailed
                  apply state.potential_afterDirect_eq_zero_of_source_failure
                    selected input result.1 event hsource
                  simp [hcache, hfailed]
                · intro result _ hsuccessful
                  rw [state.potential_afterDirect_eq_recordSourceState selected input result.1
                    event hsource hcache hsuccessful]
              _ = state.potential event :=
                state.sum_uniform_potential_recordSourceState selected input event hvalid
                  (state.sourceAt_not_seenSource selected hcoherent hvalid hsource)
                  (state.sourceAt_not_seenView selected hcoherent hvalid hsource)
                  (state.sourceAt_signer_pending selected hcoherent hvalid hsource)
          · have hfailure : ∀ output : HashOutput,
                ¬ (state.viewed.cache input = none ∧
                  signAttemptResultOfOutput output ≠ none) := by
              intro output hcondition
              exact hcache hcondition.1
            simp_rw [state.potential_afterDirect_eq_zero_of_source_failure selected input _ event
              hsource (hfailure _)]
            simp

theorem OriginMonitorState.potential_afterSigner_of_selectedAt?_eq_none
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = none) :
    (state.afterSigner secretKey request result).potential event = state.potential event := by
  classical
  rw [show state.afterSigner secretKey request result = state.advanceSigner by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected,
      OriginMonitorState.advanceSigner]]
  exact state.potential_advanceSigner_of_selectedAt?_eq_none event hselected

theorem OriginMonitorState.potential_afterSigner_eq_zero_of_invalid
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hinvalid : state.valid = false) :
    (state.afterSigner secretKey request result).potential event = 0 := by
  classical
  have hafter : (state.afterSigner secretKey request result).valid = false := by
    cases hselected : pattern.selectedAt? state.signerOrdinal with
    | none =>
        simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hinvalid]
    | some selected =>
        by_cases hprehit : selected ∈ configuration.prehit
        · let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
          by_cases hcondition : prehit ∈ state.observation.seenSources ∧
            PrehitSuccessfulSignerView
              (onlyInputCache state.viewed.cache (state.observation.sourceInputs prehit))
              secretKey request (fun view => view = state.observation.views selected) result
          · simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit,
              prehit, hcondition, hinvalid]
          · simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit,
              prehit, hcondition]
        · cases hview : freshSuccessfulView? state.viewed.cache secretKey request result with
          | none =>
              simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hview]
          | some view =>
              simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hview,
                hinvalid]
  simp [OriginMonitorState.potential, hafter]

theorem OriginMonitorState.potential_afterSigner_eq_zero_of_prehit_failure
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (hprehit : selected ∈ configuration.prehit)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = some selected)
    (hfailure : ¬ ((⟨selected, hprehit⟩ : ↑configuration.prehit) ∈
        state.observation.seenSources ∧
      PrehitSuccessfulSignerView
        (onlyInputCache state.viewed.cache
          (state.observation.sourceInputs ⟨selected, hprehit⟩))
        secretKey request (fun view => view = state.observation.views selected) result)) :
    (state.afterSigner secretKey request result).potential event = 0 := by
  classical
  simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hfailure,
    OriginMonitorState.potential]

theorem OriginMonitorState.potential_afterSigner_eq_advanceSigner_of_prehit
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (hprehit : selected ∈ configuration.prehit)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = some selected)
    (hseen : (⟨selected, hprehit⟩ : ↑configuration.prehit) ∈
      state.observation.seenSources)
    (hsuccess : PrehitSuccessfulSignerView
      (onlyInputCache state.viewed.cache
        (state.observation.sourceInputs ⟨selected, hprehit⟩))
      secretKey request (fun view => view = state.observation.views selected) result) :
    (state.afterSigner secretKey request result).potential event =
      state.advanceSigner.potential event := by
  classical
  rw [show state.afterSigner secretKey request result = state.advanceSigner by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hseen, hsuccess,
      OriginMonitorState.advanceSigner]]

theorem OriginMonitorState.potential_afterSigner_eq_zero_of_fresh_none
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = some selected)
    (hnotPrehit : selected ∉ configuration.prehit)
    (hnone : freshSuccessfulView? state.viewed.cache secretKey request result = none) :
    (state.afterSigner secretKey request result).potential event = 0 := by
  classical
  simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hnotPrehit, hnone,
    OriginMonitorState.potential]

theorem OriginMonitorState.potential_afterSigner_eq_recordFreshState
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (view : FewTimeView) (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = some selected)
    (hnotPrehit : selected ∉ configuration.prehit)
    (hview : freshSuccessfulView? state.viewed.cache secretKey request result = some view) :
    (state.afterSigner secretKey request result).potential event =
      (state.recordFreshState selected view).potential event := by
  classical
  rw [show state.afterSigner secretKey request result =
      state.recordFreshState selected view by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hnotPrehit, hview,
      OriginMonitorState.recordFreshState]]

set_option maxRecDepth 100000 in
theorem OriginMonitorState.expected_potential_afterSigner_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result |
        (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
          (state.afterSigner secretKey request result).potential event) ≤
      state.potential event := by
  classical
  cases hselected : pattern.selectedAt? state.signerOrdinal with
  | none =>
      simp_rw [state.potential_afterSigner_of_selectedAt?_eq_none secretKey request _ event
        hselected]
      rw [ENNReal.tsum_mul_right]
      calc
        (∑' result,
            Pr[= result |
              (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache]) *
              state.potential event ≤ 1 * state.potential event := by
          gcongr
          exact tsum_probOutput_le_one
        _ = _ := one_mul _
  | some selected =>
      cases hvalid : state.valid with
      | false =>
          simp_rw [state.potential_afterSigner_eq_zero_of_invalid secretKey request _ event
            hvalid]
          simp [OriginMonitorState.potential, hvalid]
      | true =>
          by_cases hprehit : selected ∈ configuration.prehit
          · let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
            by_cases hseen : prehit ∈ state.observation.seenSources
            · calc
                (∑' result,
                    Pr[= result |
                      (simulateQ romImpl
                        (signWithView secretKey request)).run state.viewed.cache] *
                      (state.afterSigner secretKey request result).potential event) ≤
                    ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ *
                      state.advanceSigner.potential event := by
                  apply tsum_probOutput_signWithView_fixedPrehit_mul_le_of_enncard_le
                    secretKey request state.viewed.cache
                      (state.observation.sourceInputs prehit)
                      (fun view => view = state.observation.views selected)
                      q hq hcache
                      (fun result =>
                        (state.afterSigner secretKey request result).potential event)
                      (state.advanceSigner.potential event)
                  · intro result _ hfailure
                    apply state.potential_afterSigner_eq_zero_of_prehit_failure
                      secretKey request selected hprehit result event hselected
                    exact fun hcondition => hfailure hcondition.2
                  · intro result _ hsuccess
                    rw [state.potential_afterSigner_eq_advanceSigner_of_prehit
                      secretKey request selected hprehit result event hselected hseen hsuccess]
                _ = state.potential event :=
                  state.reuseWeight_mul_potential_advanceSigner prehit event hvalid hseen
                    ((pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).mp hselected)
            · have hfailure : ∀ result,
                  ¬ (prehit ∈ state.observation.seenSources ∧
                    PrehitSuccessfulSignerView
                      (onlyInputCache state.viewed.cache
                        (state.observation.sourceInputs prehit))
                      secretKey request (fun view => view = state.observation.views selected)
                        result) := by
                intro result hcondition
                exact hseen hcondition.1
              simp_rw [state.potential_afterSigner_eq_zero_of_prehit_failure
                secretKey request selected hprehit _ event hselected (hfailure _)]
              simp
          · calc
              (∑' result,
                  Pr[= result |
                    (simulateQ romImpl
                      (signWithView secretKey request)).run state.viewed.cache] *
                    (state.afterSigner secretKey request result).potential event) ≤
                  ∑ view, Pr[fun value : FewTimeView => value = view |
                    ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                      (state.recordFreshState selected view).potential event := by
                apply tsum_probOutput_signWithView_fresh_mul_le_expected
                  secretKey request state.viewed.cache
                    (fun result =>
                      (state.afterSigner secretKey request result).potential event)
                    (fun view => (state.recordFreshState selected view).potential event)
                · intro result _ hnone
                  exact state.potential_afterSigner_eq_zero_of_fresh_none
                    secretKey request selected result event hselected hprehit hnone
                · intro result _ view hview
                  rw [state.potential_afterSigner_eq_recordFreshState
                    secretKey request selected result view event hselected hprehit hview]
              _ = state.potential event :=
                state.sum_uniform_potential_recordFreshState selected event hvalid
                  (state.selectedAt_fresh_not_seenView selected hcoherent hvalid hselected hprehit)
                  ((pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).mp hselected)
                  hprehit

theorem originMonitoredAdversaryImpl_direct_result_potential
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (_secretKey : SecretKey)
    (state : OriginMonitorState configuration) (input : HashInput)
    (result : HashOutput × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop) :
    let trace := fullAdversaryTraceUpdate (.inl (.inr input)) state.viewed.cache result.1
      result.2 state.viewed.trace
    let monitored := monitorDirectSource state input result.1
    (⟨⟨result.2, trace, state.viewed.views, state.viewed.targetView⟩,
      monitored.1, state.directOrdinal + 1, state.signerOrdinal, monitored.2⟩ :
        OriginMonitorState configuration).potential event =
      (state.afterDirect input result.1).potential event := by
  rfl

theorem originMonitoredAdversaryImpl_uniform_result_potential
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (_secretKey : SecretKey)
    (state : OriginMonitorState configuration) (uniformInput : Nat)
    (result : OracleWorld.Range (.inl uniformInput) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop) :
    let trace := fullAdversaryTraceUpdate (.inl (.inl uniformInput)) state.viewed.cache
      result.1 result.2 state.viewed.trace
    (⟨⟨result.2, trace, state.viewed.views, state.viewed.targetView⟩,
      state.observation, state.directOrdinal, state.signerOrdinal, state.valid⟩ :
        OriginMonitorState configuration).potential event = state.potential event := by
  rfl

theorem originMonitoredAdversaryImpl_signer_result_potential
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (state : OriginMonitorState configuration) (request : SignRequest)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop) :
    let trace := fullAdversaryTraceUpdate (.inr request) state.viewed.cache result.1.1
      result.2 state.viewed.trace
    let monitored := monitorSigner secretKey request state result
    (⟨⟨result.2, trace, state.viewed.views ++ [result.1.2], state.viewed.targetView⟩,
      monitored.1, state.directOrdinal, state.signerOrdinal + 1, monitored.2⟩ :
        OriginMonitorState configuration).potential event =
      (state.afterSigner secretKey request result).potential event := by
  rfl

theorem originMonitoredAdversaryImpl_expected_potential_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result | (originMonitoredAdversaryImpl configuration secretKey input).run state] *
        result.2.potential event) ≤ state.potential event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
            tsum_probOutput_pure_mul]
          change (∑' result,
            Pr[= result | (romImpl (.inl uniformInput)).run state.viewed.cache] *
              state.potential event) ≤ state.potential event
          rw [ENNReal.tsum_mul_right]
          calc
            _ ≤ 1 * state.potential event := by
              gcongr
              exact tsum_probOutput_le_one
            _ = _ := one_mul _
      | inr hashInput =>
          simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
            tsum_probOutput_pure_mul]
          change (∑' result,
            Pr[= result | (randomOracle hashInput).run state.viewed.cache] *
              (state.afterDirect hashInput result.1).potential event) ≤ _
          exact state.expected_potential_afterDirect_le hashInput event hcoherent
  | inr request =>
      simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
        tsum_probOutput_pure_mul]
      simp_rw [originMonitoredAdversaryImpl_signer_result_potential]
      change (∑' result,
        Pr[= result |
          (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
            (state.afterSigner secretKey request result).potential event) ≤ _
      exact state.expected_potential_afterSigner_le secretKey request event q hq hcache hcoherent

end Concrete

end SphincsSecurity
