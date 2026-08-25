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

theorem OriginMonitorState.scheduleCoherent_afterDirect
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput)
    (hcoherent : state.ScheduleCoherent) :
    (state.afterDirect input output).ScheduleCoherent := by
  classical
  intro hafterValid
  cases hsource : configuration.sourceAt? state.directOrdinal with
  | none =>
      have hvalid : state.valid = true := by
        simpa [OriginMonitorState.afterDirect, monitorDirectSource, hsource] using hafterValid
      obtain ⟨hsources, hviews, hsigned⟩ := hcoherent hvalid
      simp only [OriginMonitorState.afterDirect, monitorDirectSource, hsource]
      constructor
      · intro selected
        have hne : (configuration.source.1 selected).val ≠ state.directOrdinal := by
          intro heq
          have hsome :=
            (configuration.sourceAt?_eq_some_iff state.directOrdinal selected).2 heq
          rw [hsource] at hsome
          contradiction
        change selected ∈ state.observation.seenSources ↔
          (configuration.source.1 selected).val < state.directOrdinal + 1
        rw [hsources selected]
        omega
      constructor
      · intro selected
        change selected ∈ state.observation.seenViews ↔
          selected.1.val < state.signerOrdinal ∨
            ∃ hprehit : selected ∈ configuration.prehit,
              (configuration.source.1 ⟨selected, hprehit⟩).val <
                state.directOrdinal + 1
        rw [hviews selected]
        constructor
        · rintro (hsigner | ⟨hprehit, hlt⟩)
          · exact Or.inl hsigner
          · exact Or.inr ⟨hprehit, Nat.lt_succ_of_lt hlt⟩
        · rintro (hsigner | ⟨hprehit, hlt⟩)
          · exact Or.inl hsigner
          · refine Or.inr ⟨hprehit, ?_⟩
            have hne : (configuration.source.1 ⟨selected, hprehit⟩).val ≠
                state.directOrdinal := by
              intro heq
              have hsome := (configuration.sourceAt?_eq_some_iff state.directOrdinal
                (⟨selected, hprehit⟩ : ↑configuration.prehit)).2 heq
              rw [hsource] at hsome
              contradiction
            omega
      · intro selected hprehit hlt
        exact Nat.lt_succ_of_lt (hsigned selected hprehit hlt)
  | some sourceSelected =>
      by_cases hcondition : state.viewed.cache input = none ∧
        signAttemptResultOfOutput output ≠ none
      · have hvalid : state.valid = true := by
          simpa [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcondition]
            using hafterValid
        obtain ⟨hsources, hviews, hsigned⟩ := hcoherent hvalid
        have hsourceEq : (configuration.source.1 sourceSelected).val =
            state.directOrdinal :=
          (configuration.sourceAt?_eq_some_iff state.directOrdinal sourceSelected).1 hsource
        obtain ⟨hcache, hanswer⟩ := hcondition
        simp only [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcache,
          true_and, dif_pos hanswer, OriginObservation.recordSource]
        constructor
        · intro selected
          have hcurrent : (configuration.source.1 selected).val = state.directOrdinal ↔
              selected = sourceSelected := by
            constructor
            · intro heq
              have hsome :=
                (configuration.sourceAt?_eq_some_iff state.directOrdinal selected).2 heq
              rw [hsource] at hsome
              exact (Option.some.inj hsome).symm
            · rintro rfl
              exact hsourceEq
          change selected ∈ insert sourceSelected state.observation.seenSources ↔
            (configuration.source.1 selected).val < state.directOrdinal + 1
          rw [Finset.mem_insert, hsources selected]
          constructor
          · rintro (rfl | hlt)
            · omega
            · omega
          · intro hlt
            have hle : (configuration.source.1 selected).val ≤ state.directOrdinal := by omega
            rcases lt_or_eq_of_le hle with hlt | heq
            · exact Or.inr hlt
            · exact Or.inl ((hcurrent).1 heq)
        constructor
        · intro selected
          change selected ∈ insert sourceSelected.1 state.observation.seenViews ↔
            selected.1.val < state.signerOrdinal ∨
              ∃ hprehit : selected ∈ configuration.prehit,
                (configuration.source.1 ⟨selected, hprehit⟩).val <
                  state.directOrdinal + 1
          rw [Finset.mem_insert, hviews selected]
          constructor
          · rintro (heq | hsigner | ⟨hprehit, hlt⟩)
            · subst selected
              refine Or.inr ⟨sourceSelected.2, ?_⟩
              rw [hsourceEq]
              exact Nat.lt_succ_self _
            · exact Or.inl hsigner
            · exact Or.inr ⟨hprehit, Nat.lt_succ_of_lt hlt⟩
          · rintro (hsigner | ⟨hprehit, hlt⟩)
            · exact Or.inr (Or.inl hsigner)
            · have hle : (configuration.source.1 ⟨selected, hprehit⟩).val ≤
                  state.directOrdinal := by omega
              rcases lt_or_eq_of_le hle with hbefore | hcurrent
              · exact Or.inr (Or.inr ⟨hprehit, hbefore⟩)
              · have hsome := (configuration.sourceAt?_eq_some_iff state.directOrdinal
                    (⟨selected, hprehit⟩ : ↑configuration.prehit)).2 hcurrent
                rw [hsource] at hsome
                have heq : selected = sourceSelected.1 := (congrArg Subtype.val
                  (Option.some.inj hsome)).symm
                exact Or.inl heq
        · intro selected hprehit hlt
          exact Nat.lt_succ_of_lt (hsigned selected hprehit hlt)
      · have : (state.afterDirect input output).valid = false := by
          simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcondition]
        rw [this] at hafterValid
        contradiction

theorem OriginMonitorState.scheduleCoherent_afterSigner
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcoherent : state.ScheduleCoherent) :
    (state.afterSigner secretKey request result).ScheduleCoherent := by
  classical
  intro hafterValid
  cases hselected : pattern.selectedAt? state.signerOrdinal with
  | none =>
      have hvalid : state.valid = true := by
        simpa [OriginMonitorState.afterSigner, monitorSigner, hselected] using hafterValid
      obtain ⟨hsources, hviews, hsigned⟩ := hcoherent hvalid
      simp only [OriginMonitorState.afterSigner, monitorSigner, hselected]
      constructor
      · exact hsources
      constructor
      · intro selected
        have hne : selected.1.val ≠ state.signerOrdinal := by
          intro heq
          have hsome := (pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).2 heq
          rw [hselected] at hsome
          contradiction
        change selected ∈ state.observation.seenViews ↔
          selected.1.val < state.signerOrdinal + 1 ∨
            ∃ hprehit : selected ∈ configuration.prehit,
              (configuration.source.1 ⟨selected, hprehit⟩).val < state.directOrdinal
        rw [hviews selected]
        constructor
        · rintro (hsigner | hsource)
          · exact Or.inl (Nat.lt_succ_of_lt hsigner)
          · exact Or.inr hsource
        · rintro (hsigner | hsource)
          · exact Or.inl (by omega)
          · exact Or.inr hsource
      · intro selected hprehit hlt
        apply hsigned selected hprehit
        have hne : selected.1.val ≠ state.signerOrdinal := by
          intro heq
          have hsome := (pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).2 heq
          rw [hselected] at hsome
          contradiction
        omega
  | some selected =>
      have hselectedEq : selected.1.val = state.signerOrdinal :=
        (pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).1 hselected
      have hcurrent : ∀ candidate : pattern.selected,
          candidate.1.val = state.signerOrdinal ↔ candidate = selected := by
        intro candidate
        constructor
        · intro heq
          have hsome := (pattern.selectedAt?_eq_some_iff state.signerOrdinal candidate).2 heq
          rw [hselected] at hsome
          exact (Option.some.inj hsome).symm
        · rintro rfl
          exact hselectedEq
      by_cases hprehit : selected ∈ configuration.prehit
      · let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
        by_cases hcondition : prehit ∈ state.observation.seenSources ∧
            PrehitSuccessfulSignerView
              (onlyInputCache state.viewed.cache (state.observation.sourceInputs prehit))
              secretKey request (fun view => view = state.observation.views selected) result
        · obtain ⟨hseen, hsuccess⟩ := hcondition
          have hvalid : state.valid = true := by
            simpa [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit,
              prehit, hseen, hsuccess] using hafterValid
          obtain ⟨hsources, hviews, hsigned⟩ := hcoherent hvalid
          have hsourceBefore : (configuration.source.1 prehit).val < state.directOrdinal :=
            (hsources prehit).1 hseen
          simp only [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit,
            prehit, hseen, hsuccess, and_self, dif_pos]
          constructor
          · exact hsources
          constructor
          · intro candidate
            change candidate ∈ state.observation.seenViews ↔
              candidate.1.val < state.signerOrdinal + 1 ∨
                ∃ hcandidate : candidate ∈ configuration.prehit,
                  (configuration.source.1 ⟨candidate, hcandidate⟩).val <
                    state.directOrdinal
            rw [hviews candidate]
            constructor
            · rintro (hsigner | hsource)
              · exact Or.inl (Nat.lt_succ_of_lt hsigner)
              · exact Or.inr hsource
            · rintro (hsigner | hsource)
              · have hle : candidate.1.val ≤ state.signerOrdinal := by omega
                rcases lt_or_eq_of_le hle with hbefore | heq
                · exact Or.inl hbefore
                · have hcand : candidate = selected := (hcurrent candidate).1 heq
                  subst candidate
                  exact Or.inr ⟨hprehit, by simpa [prehit] using hsourceBefore⟩
              · exact Or.inr hsource
          · intro candidate hcandidate hlt
            have hle : candidate.1.val ≤ state.signerOrdinal := by omega
            rcases lt_or_eq_of_le hle with hbefore | heq
            · exact hsigned candidate hcandidate hbefore
            · have hcand : candidate = selected := (hcurrent candidate).1 heq
              subst candidate
              simpa [prehit] using hsourceBefore
        · have hinvalid : (state.afterSigner secretKey request result).valid = false := by
            simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit,
              prehit, hcondition]
          rw [hinvalid] at hafterValid
          contradiction
      · cases hview : freshSuccessfulView? state.viewed.cache secretKey request result with
        | none =>
            have hinvalid : (state.afterSigner secretKey request result).valid = false := by
              simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hview]
            rw [hinvalid] at hafterValid
            contradiction
        | some view =>
            have hvalid : state.valid = true := by
              simpa [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hview]
                using hafterValid
            obtain ⟨hsources, hviews, hsigned⟩ := hcoherent hvalid
            simp only [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hview,
              OriginObservation.recordFresh]
            constructor
            · exact hsources
            constructor
            · intro candidate
              change candidate ∈ insert selected state.observation.seenViews ↔
                candidate.1.val < state.signerOrdinal + 1 ∨
                  ∃ hcandidate : candidate ∈ configuration.prehit,
                    (configuration.source.1 ⟨candidate, hcandidate⟩).val <
                      state.directOrdinal
              rw [Finset.mem_insert, hviews candidate]
              constructor
              · rintro (rfl | hsigner | hsource)
                · exact Or.inl (by omega)
                · exact Or.inl (Nat.lt_succ_of_lt hsigner)
                · exact Or.inr hsource
              · rintro (hsigner | hsource)
                · have hle : candidate.1.val ≤ state.signerOrdinal := by omega
                  rcases lt_or_eq_of_le hle with hbefore | heq
                  · exact Or.inr (Or.inl hbefore)
                  · exact Or.inl ((hcurrent candidate).1 heq)
                · exact Or.inr (Or.inr hsource)
            · intro candidate hcandidate hlt
              have hle : candidate.1.val ≤ state.signerOrdinal := by omega
              rcases lt_or_eq_of_le hle with hbefore | heq
              · exact hsigned candidate hcandidate hbefore
              · have hcand : candidate = selected := (hcurrent candidate).1 heq
                subst candidate
                exact (hprehit hcandidate).elim

theorem originMonitoredAdversaryImpl_query_scheduleCoherent
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginMonitorState configuration)
    (hcoherent : state.ScheduleCoherent)
    (hmem : result ∈ support
      ((originMonitoredAdversaryImpl configuration secretKey input).run state)) :
    result.2.ScheduleCoherent := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          rw [originMonitoredAdversaryImpl] at hmem
          simp only [StateT.run, mem_support_bind_iff] at hmem
          obtain ⟨⟨output, finalCache⟩, _, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [OriginMonitorState.ScheduleCoherent] using hcoherent
      | inr hashInput =>
          rw [originMonitoredAdversaryImpl] at hmem
          simp only [StateT.run, mem_support_bind_iff] at hmem
          obtain ⟨⟨output, finalCache⟩, _, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [OriginMonitorState.ScheduleCoherent, OriginMonitorState.afterDirect] using
            state.scheduleCoherent_afterDirect hashInput output hcoherent
  | inr request =>
      rw [originMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨signature, view⟩, finalCache⟩, _, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      simpa [OriginMonitorState.ScheduleCoherent, OriginMonitorState.afterSigner] using
        state.scheduleCoherent_afterSigner secretKey request ((signature, view), finalCache)
          hcoherent

theorem originMonitoredAdversaryImpl_scheduleCoherent
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (result : α × OriginMonitorState configuration)
    (hcoherent : initialState.ScheduleCoherent)
    (hmem : result ∈ support
      ((simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState)) :
    result.2.ScheduleCoherent := by
  exact OracleComp.simulateQ_run_preservesInv
    (originMonitoredAdversaryImpl configuration secretKey)
    OriginMonitorState.ScheduleCoherent
    (by
      intro input state hstate queryResult hquery
      exact originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey input
        state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem originMonitoredAdversaryImpl_query_cache_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginMonitorState configuration)
    (hmem : result ∈ support
      ((originMonitoredAdversaryImpl configuration secretKey input).run state)) :
    state.viewed.cache ≤ result.2.viewed.cache := by
  classical
  cases input with
  | inl worldInput =>
      rw [originMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, finalCache⟩, hquery, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact unloggedMappedAdversaryImpl_cache_le secretKey (.inl (.inl uniformInput))
            state.viewed.cache (output, finalCache) hquery
      | inr hashInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact unloggedMappedAdversaryImpl_cache_le secretKey (.inl (.inr hashInput))
            state.viewed.cache (output, finalCache) hquery
  | inr request =>
      rw [originMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨signature, view⟩, finalCache⟩, hquery, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact simulateQ_romImpl_cache_le (signWithView secretKey request) state.viewed.cache
        ((signature, view), finalCache) hquery

noncomputable def OriginMonitorState.cappedPotential {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) : ℝ≥0∞ := by
  classical
  exact if QueryCache.enncard state.viewed.cache ≤ q then state.potential event else 0

theorem OriginMonitorState.cappedPotential_le_potential
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) :
    state.cappedPotential q event ≤ state.potential event := by
  classical
  simp only [OriginMonitorState.cappedPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginMonitorState.cappedPotential_eq_of_enncard_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q) :
    state.cappedPotential q event = state.potential event := by
  classical
  simp [OriginMonitorState.cappedPotential, hcache]

theorem OriginMonitorState.cappedPotential_eq_zero_of_not_enncard_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : ¬ QueryCache.enncard state.viewed.cache ≤ q) :
    state.cappedPotential q event = 0 := by
  classical
  simp [OriginMonitorState.cappedPotential, hcache]

theorem originMonitoredAdversaryImpl_expected_cappedPotential_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result | (originMonitoredAdversaryImpl configuration secretKey input).run state] *
        result.2.cappedPotential q event) ≤ state.cappedPotential q event := by
  classical
  by_cases hcache : QueryCache.enncard state.viewed.cache ≤ q
  · rw [state.cappedPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (originMonitoredAdversaryImpl configuration secretKey input).run state] *
            result.2.cappedPotential q event) ≤
          ∑' result,
            Pr[= result |
              (originMonitoredAdversaryImpl configuration secretKey input).run state] *
              result.2.potential event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedPotential_le_potential q event)
      _ ≤ _ := originMonitoredAdversaryImpl_expected_potential_le configuration secretKey input
        state event q hq hcache hcoherent
  · rw [state.cappedPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (originMonitoredAdversaryImpl configuration secretKey input).run state] *
          result.2.cappedPotential q event) = 0 := by
      apply ENNReal.tsum_eq_zero.2
      intro result
      by_cases hresult : result ∈ support
          ((originMonitoredAdversaryImpl configuration secretKey input).run state)
      · have hle := originMonitoredAdversaryImpl_query_cache_le configuration secretKey input
          state result hresult
        have hcard := QueryCache.enncard_mono hle
        have hnotFinal : ¬ QueryCache.enncard result.2.viewed.cache ≤ q := fun hfinal =>
          hcache (hcard.trans hfinal)
        rw [result.2.cappedPotential_eq_zero_of_not_enncard_le q event hnotFinal, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem originMonitoredAdversaryImpl_expected_cappedPotential_simulateQ_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : initialState.ScheduleCoherent) :
    (∑' result,
      Pr[= result |
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
          computation).run initialState] *
        result.2.cappedPotential q event) ≤ initialState.cappedPotential q event := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value =>
      simp [simulateQ_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query,
        tsum_probOutput_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      calc
        (∑' result,
            Pr[= result |
              (originMonitoredAdversaryImpl configuration secretKey input).run initialState] *
              ∑' finalResult,
                Pr[= finalResult |
                  (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
                    (next result.1)).run result.2] *
                  finalResult.2.cappedPotential q event) ≤
            ∑' result,
              Pr[= result |
                (originMonitoredAdversaryImpl configuration secretKey input).run initialState] *
                result.2.cappedPotential q event := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support
              ((originMonitoredAdversaryImpl configuration secretKey input).run initialState)
          · apply mul_le_mul' le_rfl
            exact ih result.1 result.2
              (originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey input
                initialState result hcoherent hresult)
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ ≤ _ := originMonitoredAdversaryImpl_expected_cappedPotential_le configuration
          secretKey input initialState event q hq hcoherent

def OriginMonitorState.Complete {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : Prop :=
  state.valid = true ∧ state.pendingSources = ∅ ∧ state.pendingReuses = ∅ ∧
    state.observation.seenViews = Finset.univ

theorem OriginMonitorState.completionMass_eq_one_of_complete
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hseen : state.observation.seenViews = Finset.univ)
    (hevent : event state.observation.views) :
    state.completionMass event = 1 := by
  classical
  have hcomplete : ∀ fallback,
      state.observation.completeViews fallback = state.observation.views := by
    intro fallback
    funext selected
    simp [OriginObservation.completeViews, hseen]
  rw [OriginMonitorState.completionMass, OriginObservation.completedViews, probEvent_map]
  change Pr[fun fallback : pattern.selected → FewTimeView =>
      event (state.observation.completeViews fallback) |
    ($ᵗ (pattern.selected → FewTimeView) :
      ProbComp (pattern.selected → FewTimeView))] = 1
  simp_rw [hcomplete]
  simp [hevent]

theorem OriginMonitorState.potential_eq_one_of_complete
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcomplete : state.Complete) (hevent : event state.observation.views) :
    state.potential event = 1 := by
  classical
  obtain ⟨hvalid, hsources, hreuses, hviews⟩ := hcomplete
  rw [OriginMonitorState.potential, if_pos hvalid, hsources, hreuses]
  simp only [Finset.card_empty, pow_zero, one_mul]
  exact state.completionMass_eq_one_of_complete event hviews hevent

theorem OriginMonitorState.cappedPotential_eq_one_of_complete
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcomplete : state.Complete) (hevent : event state.observation.views) :
    state.cappedPotential q event = 1 := by
  rw [state.cappedPotential_eq_of_enncard_le q event hcache,
    state.potential_eq_one_of_complete event hcomplete hevent]

theorem probEvent_originMonitored_complete_le_initial
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : initialState.ScheduleCoherent) :
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState] ≤ initialState.cappedPotential q event := by
  let run := (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
    computation).run initialState
  calc
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedPotential q event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := originMonitoredAdversaryImpl_expected_cappedPotential_simulateQ_le
      configuration secretKey computation initialState event q hq hcoherent

theorem probEvent_originMonitored_complete_le_ideal
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run (OriginMonitorState.initial configuration initialCache)] ≤
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[event | ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))] := by
  calc
    _ ≤ (OriginMonitorState.initial configuration initialCache).cappedPotential q event :=
      probEvent_originMonitored_complete_le_initial configuration secretKey computation
        (OriginMonitorState.initial configuration initialCache) event q hq
        (OriginMonitorState.scheduleCoherent_initial configuration initialCache)
    _ = (OriginMonitorState.initial configuration initialCache).potential event :=
      (OriginMonitorState.initial configuration initialCache).cappedPotential_eq_of_enncard_le
        q event hcache
    _ = _ := OriginMonitorState.potential_initial configuration initialCache event

end Concrete

end SphincsSecurity
