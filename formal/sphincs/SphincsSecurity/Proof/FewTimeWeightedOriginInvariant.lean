import SphincsSecurity.Proof.FewTimeWeightedOriginPotential
import SphincsSecurity.Proof.FewTimeWeightedOriginRace

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem OriginMonitorState.weightedPotential_afterDirect_of_sourceAt?_eq_none {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = none) :
    (state.afterDirect input output).weightedPotential reuseWeight event = state.weightedPotential reuseWeight event := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource,
    OriginMonitorState.weightedPotential, OriginMonitorState.pendingSources,
    OriginMonitorState.pendingReuses, OriginMonitorState.completionMass]

theorem OriginMonitorState.weightedPotential_afterDirect_eq_zero_of_invalid {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hinvalid : state.valid = false) :
    (state.afterDirect input output).weightedPotential reuseWeight event = 0 := by
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
  simp [OriginMonitorState.weightedPotential, hafter]

theorem OriginMonitorState.weightedPotential_afterDirect_eq_zero_of_source_failure {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected)
    (hfailure : ¬ (state.viewed.cache input = none ∧
      signAttemptResultOfOutput output ≠ none)) :
    (state.afterDirect input output).weightedPotential reuseWeight event = 0 := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hfailure,
    OriginMonitorState.weightedPotential]

theorem OriginMonitorState.weightedPotential_afterDirect_eq_recordSourceState {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected)
    (hcache : state.viewed.cache input = none)
    (hsuccess : signAttemptResultOfOutput output ≠ none) :
    (state.afterDirect input output).weightedPotential reuseWeight event =
      (state.recordSourceState selected input (hashOutputFewTimeView output)).weightedPotential reuseWeight event := by
  classical
  simp [OriginMonitorState.afterDirect, monitorDirectSource, hsource, hcache, hsuccess,
    OriginMonitorState.recordSourceState, OriginMonitorState.weightedPotential,
    OriginMonitorState.pendingSources, OriginMonitorState.pendingReuses,
    OriginMonitorState.completionMass]

theorem OriginMonitorState.expected_weightedPotential_afterDirect_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (input : HashInput)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result, Pr[= result | (randomOracle input).run state.viewed.cache] *
      (state.afterDirect input result.1).weightedPotential reuseWeight event) ≤ state.weightedPotential reuseWeight event := by
  classical
  cases hsource : configuration.sourceAt? state.directOrdinal with
  | none =>
      simp_rw [state.weightedPotential_afterDirect_of_sourceAt?_eq_none input _ event hsource]
      rw [ENNReal.tsum_mul_right]
      calc
        (∑' result, Pr[= result | (randomOracle input).run state.viewed.cache]) *
            state.weightedPotential reuseWeight event ≤ 1 * state.weightedPotential reuseWeight event := by
          gcongr
          exact tsum_probOutput_le_one
        _ = _ := one_mul _
  | some selected =>
      cases hvalid : state.valid with
      | false =>
          simp_rw [state.weightedPotential_afterDirect_eq_zero_of_invalid input _ event hvalid]
          simp [OriginMonitorState.weightedPotential, hvalid]
      | true =>
          by_cases hcache : state.viewed.cache input = none
          · calc
              (∑' result,
                  Pr[= result | (randomOracle input).run state.viewed.cache] *
                    (state.afterDirect input result.1).weightedPotential reuseWeight event) ≤
                  ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
                    ∑ view, Pr[fun value : FewTimeView => value = view |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (state.recordSourceState selected input view).weightedPotential reuseWeight event := by
                apply tsum_probOutput_randomOracle_fresh_admissible_view_mul_le_expected
                  input state.viewed.cache hcache
                    (fun result => (state.afterDirect input result.1).weightedPotential reuseWeight event)
                    (fun view => (state.recordSourceState selected input view).weightedPotential reuseWeight event)
                · intro result _ hfailed
                  apply state.weightedPotential_afterDirect_eq_zero_of_source_failure
                    selected input result.1 event hsource
                  simp [hcache, hfailed]
                · intro result _ hsuccessful
                  rw [state.weightedPotential_afterDirect_eq_recordSourceState selected input result.1
                    event hsource hcache hsuccessful]
              _ = state.weightedPotential reuseWeight event :=
                state.sum_uniform_weightedPotential_recordSourceState selected input event hvalid
                  (state.sourceAt_not_seenSource selected hcoherent hvalid hsource)
                  (state.sourceAt_not_seenView selected hcoherent hvalid hsource)
                  (state.sourceAt_signer_pending selected hcoherent hvalid hsource)
          · have hfailure : ∀ output : HashOutput,
                ¬ (state.viewed.cache input = none ∧
                  signAttemptResultOfOutput output ≠ none) := by
              intro output hcondition
              exact hcache hcondition.1
            simp_rw [state.weightedPotential_afterDirect_eq_zero_of_source_failure selected input _ event
              hsource (hfailure _)]
            simp

theorem OriginMonitorState.weightedPotential_afterSigner_of_selectedAt?_eq_none {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = none) :
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event = state.weightedPotential reuseWeight event := by
  classical
  rw [show state.afterSigner secretKey request result = state.advanceSigner by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected,
      OriginMonitorState.advanceSigner]]
  exact state.weightedPotential_advanceSigner_of_selectedAt?_eq_none event hselected

theorem OriginMonitorState.weightedPotential_afterSigner_eq_zero_of_invalid {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hinvalid : state.valid = false) :
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event = 0 := by
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
  simp [OriginMonitorState.weightedPotential, hafter]

theorem OriginMonitorState.weightedPotential_afterSigner_eq_zero_of_prehit_failure {reuseWeight : ℝ≥0∞}
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
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event = 0 := by
  classical
  simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hfailure,
    OriginMonitorState.weightedPotential]

theorem OriginMonitorState.weightedPotential_afterSigner_eq_advanceSigner_of_prehit {reuseWeight : ℝ≥0∞}
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
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event =
      state.advanceSigner.weightedPotential reuseWeight event := by
  classical
  rw [show state.afterSigner secretKey request result = state.advanceSigner by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hprehit, hseen, hsuccess,
      OriginMonitorState.advanceSigner]]

theorem OriginMonitorState.weightedPotential_afterSigner_eq_zero_of_fresh_none {reuseWeight : ℝ≥0∞}
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
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event = 0 := by
  classical
  simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hnotPrehit, hnone,
    OriginMonitorState.weightedPotential]

theorem OriginMonitorState.weightedPotential_afterSigner_eq_recordFreshState {reuseWeight : ℝ≥0∞}
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
    (state.afterSigner secretKey request result).weightedPotential reuseWeight event =
      (state.recordFreshState selected view).weightedPotential reuseWeight event := by
  classical
  rw [show state.afterSigner secretKey request result =
      state.recordFreshState selected view by
    simp [OriginMonitorState.afterSigner, monitorSigner, hselected, hnotPrehit, hview,
      OriginMonitorState.recordFreshState]]

set_option maxRecDepth 100000 in
theorem OriginMonitorState.expected_weightedPotential_afterSigner_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hreuse : ∀ target P,
      Pr[PrehitSuccessfulSignerView (onlyInputCache state.viewed.cache target)
        secretKey request P |
        (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] ≤ reuseWeight)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result |
        (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
          (state.afterSigner secretKey request result).weightedPotential reuseWeight event) ≤
      state.weightedPotential reuseWeight event := by
  classical
  cases hselected : pattern.selectedAt? state.signerOrdinal with
  | none =>
      simp_rw [state.weightedPotential_afterSigner_of_selectedAt?_eq_none secretKey request _ event
        hselected]
      rw [ENNReal.tsum_mul_right]
      calc
        (∑' result,
            Pr[= result |
              (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache]) *
              state.weightedPotential reuseWeight event ≤ 1 * state.weightedPotential reuseWeight event := by
          gcongr
          exact tsum_probOutput_le_one
        _ = _ := one_mul _
  | some selected =>
      cases hvalid : state.valid with
      | false =>
          simp_rw [state.weightedPotential_afterSigner_eq_zero_of_invalid secretKey request _ event
            hvalid]
          simp [OriginMonitorState.weightedPotential, hvalid]
      | true =>
          by_cases hprehit : selected ∈ configuration.prehit
          · let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
            by_cases hseen : prehit ∈ state.observation.seenSources
            · calc
                (∑' result,
                    Pr[= result |
                      (simulateQ romImpl
                        (signWithView secretKey request)).run state.viewed.cache] *
                      (state.afterSigner secretKey request result).weightedPotential reuseWeight event) ≤
                    reuseWeight *
                      state.advanceSigner.weightedPotential reuseWeight event := by
                  apply tsum_probOutput_signWithView_fixedPrehit_mul_le_of_weight
                    secretKey request state.viewed.cache
                      (state.observation.sourceInputs prehit)
                      (fun view => view = state.observation.views selected)
                      reuseWeight (hreuse _ _)
                      (fun result =>
                        (state.afterSigner secretKey request result).weightedPotential reuseWeight event)
                      (state.advanceSigner.weightedPotential reuseWeight event)
                  · intro result _ hfailure
                    apply state.weightedPotential_afterSigner_eq_zero_of_prehit_failure
                      secretKey request selected hprehit result event hselected
                    exact fun hcondition => hfailure hcondition.2
                  · intro result _ hsuccess
                    rw [state.weightedPotential_afterSigner_eq_advanceSigner_of_prehit
                      secretKey request selected hprehit result event hselected hseen hsuccess]
                _ = state.weightedPotential reuseWeight event :=
                  state.reuseWeight_mul_weightedPotential_advanceSigner prehit event hvalid hseen
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
              simp_rw [state.weightedPotential_afterSigner_eq_zero_of_prehit_failure
                secretKey request selected hprehit _ event hselected (hfailure _)]
              simp
          · calc
              (∑' result,
                  Pr[= result |
                    (simulateQ romImpl
                      (signWithView secretKey request)).run state.viewed.cache] *
                    (state.afterSigner secretKey request result).weightedPotential reuseWeight event) ≤
                  ∑ view, Pr[fun value : FewTimeView => value = view |
                    ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                      (state.recordFreshState selected view).weightedPotential reuseWeight event := by
                apply tsum_probOutput_signWithView_fresh_mul_le_expected
                  secretKey request state.viewed.cache
                    (fun result =>
                      (state.afterSigner secretKey request result).weightedPotential reuseWeight event)
                    (fun view => (state.recordFreshState selected view).weightedPotential reuseWeight event)
                · intro result _ hnone
                  exact state.weightedPotential_afterSigner_eq_zero_of_fresh_none
                    secretKey request selected result event hselected hprehit hnone
                · intro result _ view hview
                  rw [state.weightedPotential_afterSigner_eq_recordFreshState
                    secretKey request selected result view event hselected hprehit hview]
              _ = state.weightedPotential reuseWeight event :=
                state.sum_uniform_weightedPotential_recordFreshState selected event hvalid
                  (state.selectedAt_fresh_not_seenView selected hcoherent hvalid hselected hprehit)
                  ((pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).mp hselected)
                  hprehit


end Concrete

end SphincsSecurity
