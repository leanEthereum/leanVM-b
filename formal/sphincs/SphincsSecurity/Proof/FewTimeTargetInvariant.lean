import SphincsSecurity.Proof.FewTimeTargetMonitor
import SphincsSecurity.Proof.FewTimeTargetCompletion

/-!
# One-step invariant for one adaptive few-time target

The joint potential lifts the origin supermartingale while a fixed candidate ordinal is pending,
then fixes the candidate's view when that ordinal is reached.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def OriginTargetMonitorState.afterDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput) : OriginTargetMonitorState configuration :=
  let advanced := state.advanceOrigin (state.origin.afterDirect input output)
  if state.origin.viewed.cache input = none then
    advanced.recordCandidate targetOrdinal
      (decide (configuration.sourceAt? state.origin.directOrdinal = none))
      (hashOutputFewTimeView output)
  else advanced

theorem OriginTargetMonitorState.targetScheduleCoherent_afterDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.afterDirect targetOrdinal input output).TargetScheduleCoherent
      targetOrdinal := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [OriginTargetMonitorState.afterDirect, hfresh, if_true]
    exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate targetOrdinal
      (state.advanceOrigin (state.origin.afterDirect input output)) _ _
      (state.targetScheduleCoherent_advanceOrigin targetOrdinal _ hcoherent)
  · simpa [OriginTargetMonitorState.afterDirect, hfresh] using
      state.targetScheduleCoherent_advanceOrigin targetOrdinal
        (state.origin.afterDirect input output) hcoherent

theorem OriginTargetMonitorState.potential_afterDirect_of_ordinal_ne
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterDirect targetOrdinal input output).potential event =
      (state.advanceOrigin (state.origin.afterDirect input output)).potential event := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [OriginTargetMonitorState.afterDirect, hfresh, if_true]
    exact OriginTargetMonitorState.potential_recordCandidate_of_ordinal_ne
      targetOrdinal _ _ _ event hne
  · simp [OriginTargetMonitorState.afterDirect, hfresh]

theorem OriginTargetMonitorState.potential_advanceOrigin_congr
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (left right : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcongr : ∀ target,
      left.potential (fun views => event (views, target)) =
        right.potential (fun views => event (views, target))) :
    (state.advanceOrigin left).potential event =
      (state.advanceOrigin right).potential event := by
  classical
  simp only [OriginTargetMonitorState.advanceOrigin,
    OriginTargetMonitorState.potential]
  split
  · cases state.targetView with
    | none => simp_rw [hcongr]
    | some target => exact hcongr target
  · rfl

theorem OriginTargetMonitorState.potential_recordCandidate_advanceOrigin_congr
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (left right : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcongr : ∀ target,
      left.potential (fun views => event (views, target)) =
        right.potential (fun views => event (views, target))) :
    ((state.advanceOrigin left).recordCandidate targetOrdinal allowed view).potential event =
      ((state.advanceOrigin right).recordCandidate targetOrdinal allowed view).potential event := by
  classical
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · cases hstate : state.valid <;> cases hallowed : allowed <;>
      simp [OriginTargetMonitorState.recordCandidate,
        OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.potential,
        heq, hstate, hcongr]
  · by_cases hvalid : state.valid = true
    · cases htarget : state.targetView with
      | none =>
          simp [OriginTargetMonitorState.recordCandidate,
            OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.potential,
            heq, hvalid, htarget]
          simp_rw [hcongr]
      | some target =>
          simpa [OriginTargetMonitorState.recordCandidate,
            OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.potential,
            heq, hvalid, htarget] using hcongr target
    · simp [OriginTargetMonitorState.recordCandidate,
        OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.potential,
        heq, hvalid]

noncomputable def OriginTargetMonitorState.afterSigner
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (targetRun : TargetSignerResult × QueryCache HashSpec) :
    OriginTargetMonitorState configuration :=
  let signerRun := (targetSignerResultView targetRun.1, targetRun.2)
  let advanced := state.advanceOrigin
    (state.origin.afterSigner secretKey request signerRun)
  match targetRun.1.2 with
  | none => advanced
  | some (input, view) =>
      if state.origin.viewed.cache input = none then
        advanced.recordCandidate targetOrdinal
          (decide (pattern.selectedAt? state.origin.signerOrdinal = none)) view
      else advanced

theorem OriginTargetMonitorState.targetScheduleCoherent_afterSigner
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (targetRun : TargetSignerResult × QueryCache HashSpec)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.afterSigner targetOrdinal secretKey request targetRun).TargetScheduleCoherent
      targetOrdinal := by
  cases hselection : targetRun.1.2 with
  | none =>
      simpa [OriginTargetMonitorState.afterSigner, hselection] using
        state.targetScheduleCoherent_advanceOrigin targetOrdinal
          (state.origin.afterSigner secretKey request
            (targetSignerResultView targetRun.1, targetRun.2)) hcoherent
  | some selection =>
      rcases selection with ⟨input, view⟩
      by_cases hfresh : state.origin.viewed.cache input = none
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_true]
        exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate targetOrdinal
          (state.advanceOrigin (state.origin.afterSigner secretKey request
            (targetSignerResultView targetRun.1, targetRun.2))) _ _
          (state.targetScheduleCoherent_advanceOrigin targetOrdinal _ hcoherent)
      · simpa [OriginTargetMonitorState.afterSigner, hselection, hfresh] using
          state.targetScheduleCoherent_advanceOrigin targetOrdinal
            (state.origin.afterSigner secretKey request
              (targetSignerResultView targetRun.1, targetRun.2)) hcoherent

theorem OriginTargetMonitorState.potential_afterSigner_of_ordinal_ne
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (targetRun : TargetSignerResult × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterSigner targetOrdinal secretKey request targetRun).potential event =
      (state.advanceOrigin (state.origin.afterSigner secretKey request
        (targetSignerResultView targetRun.1, targetRun.2))).potential event := by
  cases hselection : targetRun.1.2 with
  | none => simp [OriginTargetMonitorState.afterSigner, hselection]
  | some selection =>
      rcases selection with ⟨input, view⟩
      by_cases hfresh : state.origin.viewed.cache input = none
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_true]
        exact OriginTargetMonitorState.potential_recordCandidate_of_ordinal_ne
          targetOrdinal _ _ _ event hne
      · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh]

theorem OriginMonitorState.expected_potential_afterTargetSigner_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcoherent : state.ScheduleCoherent) :
    (∑' targetRun,
      Pr[= targetRun |
        (simulateQ romImpl (signWithTargetView secretKey request)).run state.viewed.cache] *
        (state.afterSigner secretKey request
          (targetSignerResultView targetRun.1, targetRun.2)).potential event) ≤
      state.potential event := by
  calc
    _ = ∑' signerRun,
        Pr[= signerRun |
          (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
          (state.afterSigner secretKey request signerRun).potential event := by
      rw [← simulateQ_signWithTargetView_projection_run]
      rw [tsum_probOutput_map_mul]
    _ ≤ _ := state.expected_potential_afterSigner_le secretKey request event q hq
      hcache hcoherent

theorem OriginTargetMonitorState.expected_potential_advanceOrigin_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (mass : α → ℝ≥0∞) (nextOrigin : α → OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hnext : ∀ target,
      (∑' result, mass result *
        (nextOrigin result).potential (fun views => event (views, target))) ≤
      state.origin.potential (fun views => event (views, target))) :
    (∑' result, mass result *
      (state.advanceOrigin (nextOrigin result)).potential event) ≤
      state.potential event := by
  classical
  cases hvalid : state.valid with
  | false =>
      simp [OriginTargetMonitorState.potential,
        OriginTargetMonitorState.advanceOrigin, hvalid]
  | true =>
      cases htarget : state.targetView with
      | some target =>
          simpa [OriginTargetMonitorState.potential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget] using hnext target
      | none =>
          simp only [OriginTargetMonitorState.potential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget, if_true]
          calc
            (∑' result, mass result *
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    (nextOrigin result).potential (fun views => event (views, target))) =
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    ∑' result, mass result *
                      (nextOrigin result).potential
                        (fun views => event (views, target)) := by
              calc
                _ = ∑' result, ∑ target,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).potential
                          (fun views => event (views, target))) := by
                    apply tsum_congr
                    intro result
                    rw [Finset.mul_sum]
                _ = ∑ target, ∑' result,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).potential
                          (fun views => event (views, target))) := by
                    exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
                _ = _ := by
                    apply Finset.sum_congr rfl
                    intro target _
                    calc
                      _ = ∑' result,
                          Pr[fun value : FewTimeView => value = target |
                              ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                            (mass result *
                              (nextOrigin result).potential
                                (fun views => event (views, target))) := by
                            apply tsum_congr
                            intro result
                            ac_rfl
                      _ = _ := ENNReal.tsum_mul_left
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro target _
              exact mul_le_mul' le_rfl (hnext target)

theorem OriginTargetMonitorState.expected_potential_afterDirect_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result, Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
      (state.afterDirect targetOrdinal input result.1).potential event) ≤
      state.potential event := by
  classical
  by_cases hfresh : state.origin.viewed.cache input = none
  · by_cases heq : state.candidateOrdinal = targetOrdinal
    · cases hsource : configuration.sourceAt? state.origin.directOrdinal with
      | some selected =>
          have hzero : ∀ output,
              (state.afterDirect targetOrdinal input output).potential event = 0 := by
            intro output
            rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
            rw [show decide
              (configuration.sourceAt? state.origin.directOrdinal = none) = false by
                simp [hsource]]
            apply OriginTargetMonitorState.potential_recordCandidate_eq_of_disallowed
            simpa [OriginTargetMonitorState.advanceOrigin] using heq
          simp_rw [hzero]
          simp
      | none =>
          cases hvalid : state.valid with
          | false =>
              have hzero : ∀ output,
                  (state.afterDirect targetOrdinal input output).potential event = 0 := by
                intro output
                rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
                apply OriginTargetMonitorState.potential_eq_zero_of_invalid
                simp [OriginTargetMonitorState.recordCandidate,
                  OriginTargetMonitorState.advanceOrigin, heq, hvalid]
              simp_rw [hzero]
              simp [OriginTargetMonitorState.potential, hvalid]
          | true =>
              have htargetView : state.targetView = none :=
                state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
              calc
                (∑' result,
                    Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
                      (state.afterDirect targetOrdinal input result.1).potential event) ≤
                    ∑ target, Pr[fun value : FewTimeView => value = target |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        state.origin.potential (fun views => event (views, target)) := by
                  apply tsum_probOutput_randomOracle_fresh_view_mul_le_expected
                    input state.origin.viewed.cache hfresh
                  intro result _
                  simp [OriginTargetMonitorState.afterDirect, hfresh, hsource,
                    OriginTargetMonitorState.recordCandidate,
                    OriginTargetMonitorState.advanceOrigin,
                    OriginTargetMonitorState.potential, heq, hvalid,
                    state.origin.potential_afterDirect_of_sourceAt?_eq_none
                      input result.1 _ hsource]
                _ = state.potential event := by
                  simp [OriginTargetMonitorState.potential, hvalid, htargetView]
    · simp_rw [state.potential_afterDirect_of_ordinal_ne targetOrdinal input _ event heq]
      apply state.expected_potential_advanceOrigin_le
      intro target
      exact state.origin.expected_potential_afterDirect_le input
        (fun views => event (views, target)) horigin
  · simp_rw [OriginTargetMonitorState.afterDirect, hfresh, if_false]
    apply state.expected_potential_advanceOrigin_le
    intro target
    exact state.origin.expected_potential_afterDirect_le input
      (fun views => event (views, target)) horigin

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem OriginTargetMonitorState.expected_potential_afterSigner_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' targetRun,
      Pr[= targetRun |
        (simulateQ romImpl (signWithTargetView secretKey request)).run
          state.origin.viewed.cache] *
        (state.afterSigner targetOrdinal secretKey request targetRun).potential event) ≤
      state.potential event := by
  classical
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · cases hselected : pattern.selectedAt? state.origin.signerOrdinal with
    | some selected =>
        calc
          (∑' targetRun,
              Pr[= targetRun |
                (simulateQ romImpl (signWithTargetView secretKey request)).run
                  state.origin.viewed.cache] *
                (state.afterSigner targetOrdinal secretKey request targetRun).potential
                  event) ≤
              ∑' targetRun,
                Pr[= targetRun |
                  (simulateQ romImpl (signWithTargetView secretKey request)).run
                    state.origin.viewed.cache] *
                  (state.advanceOrigin (state.origin.afterSigner secretKey request
                    (targetSignerResultView targetRun.1, targetRun.2))).potential event := by
            apply ENNReal.tsum_le_tsum
            intro targetRun
            apply mul_le_mul' le_rfl
            cases hselection : targetRun.1.2 with
            | none =>
                simp [OriginTargetMonitorState.afterSigner, hselection]
            | some selection =>
                rcases selection with ⟨input, view⟩
                by_cases hfresh : state.origin.viewed.cache input = none
                · have hdisallowed : decide
                      (pattern.selectedAt? state.origin.signerOrdinal = none) = false := by
                    simp [hselected]
                  rw [OriginTargetMonitorState.afterSigner]
                  simp only [hselection]
                  rw [if_pos hfresh, hdisallowed]
                  rw [OriginTargetMonitorState.potential_recordCandidate_eq_of_disallowed]
                  · exact zero_le
                  · simpa [OriginTargetMonitorState.advanceOrigin] using heq
                · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh]
          _ ≤ state.potential event := by
            apply state.expected_potential_advanceOrigin_le
            intro target
            exact state.origin.expected_potential_afterTargetSigner_le secretKey request
              (fun views => event (views, target)) q hq hcache horigin
    | none =>
        cases hvalid : state.valid with
        | false =>
            have hzero : ∀ targetRun,
                (state.afterSigner targetOrdinal secretKey request targetRun).potential
                  event = 0 := by
              intro targetRun
              apply OriginTargetMonitorState.potential_eq_zero_of_invalid
              cases hselection : targetRun.1.2 with
              | none =>
                  simp [OriginTargetMonitorState.afterSigner, hselection,
                    OriginTargetMonitorState.advanceOrigin, hvalid]
              | some selection =>
                  rcases selection with ⟨input, view⟩
                  by_cases hfresh : state.origin.viewed.cache input = none
                  · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh,
                      OriginTargetMonitorState.recordCandidate,
                      OriginTargetMonitorState.advanceOrigin, hvalid]
                  · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh,
                      OriginTargetMonitorState.advanceOrigin, hvalid]
            simp_rw [hzero]
            simp [OriginTargetMonitorState.potential, hvalid]
        | true =>
            have htargetView : state.targetView = none :=
              state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
            rw [OriginTargetMonitorState.potential, if_pos hvalid, htargetView]
            let signerCost := fun targetRun : TargetSignerResult × QueryCache HashSpec =>
              (state.afterSigner targetOrdinal secretKey request targetRun).potential event
            let signerRisk := fun target : FewTimeView =>
              state.origin.potential (fun views => event (views, target))
            refine tsum_probOutput_signWithTargetView_completed_le_expected
              secretKey request state.origin.viewed.cache signerCost signerRisk ?_ ?_
            · intro targetRun _hsupport hnone
              dsimp only [signerCost, signerRisk]
              cases hselection : targetRun.1.2 with
              | none =>
                  simp [OriginTargetMonitorState.afterSigner, hselection,
                    OriginTargetMonitorState.potential,
                    OriginTargetMonitorState.advanceOrigin, hvalid, htargetView,
                    state.origin.potential_afterSigner_of_selectedAt?_eq_none
                      secretKey request
                        (targetSignerResultView targetRun.1, targetRun.2) _ hselected]
              | some selection =>
                  rcases selection with ⟨input, view⟩
                  have hfresh : state.origin.viewed.cache input ≠ none := by
                    simpa [freshTargetSignerView?, hselection] using hnone
                  simp [OriginTargetMonitorState.afterSigner, hselection, hfresh,
                    OriginTargetMonitorState.potential,
                    OriginTargetMonitorState.advanceOrigin, hvalid, htargetView,
                    state.origin.potential_afterSigner_of_selectedAt?_eq_none
                      secretKey request
                        (targetSignerResultView targetRun.1, targetRun.2) _ hselected]
            · intro targetRun _hsupport target hsome
              dsimp only [signerCost, signerRisk]
              cases hselection : targetRun.1.2 with
              | none => simp [freshTargetSignerView?, hselection] at hsome
              | some selection =>
                  rcases selection with ⟨input, view⟩
                  have hfresh : state.origin.viewed.cache input = none := by
                    by_contra hnot
                    simp [freshTargetSignerView?, hselection, hnot] at hsome
                  have hview : view = target := by
                    simpa [freshTargetSignerView?, hselection, hfresh] using hsome
                  subst view
                  simp [OriginTargetMonitorState.afterSigner, hselection, hfresh,
                    OriginTargetMonitorState.recordCandidate,
                    OriginTargetMonitorState.advanceOrigin,
                    OriginTargetMonitorState.potential, heq, hvalid, hselected,
                    state.origin.potential_afterSigner_of_selectedAt?_eq_none
                      secretKey request
                        (targetSignerResultView targetRun.1, targetRun.2) _ hselected]
  · simp_rw [state.potential_afterSigner_of_ordinal_ne targetOrdinal secretKey request _
      event heq]
    apply state.expected_potential_advanceOrigin_le
    intro target
    exact state.origin.expected_potential_afterTargetSigner_le secretKey request
      (fun views => event (views, target)) q hq hcache horigin

theorem originTargetMonitoredAdversaryImpl_direct_result_potential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (result : HashOutput × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    let trace := fullAdversaryTraceUpdate (.inl (.inr input)) state.origin.viewed.cache
      result.1 result.2 state.origin.viewed.trace
    let monitored := monitorDirectSource state.origin input result.1
    let origin : OriginMonitorState configuration :=
      ⟨⟨result.2, trace, state.origin.viewed.views, state.origin.viewed.targetView⟩,
        monitored.1, state.origin.directOrdinal + 1, state.origin.signerOrdinal,
        monitored.2⟩
    let advanced := state.advanceOrigin origin
    (if state.origin.viewed.cache input = none then
      advanced.recordCandidate targetOrdinal
        (decide (configuration.sourceAt? state.origin.directOrdinal = none))
        (hashOutputFewTimeView result.1)
    else advanced).potential event =
      (state.afterDirect targetOrdinal input result.1).potential event := by
  classical
  dsimp only
  have horigin : ∀ target,
      (⟨⟨result.2,
          fullAdversaryTraceUpdate (.inl (.inr input)) state.origin.viewed.cache
            result.1 result.2 state.origin.viewed.trace,
          state.origin.viewed.views, state.origin.viewed.targetView⟩,
        (monitorDirectSource state.origin input result.1).1,
        state.origin.directOrdinal + 1, state.origin.signerOrdinal,
        (monitorDirectSource state.origin input result.1).2⟩ :
          OriginMonitorState configuration).potential
          (fun views => event (views, target)) =
        (state.origin.afterDirect input result.1).potential
          (fun views => event (views, target)) := by
    intro target
    exact originMonitoredAdversaryImpl_direct_result_potential configuration secretKey
      state.origin input result (fun views => event (views, target))
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [hfresh, if_true, OriginTargetMonitorState.afterDirect]
    exact OriginTargetMonitorState.potential_recordCandidate_advanceOrigin_congr
      targetOrdinal state _ _ _ _ event horigin
  · simp only [hfresh, if_false, OriginTargetMonitorState.afterDirect]
    exact state.potential_advanceOrigin_congr _ _ event horigin

theorem originTargetMonitoredAdversaryImpl_signer_result_potential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (request : SignRequest) (targetRun : TargetSignerResult × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    let signerRun := (targetSignerResultView targetRun.1, targetRun.2)
    let trace := fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache
      signerRun.1.1 signerRun.2 state.origin.viewed.trace
    let monitored := monitorSigner secretKey request state.origin signerRun
    let origin : OriginMonitorState configuration :=
      ⟨⟨signerRun.2, trace, state.origin.viewed.views ++ [signerRun.1.2],
        state.origin.viewed.targetView⟩, monitored.1, state.origin.directOrdinal,
        state.origin.signerOrdinal + 1, monitored.2⟩
    let advanced := state.advanceOrigin origin
    (match targetRun.1.2 with
    | none => advanced
    | some (input, view) =>
        if state.origin.viewed.cache input = none then
          advanced.recordCandidate targetOrdinal
            (decide (pattern.selectedAt? state.origin.signerOrdinal = none)) view
        else advanced).potential event =
      (state.afterSigner targetOrdinal secretKey request targetRun).potential event := by
  classical
  dsimp only
  have horigin : ∀ target,
      (⟨⟨targetRun.2,
          fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache
            (targetSignerResultView targetRun.1).1 targetRun.2 state.origin.viewed.trace,
          state.origin.viewed.views ++ [(targetSignerResultView targetRun.1).2],
          state.origin.viewed.targetView⟩,
        (monitorSigner secretKey request state.origin
          (targetSignerResultView targetRun.1, targetRun.2)).1,
        state.origin.directOrdinal, state.origin.signerOrdinal + 1,
        (monitorSigner secretKey request state.origin
          (targetSignerResultView targetRun.1, targetRun.2)).2⟩ :
          OriginMonitorState configuration).potential
          (fun views => event (views, target)) =
        (state.origin.afterSigner secretKey request
          (targetSignerResultView targetRun.1, targetRun.2)).potential
            (fun views => event (views, target)) := by
    intro target
    exact originMonitoredAdversaryImpl_signer_result_potential configuration secretKey
      state.origin request (targetSignerResultView targetRun.1, targetRun.2)
        (fun views => event (views, target))
  cases hselection : targetRun.1.2 with
  | none =>
      simp only [OriginTargetMonitorState.afterSigner, hselection]
      exact state.potential_advanceOrigin_congr _ _ event horigin
  | some selection =>
      rcases selection with ⟨input, view⟩
      by_cases hfresh : state.origin.viewed.cache input = none
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_true]
        exact OriginTargetMonitorState.potential_recordCandidate_advanceOrigin_congr
          targetOrdinal state _ view _ _ event horigin
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_false]
        exact state.potential_advanceOrigin_congr _ _ event horigin

theorem originTargetMonitoredAdversaryImpl_expected_potential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.potential event) ≤
      state.potential event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [originTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          apply state.expected_potential_advanceOrigin_le
          intro target
          exact originMonitoredAdversaryImpl_expected_potential_le configuration secretKey
            (.inl (.inl uniformInput)) state.origin (fun views => event (views, target))
              q hq hcache horigin
      | inr hashInput =>
          simp only [originTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
            originMonitoredAdversaryImpl]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            convert state.expected_potential_afterDirect_le targetOrdinal hashInput event
              horigin htarget using 1
            apply tsum_congr
            intro result
            congr 1
            simpa only [hfresh, if_true] using
              (originTargetMonitoredAdversaryImpl_direct_result_potential
                configuration secretKey targetOrdinal state hashInput result event)
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            convert state.expected_potential_afterDirect_le targetOrdinal hashInput event
              horigin htarget using 1
            apply tsum_congr
            intro result
            congr 1
            simpa only [hfresh, if_false] using
              (originTargetMonitoredAdversaryImpl_direct_result_potential
                configuration secretKey targetOrdinal state hashInput result event)
  | inr request =>
      simp only [originTargetMonitoredAdversaryImpl, StateT.run,
        tsum_probOutput_bind_mul]
      convert state.expected_potential_afterSigner_le targetOrdinal secretKey request event
        q hq hcache horigin htarget using 1
      apply tsum_congr
      intro targetRun
      congr 1
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [tsum_probOutput_pure_mul]
          simpa only [hselection] using
            (originTargetMonitoredAdversaryImpl_signer_result_potential
              configuration secretKey targetOrdinal state request targetRun event)
      | some selection =>
          rcases selection with ⟨input, view⟩
          by_cases hfresh : state.origin.viewed.cache input = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            simpa only [hselection, hfresh, if_true] using
              (originTargetMonitoredAdversaryImpl_signer_result_potential
                configuration secretKey targetOrdinal state request targetRun event)
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            simpa only [hselection, hfresh, if_false] using
              (originTargetMonitoredAdversaryImpl_signer_result_potential
                configuration secretKey targetOrdinal state request targetRun event)

def OriginTargetMonitorState.JointCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration) : Prop :=
  state.origin.ScheduleCoherent ∧ state.TargetScheduleCoherent targetOrdinal

theorem OriginTargetMonitorState.jointCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec)
    (targetOrdinal : Nat) :
    (OriginTargetMonitorState.initial configuration cache).JointCoherent targetOrdinal := by
  exact ⟨OriginMonitorState.scheduleCoherent_initial configuration cache,
    OriginTargetMonitorState.targetScheduleCoherent_initial configuration cache targetOrdinal⟩

theorem originTargetMonitoredAdversaryImpl_query_jointCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.JointCoherent targetOrdinal)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.JointCoherent targetOrdinal := by
  classical
  rcases hcoherent with ⟨horigin, htarget⟩
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horiginMem, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          constructor
          · exact originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey
              (.inl (.inl uniformInput)) state.origin (output, origin) horigin horiginMem
          · simpa [OriginTargetMonitorState.JointCoherent,
              OriginTargetMonitorState.TargetScheduleCoherent,
              OriginTargetMonitorState.advanceOrigin] using htarget
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            constructor
            · exact originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey
                (.inl (.inr hashInput)) state.origin (output, origin) horigin horiginMem
            · exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate
                targetOrdinal (state.advanceOrigin origin) _ _
                  (state.targetScheduleCoherent_advanceOrigin targetOrdinal origin htarget)
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            constructor
            · exact originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey
                (.inl (.inr hashInput)) state.origin (output, origin) horigin horiginMem
            · exact state.targetScheduleCoherent_advanceOrigin targetOrdinal origin htarget
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, htargetRun, hpure⟩ := hmem
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, support_pure, Set.mem_singleton_iff] at hpure
          subst result
          constructor
          · simpa [OriginMonitorState.ScheduleCoherent, OriginMonitorState.afterSigner,
              OriginTargetMonitorState.advanceOrigin] using
              state.origin.scheduleCoherent_afterSigner secretKey request
                (targetSignerResultView targetRun.1, targetRun.2) horigin
          · exact state.targetScheduleCoherent_advanceOrigin targetOrdinal _ htarget
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, hfresh, if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            subst result
            constructor
            · simpa [OriginMonitorState.ScheduleCoherent, OriginMonitorState.afterSigner,
                OriginTargetMonitorState.recordCandidate,
                OriginTargetMonitorState.advanceOrigin] using
                state.origin.scheduleCoherent_afterSigner secretKey request
                  (targetSignerResultView targetRun.1, targetRun.2) horigin
            · exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate
                targetOrdinal _ _ _
                  (state.targetScheduleCoherent_advanceOrigin targetOrdinal _ htarget)
          · simp only [hselection, hfresh, if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            subst result
            constructor
            · simpa [OriginMonitorState.ScheduleCoherent, OriginMonitorState.afterSigner,
                OriginTargetMonitorState.advanceOrigin] using
                state.origin.scheduleCoherent_afterSigner secretKey request
                  (targetSignerResultView targetRun.1, targetRun.2) horigin
            · exact state.targetScheduleCoherent_advanceOrigin targetOrdinal _ htarget

theorem originTargetMonitoredAdversaryImpl_query_cache_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : state.origin.viewed.cache ≤ result.2.origin.viewed.cache := by
  classical
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horiginMem, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact originMonitoredAdversaryImpl_query_cache_le configuration secretKey
            (.inl (.inl uniformInput)) state.origin (output, origin) horiginMem
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            exact originMonitoredAdversaryImpl_query_cache_le configuration secretKey
              (.inl (.inr hashInput)) state.origin (output, origin) horiginMem
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            exact originMonitoredAdversaryImpl_query_cache_le configuration secretKey
              (.inl (.inr hashInput)) state.origin (output, origin) horiginMem
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, htargetRun, hpure⟩ := hmem
      have hle := simulateQ_romImpl_cache_le (signWithTargetView secretKey request)
        state.origin.viewed.cache targetRun htargetRun
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact hle
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, hfresh, if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            subst result
            exact hle
          · simp only [hselection, hfresh, if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            subst result
            exact hle

noncomputable def OriginTargetMonitorState.cappedPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if QueryCache.enncard state.origin.viewed.cache ≤ q then state.potential event else 0

theorem OriginTargetMonitorState.cappedPotential_le_potential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    state.cappedPotential q event ≤ state.potential event := by
  classical
  simp only [OriginTargetMonitorState.cappedPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginTargetMonitorState.cappedPotential_eq_of_enncard_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedPotential q event = state.potential event := by
  simp [OriginTargetMonitorState.cappedPotential, hcache]

theorem OriginTargetMonitorState.cappedPotential_eq_zero_of_not_enncard_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : ¬ QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedPotential q event = 0 := by
  simp [OriginTargetMonitorState.cappedPotential, hcache]

theorem originTargetMonitoredAdversaryImpl_expected_cappedPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : state.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.cappedPotential q event) ≤
      state.cappedPotential q event := by
  classical
  by_cases hcache : QueryCache.enncard state.origin.viewed.cache ≤ q
  · rw [state.cappedPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
              state] * result.2.cappedPotential q event) ≤
          ∑' result,
            Pr[= result |
              (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                state] * result.2.potential event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedPotential_le_potential q event)
      _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_potential_le configuration
        secretKey targetOrdinal input state event q hq hcache hcoherent.1 hcoherent.2
  · rw [state.cappedPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state] * result.2.cappedPotential q event) = 0 := by
      apply ENNReal.tsum_eq_zero.2
      intro result
      by_cases hresult : result ∈ support
          ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state)
      · have hle := originTargetMonitoredAdversaryImpl_query_cache_le configuration
          secretKey targetOrdinal input state result hresult
        have hcard := QueryCache.enncard_mono hle
        have hnotFinal : ¬ QueryCache.enncard result.2.origin.viewed.cache ≤ q :=
          fun hfinal => hcache (hcard.trans hfinal)
        rw [result.2.cappedPotential_eq_zero_of_not_enncard_le q event hnotFinal,
          mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem originTargetMonitoredAdversaryImpl_expected_cappedPotential_simulateQ_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
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
              (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                initialState] *
              ∑' finalResult,
                Pr[= finalResult |
                  (simulateQ
                    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
                    (next result.1)).run result.2] *
                  finalResult.2.cappedPotential q event) ≤
            ∑' result,
              Pr[= result |
                (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                  initialState] * result.2.cappedPotential q event := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support
              ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                initialState)
          · apply mul_le_mul' le_rfl
            exact ih result.1 result.2
              (originTargetMonitoredAdversaryImpl_query_jointCoherent configuration secretKey
                targetOrdinal input initialState result hcoherent hresult)
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_cappedPotential_le
          configuration secretKey targetOrdinal input initialState event q hq hcoherent

def OriginTargetMonitorState.Complete
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration) : Prop :=
  state.valid = true ∧ state.origin.Complete ∧ ∃ target, state.targetView = some target

theorem OriginTargetMonitorState.potential_eq_one_of_complete
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.potential event = 1 := by
  rcases hcomplete with ⟨hvalid, horigin, target, htarget⟩
  simp [OriginTargetMonitorState.potential, hvalid, htarget,
    state.origin.potential_eq_one_of_complete
      (fun views => event (views, target)) horigin (hevent target htarget)]

theorem OriginTargetMonitorState.cappedPotential_eq_one_of_complete
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.cappedPotential q event = 1 := by
  rw [state.cappedPotential_eq_of_enncard_le q event hcache,
    state.potential_eq_one_of_complete event hcomplete hevent]

theorem probEvent_originTargetMonitored_complete_le_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState] ≤ initialState.cappedPotential q event := by
  let run := (simulateQ
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    computation).run initialState
  calc
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedPotential q event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_cappedPotential_simulateQ_le
      configuration secretKey targetOrdinal computation initialState event q hq hcoherent

theorem probEvent_uniform_views_target_eq_sum
    {signatures distinct : Nat} (pattern : FewTimePattern signatures distinct)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
      ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] =
      ∑ target, Pr[fun value : FewTimeView => value = target |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          Pr[fun views => event (views, target) |
            ($ᵗ (pattern.selected → FewTimeView) :
              ProbComp (pattern.selected → FewTimeView))] := by
  classical
  let viewsComp := ($ᵗ (pattern.selected → FewTimeView) :
    ProbComp (pattern.selected → FewTimeView))
  let targetComp := ($ᵗ FewTimeView : ProbComp FewTimeView)
  calc
    _ = Pr[event | do
        let views ← viewsComp
        let target ← targetComp
        pure (views, target)] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalDist_independent_uniform_pair.symm
    _ = Pr[event | do
        let target ← targetComp
        let views ← viewsComp
        pure (views, target)] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      exact OracleComp.DeferredSampling.evalDist_bind_comm viewsComp targetComp
        (fun views target => pure (views, target))
    _ = ∑' target, Pr[= target | targetComp] *
        Pr[fun views => event (views, target) | viewsComp] := by
      rw [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro target
      congr 1
      rw [bind_pure_comp, probEvent_map]
      rfl
    _ = _ := by
      simp only [viewsComp, targetComp, tsum_fintype,
        probEvent_eq_eq_probOutput]

theorem OriginTargetMonitorState.potential_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    (OriginTargetMonitorState.initial configuration cache).potential event =
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
          ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] := by
  classical
  rw [OriginTargetMonitorState.potential]
  simp only [OriginTargetMonitorState.initial, if_true]
  simp_rw [OriginMonitorState.potential_initial]
  rw [probEvent_uniform_views_target_eq_sum pattern event]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  ac_rfl

theorem probEvent_originTargetMonitored_complete_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
          ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] := by
  calc
    _ ≤ (OriginTargetMonitorState.initial configuration initialCache).cappedPotential
        q event :=
      probEvent_originTargetMonitored_complete_le_initial configuration secretKey
        targetOrdinal computation (OriginTargetMonitorState.initial configuration initialCache)
          event q hq
            (OriginTargetMonitorState.jointCoherent_initial configuration initialCache
              targetOrdinal)
    _ = (OriginTargetMonitorState.initial configuration initialCache).potential event :=
      OriginTargetMonitorState.cappedPotential_eq_of_enncard_le q
        (OriginTargetMonitorState.initial configuration initialCache) event hcache
    _ = _ := OriginTargetMonitorState.potential_initial configuration initialCache event

end Concrete

end SphincsSecurity
