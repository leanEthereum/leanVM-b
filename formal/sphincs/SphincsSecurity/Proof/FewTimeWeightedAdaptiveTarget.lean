import SphincsSecurity.Proof.FewTimeWeightedTargetPotential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem OriginTargetMonitorState.weightedPotential_eq_zero_of_invalid {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hinvalid : state.valid = false) : state.weightedPotential reuseWeight event = 0 := by
  simp [OriginTargetMonitorState.weightedPotential, hinvalid]

theorem OriginTargetMonitorState.weightedPotential_recordCandidate_of_ordinal_ne {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.recordCandidate targetOrdinal allowed view).weightedPotential reuseWeight event =
      state.weightedPotential reuseWeight event := by
  simp [OriginTargetMonitorState.recordCandidate, OriginTargetMonitorState.weightedPotential, hne]

theorem OriginTargetMonitorState.weightedPotential_recordCandidate_eq_of_disallowed {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (view : FewTimeView)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (heq : state.candidateOrdinal = targetOrdinal) :
    (state.recordCandidate targetOrdinal false view).weightedPotential reuseWeight event = 0 := by
  simp [OriginTargetMonitorState.recordCandidate, OriginTargetMonitorState.weightedPotential, heq]

theorem OriginTargetMonitorState.weightedPotential_afterDirect_of_ordinal_ne {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterDirect targetOrdinal input output).weightedPotential reuseWeight event =
      (state.advanceOrigin (state.origin.afterDirect input output)).weightedPotential reuseWeight event := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [OriginTargetMonitorState.afterDirect, hfresh, if_true]
    exact OriginTargetMonitorState.weightedPotential_recordCandidate_of_ordinal_ne
      targetOrdinal _ _ _ event hne
  · simp [OriginTargetMonitorState.afterDirect, hfresh]

theorem OriginTargetMonitorState.weightedPotential_advanceOrigin_congr {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (left right : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcongr : ∀ target,
      left.weightedPotential reuseWeight (fun views => event (views, target)) =
        right.weightedPotential reuseWeight (fun views => event (views, target))) :
    (state.advanceOrigin left).weightedPotential reuseWeight event =
      (state.advanceOrigin right).weightedPotential reuseWeight event := by
  classical
  simp only [OriginTargetMonitorState.advanceOrigin,
    OriginTargetMonitorState.weightedPotential]
  split
  · cases state.targetView with
    | none => simp_rw [hcongr]
    | some target => exact hcongr target
  · rfl

theorem OriginTargetMonitorState.weightedPotential_recordCandidate_advanceOrigin_congr {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (left right : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcongr : ∀ target,
      left.weightedPotential reuseWeight (fun views => event (views, target)) =
        right.weightedPotential reuseWeight (fun views => event (views, target))) :
    ((state.advanceOrigin left).recordCandidate targetOrdinal allowed view).weightedPotential reuseWeight event =
      ((state.advanceOrigin right).recordCandidate targetOrdinal allowed view).weightedPotential reuseWeight event := by
  classical
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · cases hstate : state.valid <;> cases hallowed : allowed <;>
      simp [OriginTargetMonitorState.recordCandidate,
        OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.weightedPotential,
        heq, hstate, hcongr]
  · by_cases hvalid : state.valid = true
    · cases htarget : state.targetView with
      | none =>
          simp [OriginTargetMonitorState.recordCandidate,
            OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.weightedPotential,
            heq, hvalid, htarget]
          simp_rw [hcongr]
      | some target =>
          simpa [OriginTargetMonitorState.recordCandidate,
            OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.weightedPotential,
            heq, hvalid, htarget] using hcongr target
    · simp [OriginTargetMonitorState.recordCandidate,
        OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.weightedPotential,
        heq, hvalid]

theorem OriginTargetMonitorState.weightedPotential_afterSigner_of_ordinal_ne {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (targetRun : TargetSignerResult × QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential reuseWeight event =
      (state.advanceOrigin (state.origin.afterSigner secretKey request
        (targetSignerResultView targetRun.1, targetRun.2))).weightedPotential reuseWeight event := by
  cases hselection : targetRun.1.2 with
  | none => simp [OriginTargetMonitorState.afterSigner, hselection]
  | some selection =>
      rcases selection with ⟨input, view⟩
      by_cases hfresh : state.origin.viewed.cache input = none
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_true]
        exact OriginTargetMonitorState.weightedPotential_recordCandidate_of_ordinal_ne
          targetOrdinal _ _ _ event hne
      · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh]

theorem OriginMonitorState.expected_weightedPotential_afterTargetSigner_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (request : SignRequest)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcoherent : state.ScheduleCoherent) :
    (∑' targetRun,
      Pr[= targetRun |
        (simulateQ romImpl (signWithTargetView secretKey request)).run state.viewed.cache] *
        (state.afterSigner secretKey request
          (targetSignerResultView targetRun.1, targetRun.2)).weightedPotential (digestReuseWeight q) event) ≤
      state.weightedPotential (digestReuseWeight q) event := by
  calc
    _ = ∑' signerRun,
        Pr[= signerRun |
          (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
          (state.afterSigner secretKey request signerRun).weightedPotential (digestReuseWeight q) event := by
      rw [← simulateQ_signWithTargetView_projection_run]
      rw [tsum_probOutput_map_mul]
    _ ≤ _ := state.expected_weightedPotential_afterSigner_le secretKey request event
      (fun target P => probEvent_signWithView_fixedPrehit_le_digestReuseWeight
        secretKey request state.viewed.cache target P q hq hcache) hcoherent

theorem OriginTargetMonitorState.expected_weightedPotential_afterDirect_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result, Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
      (state.afterDirect targetOrdinal input result.1).weightedPotential reuseWeight event) ≤
      state.weightedPotential reuseWeight event := by
  classical
  by_cases hfresh : state.origin.viewed.cache input = none
  · by_cases heq : state.candidateOrdinal = targetOrdinal
    · cases hsource : configuration.sourceAt? state.origin.directOrdinal with
      | some selected =>
          have hzero : ∀ output,
              (state.afterDirect targetOrdinal input output).weightedPotential reuseWeight event = 0 := by
            intro output
            rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
            rw [show decide
              (configuration.sourceAt? state.origin.directOrdinal = none) = false by
                simp [hsource]]
            apply OriginTargetMonitorState.weightedPotential_recordCandidate_eq_of_disallowed
            simpa [OriginTargetMonitorState.advanceOrigin] using heq
          simp_rw [hzero]
          simp
      | none =>
          cases hvalid : state.valid with
          | false =>
              have hzero : ∀ output,
                  (state.afterDirect targetOrdinal input output).weightedPotential reuseWeight event = 0 := by
                intro output
                rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
                apply OriginTargetMonitorState.weightedPotential_eq_zero_of_invalid
                simp [OriginTargetMonitorState.recordCandidate,
                  OriginTargetMonitorState.advanceOrigin, heq, hvalid]
              simp_rw [hzero]
              simp [OriginTargetMonitorState.weightedPotential, hvalid]
          | true =>
              have htargetView : state.targetView = none :=
                state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
              calc
                (∑' result,
                    Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
                      (state.afterDirect targetOrdinal input result.1).weightedPotential reuseWeight event) ≤
                    ∑ target, Pr[fun value : FewTimeView => value = target |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        state.origin.weightedPotential reuseWeight (fun views => event (views, target)) := by
                  apply tsum_probOutput_randomOracle_fresh_view_mul_le_expected
                    input state.origin.viewed.cache hfresh
                  intro result _
                  simp [OriginTargetMonitorState.afterDirect, hfresh, hsource,
                    OriginTargetMonitorState.recordCandidate,
                    OriginTargetMonitorState.advanceOrigin,
                    OriginTargetMonitorState.weightedPotential, heq, hvalid,
                    state.origin.weightedPotential_afterDirect_of_sourceAt?_eq_none
                      input result.1 _ hsource]
                _ = state.weightedPotential reuseWeight event := by
                  simp [OriginTargetMonitorState.weightedPotential, hvalid, htargetView]
    · simp_rw [state.weightedPotential_afterDirect_of_ordinal_ne targetOrdinal input _ event heq]
      apply state.expected_weightedPotential_advanceOrigin_le
      intro target
      exact state.origin.expected_weightedPotential_afterDirect_le input
        (fun views => event (views, target)) horigin
  · simp_rw [OriginTargetMonitorState.afterDirect, hfresh, if_false]
    apply state.expected_weightedPotential_advanceOrigin_le
    intro target
    exact state.origin.expected_weightedPotential_afterDirect_le input
      (fun views => event (views, target)) horigin

theorem OriginTargetMonitorState.expected_weightedPotential_afterSigner_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (secretKey : SecretKey) (request : SignRequest)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' targetRun,
      Pr[= targetRun |
        (simulateQ romImpl (signWithTargetView secretKey request)).run
          state.origin.viewed.cache] *
        (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential (digestReuseWeight q) event) ≤
      state.weightedPotential (digestReuseWeight q) event := by
  classical
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · cases hselected : pattern.selectedAt? state.origin.signerOrdinal with
    | some selected =>
        calc
          (∑' targetRun,
              Pr[= targetRun |
                (simulateQ romImpl (signWithTargetView secretKey request)).run
                  state.origin.viewed.cache] *
                (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential (digestReuseWeight q)
                  event) ≤
              ∑' targetRun,
                Pr[= targetRun |
                  (simulateQ romImpl (signWithTargetView secretKey request)).run
                    state.origin.viewed.cache] *
                  (state.advanceOrigin (state.origin.afterSigner secretKey request
                    (targetSignerResultView targetRun.1, targetRun.2))).weightedPotential (digestReuseWeight q) event := by
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
                  rw [OriginTargetMonitorState.weightedPotential_recordCandidate_eq_of_disallowed]
                  · exact zero_le
                  · simpa [OriginTargetMonitorState.advanceOrigin] using heq
                · simp [OriginTargetMonitorState.afterSigner, hselection, hfresh]
          _ ≤ state.weightedPotential (digestReuseWeight q) event := by
            apply state.expected_weightedPotential_advanceOrigin_le
            intro target
            exact state.origin.expected_weightedPotential_afterTargetSigner_le secretKey request
              (fun views => event (views, target)) q hq hcache horigin
    | none =>
        cases hvalid : state.valid with
        | false =>
            have hzero : ∀ targetRun,
                (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential (digestReuseWeight q)
                  event = 0 := by
              intro targetRun
              apply OriginTargetMonitorState.weightedPotential_eq_zero_of_invalid
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
            simp [OriginTargetMonitorState.weightedPotential, hvalid]
        | true =>
            have htargetView : state.targetView = none :=
              state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
            rw [OriginTargetMonitorState.weightedPotential, if_pos hvalid, htargetView]
            let signerCost := fun targetRun : TargetSignerResult × QueryCache HashSpec =>
              (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential (digestReuseWeight q) event
            let signerRisk := fun target : FewTimeView =>
              state.origin.weightedPotential (digestReuseWeight q) (fun views => event (views, target))
            refine tsum_probOutput_signWithTargetView_completed_le_expected
              secretKey request state.origin.viewed.cache signerCost signerRisk ?_ ?_
            · intro targetRun _hsupport hnone
              dsimp only [signerCost, signerRisk]
              cases hselection : targetRun.1.2 with
              | none =>
                  simp [OriginTargetMonitorState.afterSigner, hselection,
                    OriginTargetMonitorState.weightedPotential,
                    OriginTargetMonitorState.advanceOrigin, hvalid, htargetView,
                    state.origin.weightedPotential_afterSigner_of_selectedAt?_eq_none
                      secretKey request
                        (targetSignerResultView targetRun.1, targetRun.2) _ hselected]
              | some selection =>
                  rcases selection with ⟨input, view⟩
                  have hfresh : state.origin.viewed.cache input ≠ none := by
                    simpa [freshTargetSignerView?, hselection] using hnone
                  simp [OriginTargetMonitorState.afterSigner, hselection, hfresh,
                    OriginTargetMonitorState.weightedPotential,
                    OriginTargetMonitorState.advanceOrigin, hvalid, htargetView,
                    state.origin.weightedPotential_afterSigner_of_selectedAt?_eq_none
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
                    OriginTargetMonitorState.weightedPotential, heq, hvalid, hselected,
                    state.origin.weightedPotential_afterSigner_of_selectedAt?_eq_none
                      secretKey request
                        (targetSignerResultView targetRun.1, targetRun.2) _ hselected]
  · simp_rw [state.weightedPotential_afterSigner_of_ordinal_ne targetOrdinal secretKey request _
      event heq]
    apply state.expected_weightedPotential_advanceOrigin_le
    intro target
    exact state.origin.expected_weightedPotential_afterTargetSigner_le secretKey request
      (fun views => event (views, target)) q hq hcache horigin

theorem originTargetMonitoredAdversaryImpl_direct_result_weightedPotential {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (_secretKey : SecretKey)
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
    else advanced).weightedPotential reuseWeight event =
      (state.afterDirect targetOrdinal input result.1).weightedPotential reuseWeight event := by
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
          OriginMonitorState configuration).weightedPotential reuseWeight
          (fun views => event (views, target)) =
        (state.origin.afterDirect input result.1).weightedPotential reuseWeight
          (fun views => event (views, target)) := by
    intro target
    rfl
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [hfresh, if_true, OriginTargetMonitorState.afterDirect]
    exact OriginTargetMonitorState.weightedPotential_recordCandidate_advanceOrigin_congr
      targetOrdinal state _ _ _ _ event horigin
  · simp only [hfresh, if_false, OriginTargetMonitorState.afterDirect]
    exact state.weightedPotential_advanceOrigin_congr _ _ event horigin

theorem originTargetMonitoredAdversaryImpl_signer_result_weightedPotential {reuseWeight : ℝ≥0∞}
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
        else advanced).weightedPotential reuseWeight event =
      (state.afterSigner targetOrdinal secretKey request targetRun).weightedPotential reuseWeight event := by
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
          OriginMonitorState configuration).weightedPotential reuseWeight
          (fun views => event (views, target)) =
        (state.origin.afterSigner secretKey request
          (targetSignerResultView targetRun.1, targetRun.2)).weightedPotential reuseWeight
            (fun views => event (views, target)) := by
    intro target
    exact originMonitoredAdversaryImpl_signer_result_weightedPotential configuration secretKey
      state.origin request (targetSignerResultView targetRun.1, targetRun.2)
        (fun views => event (views, target))
  cases hselection : targetRun.1.2 with
  | none =>
      simp only [OriginTargetMonitorState.afterSigner, hselection]
      exact state.weightedPotential_advanceOrigin_congr _ _ event horigin
  | some selection =>
      rcases selection with ⟨input, view⟩
      by_cases hfresh : state.origin.viewed.cache input = none
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_true]
        exact OriginTargetMonitorState.weightedPotential_recordCandidate_advanceOrigin_congr
          targetOrdinal state _ view _ _ event horigin
      · simp only [OriginTargetMonitorState.afterSigner, hselection, hfresh, if_false]
        exact state.weightedPotential_advanceOrigin_congr _ _ event horigin

theorem originTargetMonitoredAdversaryImpl_expected_weightedPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.weightedPotential (digestReuseWeight q) event) ≤
      state.weightedPotential (digestReuseWeight q) event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [originTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          apply state.expected_weightedPotential_advanceOrigin_le
          intro target
          exact originMonitoredAdversaryImpl_expected_weightedPotential_le configuration secretKey
            (.inl (.inl uniformInput)) state.origin (fun views => event (views, target))
              q hq hcache horigin
      | inr hashInput =>
          simp only [originTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
            originMonitoredAdversaryImpl]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            convert state.expected_weightedPotential_afterDirect_le targetOrdinal hashInput event
              horigin htarget using 1
            apply tsum_congr
            intro result
            congr 1
            simpa only [hfresh, if_true] using
              (originTargetMonitoredAdversaryImpl_direct_result_weightedPotential
                configuration secretKey targetOrdinal state hashInput result event)
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            convert state.expected_weightedPotential_afterDirect_le targetOrdinal hashInput event
              horigin htarget using 1
            apply tsum_congr
            intro result
            congr 1
            simpa only [hfresh, if_false] using
              (originTargetMonitoredAdversaryImpl_direct_result_weightedPotential
                configuration secretKey targetOrdinal state hashInput result event)
  | inr request =>
      simp only [originTargetMonitoredAdversaryImpl, StateT.run,
        tsum_probOutput_bind_mul]
      convert state.expected_weightedPotential_afterSigner_le targetOrdinal secretKey request event
        q hq hcache horigin htarget using 1
      apply tsum_congr
      intro targetRun
      congr 1
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [tsum_probOutput_pure_mul]
          simpa only [hselection] using
            (originTargetMonitoredAdversaryImpl_signer_result_weightedPotential
              configuration secretKey targetOrdinal state request targetRun event)
      | some selection =>
          rcases selection with ⟨input, view⟩
          by_cases hfresh : state.origin.viewed.cache input = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            simpa only [hselection, hfresh, if_true] using
              (originTargetMonitoredAdversaryImpl_signer_result_weightedPotential
                configuration secretKey targetOrdinal state request targetRun event)
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            simpa only [hselection, hfresh, if_false] using
              (originTargetMonitoredAdversaryImpl_signer_result_weightedPotential
                configuration secretKey targetOrdinal state request targetRun event)

end SphincsSecurity.Concrete
