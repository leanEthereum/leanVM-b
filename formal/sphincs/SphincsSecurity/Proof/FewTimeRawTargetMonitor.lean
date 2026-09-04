import SphincsSecurity.Proof.FewTimeRawTargetInvariant

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def rawTargetMonitoredAdversaryImpl
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (OriginTargetMonitorState configuration) ProbComp) := by
  intro input
  cases input with
  | inl worldInput =>
      exact fun state => do
        let (output, origin) ←
          ((originMonitoredAdversaryImpl configuration secretKey (.inl worldInput)).run
            state.origin)
        let advanced := state.advanceOrigin origin
        match worldInput with
        | .inl _ => pure (output, advanced)
        | .inr hashInput =>
            if state.origin.viewed.cache hashInput = none then
              pure (output, advanced.recordCandidate targetOrdinal
                (decide (configuration.sourceAt? state.origin.directOrdinal = none ∧
                  signAttemptResultOfOutput output ≠ none))
                (hashOutputFewTimeView output))
            else pure (output, advanced)
  | inr request =>
      exact fun state => do
        let (output, origin) ←
          ((originMonitoredAdversaryImpl configuration secretKey (.inr request)).run
            state.origin)
        pure (output, state.advanceOrigin origin)

theorem rawTargetMonitoredAdversaryImpl_expected_rawPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.rawPotential event) ≤
      state.rawPotential event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          apply state.expected_rawPotential_advanceOrigin_le
          intro target
          exact originMonitoredAdversaryImpl_expected_potential_le configuration secretKey
            (.inl (.inl uniformInput)) state.origin (fun views => event (views, target))
              q hq hcache horigin
      | inr hashInput =>
          simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
            originMonitoredAdversaryImpl]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            have hbound := state.expected_rawPotential_afterRawDirect_le targetOrdinal
              hashInput event horigin htarget
            simp only [OriginTargetMonitorState.afterRawDirect, hfresh, if_true] at hbound
            convert hbound using 1
            apply tsum_congr
            intro result
            congr 1
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            have hbound := state.expected_rawPotential_afterRawDirect_le targetOrdinal
              hashInput event horigin htarget
            simp only [OriginTargetMonitorState.afterRawDirect, hfresh, if_false] at hbound
            convert hbound using 1
            apply tsum_congr
            intro result
            congr 1
  | inr request =>
      simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
        tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      apply state.expected_rawPotential_advanceOrigin_le
      intro target
      exact originMonitoredAdversaryImpl_expected_potential_le configuration secretKey
        (.inr request) state.origin (fun views => event (views, target))
          q hq hcache horigin


theorem rawTargetMonitoredAdversaryImpl_query_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration) :
    (fun result => (result.1, result.2.origin)) <$>
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run state) =
      (originMonitoredAdversaryImpl configuration secretKey input).run state.origin := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp [rawTargetMonitoredAdversaryImpl, StateT.run, map_eq_bind_pure_comp,
            Function.comp_apply, bind_assoc, OriginTargetMonitorState.advanceOrigin]
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none <;>
            simp [rawTargetMonitoredAdversaryImpl, StateT.run, map_eq_bind_pure_comp,
              Function.comp_apply, bind_assoc, hfresh, OriginTargetMonitorState.advanceOrigin,
              OriginTargetMonitorState.recordCandidate]
  | inr request =>
      simp [rawTargetMonitoredAdversaryImpl, StateT.run, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, OriginTargetMonitorState.advanceOrigin]

theorem rawTargetMonitoredAdversaryImpl_query_jointCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.JointCoherent targetOrdinal)
    (hmem : result ∈ support
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.JointCoherent targetOrdinal := by
  classical
  rcases hcoherent with ⟨horigin, htarget⟩
  cases input with
  | inl worldInput =>
      rw [rawTargetMonitoredAdversaryImpl] at hmem
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
      rw [rawTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horiginMem, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      constructor
      · exact originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey
          (.inr request) state.origin (output, origin) horigin horiginMem
      · exact state.targetScheduleCoherent_advanceOrigin targetOrdinal origin htarget

theorem rawTargetMonitoredAdversaryImpl_query_cache_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : state.origin.viewed.cache ≤ result.2.origin.viewed.cache := by
  classical
  cases input with
  | inl worldInput =>
      rw [rawTargetMonitoredAdversaryImpl] at hmem
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
      rw [rawTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horiginMem, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact originMonitoredAdversaryImpl_query_cache_le configuration secretKey
        (.inr request) state.origin (output, origin) horiginMem

theorem rawTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration) :
    Prod.map id OriginTargetMonitorState.origin <$>
        (simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState =
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (originMonitoredAdversaryImpl configuration secretKey)
    OriginTargetMonitorState.origin
  intro input state
  exact rawTargetMonitoredAdversaryImpl_query_projection configuration secretKey
    targetOrdinal input state

theorem probEvent_rawTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : α × OriginMonitorState configuration → Prop) :
    Pr[event |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] =
      Pr[fun result : α × OriginTargetMonitorState configuration =>
          event (result.1, result.2.origin) |
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  rw [← rawTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState, probEvent_map]
  rfl

theorem probEvent_originMonitored_le_rawTargetMonitored
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (originEvent : α × OriginMonitorState configuration → Prop)
    (targetEvent : α × OriginTargetMonitorState configuration → Prop)
    (himp : ∀ result ∈ support
      ((simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState),
      originEvent (result.1, result.2.origin) → targetEvent result) :
    Pr[originEvent |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] ≤
      Pr[targetEvent |
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  classical
  rw [probEvent_rawTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState originEvent]
  exact probEvent_mono himp
theorem rawTargetMonitoredAdversaryImpl_viewed_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration) :
    (fun result => (result.1, result.2.origin.viewed)) <$>
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState =
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed := by
  calc
    _ = Prod.map id OriginMonitorState.viewed <$>
        (Prod.map id OriginTargetMonitorState.origin <$>
          (simulateQ
            (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
            computation).run initialState) := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      rfl
    _ = Prod.map id OriginMonitorState.viewed <$>
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
          computation).run initialState.origin := by
      rw [rawTargetMonitoredAdversaryImpl_projection]
    _ = _ := originMonitoredAdversaryImpl_projection configuration secretKey
      computation initialState.origin

theorem exists_rawTargetMonitored_of_viewed_support
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × ViewedFullTraceState)
    (hmem : result ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed)) :
    ∃ monitored ∈ support
        ((simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState),
      monitored.1 = result.1 ∧ monitored.2.origin.viewed = result.2 := by
  rw [← rawTargetMonitoredAdversaryImpl_viewed_projection configuration secretKey
    targetOrdinal computation initialState, support_map] at hmem
  obtain ⟨monitored, hmonitored, heq⟩ := hmem
  refine ⟨monitored, hmonitored, ?_⟩
  exact Prod.mk.inj heq

theorem probEvent_viewed_le_rawTargetMonitoredAdversaryImpl
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (viewedEvent : α × ViewedFullTraceState → Prop)
    (monitoredEvent : α × OriginTargetMonitorState configuration → Prop)
    (himp : ∀ result ∈ support
      ((simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState),
      viewedEvent (result.1, result.2.origin.viewed) → monitoredEvent result) :
    Pr[viewedEvent |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed] ≤
      Pr[monitoredEvent |
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  classical
  rw [← rawTargetMonitoredAdversaryImpl_viewed_projection configuration secretKey
    targetOrdinal computation initialState, probEvent_map]
  exact probEvent_mono himp

end SphincsSecurity.Concrete
