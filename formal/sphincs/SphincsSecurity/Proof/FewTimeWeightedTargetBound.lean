import SphincsSecurity.Proof.FewTimeWeightedTargetPotential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginTargetMonitorState.cappedRawWeightedPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if QueryCache.enncard state.origin.viewed.cache ≤ q then state.rawWeightedPotential reuseWeight event else 0

theorem OriginTargetMonitorState.cappedRawWeightedPotential_le_rawWeightedPotential {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    state.cappedRawWeightedPotential q reuseWeight event ≤ state.rawWeightedPotential reuseWeight event := by
  classical
  simp only [OriginTargetMonitorState.cappedRawWeightedPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginTargetMonitorState.cappedRawWeightedPotential_eq_of_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedRawWeightedPotential q reuseWeight event = state.rawWeightedPotential reuseWeight event := by
  simp [OriginTargetMonitorState.cappedRawWeightedPotential, hcache]

theorem OriginTargetMonitorState.cappedRawWeightedPotential_eq_zero_of_not_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : ¬ QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedRawWeightedPotential q reuseWeight event = 0 := by
  simp [OriginTargetMonitorState.cappedRawWeightedPotential, hcache]

theorem OriginTargetMonitorState.cappedRawWeightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.cappedRawWeightedPotential q reuseWeight event = 1 := by
  rw [state.cappedRawWeightedPotential_eq_of_enncard_le q event hcache,
    state.rawWeightedPotential_eq_one_of_complete event hcomplete hevent]

theorem rawTargetMonitoredAdversaryImpl_expected_rawWeightedPotential_le
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
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.rawWeightedPotential (digestReuseWeight q) event) ≤
      state.rawWeightedPotential (digestReuseWeight q) event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          apply state.expected_rawWeightedPotential_advanceOrigin_le
          intro target
          exact originMonitoredAdversaryImpl_expected_weightedPotential_le configuration secretKey
            (.inl (.inl uniformInput)) state.origin (fun views => event (views, target))
              q hq hcache horigin
      | inr hashInput =>
          simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
            tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
            originMonitoredAdversaryImpl]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, tsum_probOutput_pure_mul]
            have hbound := state.expected_rawWeightedPotential_afterRawDirect_le
              (reuseWeight := digestReuseWeight q) targetOrdinal
              hashInput event horigin htarget
            simp only [OriginTargetMonitorState.afterRawDirect, hfresh, if_true] at hbound
            convert hbound using 1
            apply tsum_congr
            intro result
            congr 1
          · simp only [hfresh, if_false, tsum_probOutput_pure_mul]
            have hbound := state.expected_rawWeightedPotential_afterRawDirect_le
              (reuseWeight := digestReuseWeight q) targetOrdinal
              hashInput event horigin htarget
            simp only [OriginTargetMonitorState.afterRawDirect, hfresh, if_false] at hbound
            convert hbound using 1
            apply tsum_congr
            intro result
            congr 1
  | inr request =>
      simp only [rawTargetMonitoredAdversaryImpl, StateT.run,
        tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      apply state.expected_rawWeightedPotential_advanceOrigin_le
      intro target
      exact originMonitoredAdversaryImpl_expected_weightedPotential_le configuration secretKey
        (.inr request) state.origin (fun views => event (views, target))
          q hq hcache horigin

theorem rawTargetMonitoredAdversaryImpl_expected_cappedRawWeightedPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : state.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.cappedRawWeightedPotential q (digestReuseWeight q) event) ≤
      state.cappedRawWeightedPotential q (digestReuseWeight q) event := by
  classical
  by_cases hcache : QueryCache.enncard state.origin.viewed.cache ≤ q
  · rw [state.cappedRawWeightedPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
              state] * result.2.cappedRawWeightedPotential q (digestReuseWeight q) event) ≤
          ∑' result,
            Pr[= result |
              (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                state] * result.2.rawWeightedPotential (digestReuseWeight q) event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedRawWeightedPotential_le_rawWeightedPotential q event)
      _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_rawWeightedPotential_le configuration
        secretKey targetOrdinal input state event q hq hcache hcoherent.1 hcoherent.2
  · rw [state.cappedRawWeightedPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state] * result.2.cappedRawWeightedPotential q (digestReuseWeight q) event) = 0 := by
      apply ENNReal.tsum_eq_zero.2
      intro result
      by_cases hresult : result ∈ support
          ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state)
      · have hle := rawTargetMonitoredAdversaryImpl_query_cache_le configuration
          secretKey targetOrdinal input state result hresult
        have hcard := QueryCache.enncard_mono hle
        have hnotFinal : ¬ QueryCache.enncard result.2.origin.viewed.cache ≤ q :=
          fun hfinal => hcache (hcard.trans hfinal)
        rw [result.2.cappedRawWeightedPotential_eq_zero_of_not_enncard_le q event hnotFinal,
          mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem rawTargetMonitoredAdversaryImpl_expected_cappedRawWeightedPotential_simulateQ_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] *
        result.2.cappedRawWeightedPotential q (digestReuseWeight q) event) ≤ initialState.cappedRawWeightedPotential q (digestReuseWeight q) event := by
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
              (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                initialState] *
              ∑' finalResult,
                Pr[= finalResult |
                  (simulateQ
                    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
                    (next result.1)).run result.2] *
                  finalResult.2.cappedRawWeightedPotential q (digestReuseWeight q) event) ≤
            ∑' result,
              Pr[= result |
                (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                  initialState] * result.2.cappedRawWeightedPotential q (digestReuseWeight q) event := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support
              ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                initialState)
          · apply mul_le_mul' le_rfl
            exact ih result.1 result.2
              (rawTargetMonitoredAdversaryImpl_query_jointCoherent configuration secretKey
                targetOrdinal input initialState result hcoherent hresult)
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_cappedRawWeightedPotential_le
          configuration secretKey targetOrdinal input initialState event q hq hcoherent

theorem probEvent_rawTargetMonitored_complete_le_weighted_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState] ≤ initialState.cappedRawWeightedPotential q (digestReuseWeight q) event := by
  let run := (simulateQ
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    computation).run initialState
  calc
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedRawWeightedPotential q (digestReuseWeight q) event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedRawWeightedPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_cappedRawWeightedPotential_simulateQ_le
      configuration secretKey targetOrdinal computation initialState event q hq hcoherent

theorem probEvent_rawTargetMonitored_complete_le_weighted_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * (digestReuseWeight q)) ^ configuration.prehit.card *
          Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]) := by
  calc
    _ ≤ (OriginTargetMonitorState.initial configuration initialCache).cappedRawWeightedPotential
        q (digestReuseWeight q) event :=
      probEvent_rawTargetMonitored_complete_le_weighted_initial configuration secretKey
        targetOrdinal computation (OriginTargetMonitorState.initial configuration initialCache)
          event q hq
            (OriginTargetMonitorState.jointCoherent_initial configuration initialCache
              targetOrdinal)
    _ = (OriginTargetMonitorState.initial configuration initialCache).rawWeightedPotential (digestReuseWeight q) event :=
      OriginTargetMonitorState.cappedRawWeightedPotential_eq_of_enncard_le q
        (OriginTargetMonitorState.initial configuration initialCache) event hcache
    _ = _ := OriginTargetMonitorState.rawWeightedPotential_initial configuration initialCache event

end SphincsSecurity.Concrete
