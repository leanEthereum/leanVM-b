import SphincsSecurity.Proof.FewTimeWeightedAdaptiveTarget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginTargetMonitorState.cappedWeightedPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if QueryCache.enncard state.origin.viewed.cache ≤ q then state.weightedPotential reuseWeight event else 0

theorem OriginTargetMonitorState.cappedWeightedPotential_le_weightedPotential {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    state.cappedWeightedPotential q reuseWeight event ≤ state.weightedPotential reuseWeight event := by
  classical
  simp only [OriginTargetMonitorState.cappedWeightedPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginTargetMonitorState.cappedWeightedPotential_eq_of_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedWeightedPotential q reuseWeight event = state.weightedPotential reuseWeight event := by
  simp [OriginTargetMonitorState.cappedWeightedPotential, hcache]

theorem OriginTargetMonitorState.cappedWeightedPotential_eq_zero_of_not_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : ¬ QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedWeightedPotential q reuseWeight event = 0 := by
  simp [OriginTargetMonitorState.cappedWeightedPotential, hcache]

theorem OriginTargetMonitorState.cappedWeightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.cappedWeightedPotential q reuseWeight event = 1 := by
  rw [state.cappedWeightedPotential_eq_of_enncard_le q event hcache,
    state.weightedPotential_eq_one_of_complete event hcomplete hevent]

theorem originTargetMonitoredAdversaryImpl_expected_cappedWeightedPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : state.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤
      state.cappedWeightedPotential q (digestReuseWeight q) event := by
  classical
  by_cases hcache : QueryCache.enncard state.origin.viewed.cache ≤ q
  · rw [state.cappedWeightedPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
              state] * result.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤
          ∑' result,
            Pr[= result |
              (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                state] * result.2.weightedPotential (digestReuseWeight q) event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedWeightedPotential_le_weightedPotential q event)
      _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_weightedPotential_le configuration
        secretKey targetOrdinal input state event q hq hcache hcoherent.1 hcoherent.2
  · rw [state.cappedWeightedPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state] * result.2.cappedWeightedPotential q (digestReuseWeight q) event) = 0 := by
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
        rw [result.2.cappedWeightedPotential_eq_zero_of_not_enncard_le q event hnotFinal,
          mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem originTargetMonitoredAdversaryImpl_expected_cappedWeightedPotential_simulateQ_le
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
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] *
        result.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤ initialState.cappedWeightedPotential q (digestReuseWeight q) event := by
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
                  finalResult.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤
            ∑' result,
              Pr[= result |
                (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                  initialState] * result.2.cappedWeightedPotential q (digestReuseWeight q) event := by
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
        _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_cappedWeightedPotential_le
          configuration secretKey targetOrdinal input initialState event q hq hcoherent

theorem probEvent_originTargetMonitored_complete_le_weighted_initial
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
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState] ≤ initialState.cappedWeightedPotential q (digestReuseWeight q) event := by
  let run := (simulateQ
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    computation).run initialState
  calc
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedWeightedPotential q (digestReuseWeight q) event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedWeightedPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := originTargetMonitoredAdversaryImpl_expected_cappedWeightedPotential_simulateQ_le
      configuration secretKey targetOrdinal computation initialState event q hq hcoherent

theorem probEvent_originTargetMonitored_complete_le_weighted_ideal
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
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ^ configuration.prehit.card *
        Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)] := by
  calc
    _ ≤ (OriginTargetMonitorState.initial configuration initialCache).cappedWeightedPotential
        q (digestReuseWeight q) event :=
      probEvent_originTargetMonitored_complete_le_weighted_initial configuration secretKey
        targetOrdinal computation (OriginTargetMonitorState.initial configuration initialCache)
          event q hq
            (OriginTargetMonitorState.jointCoherent_initial configuration initialCache
              targetOrdinal)
    _ = (OriginTargetMonitorState.initial configuration initialCache).weightedPotential (digestReuseWeight q) event :=
      OriginTargetMonitorState.cappedWeightedPotential_eq_of_enncard_le q
        (OriginTargetMonitorState.initial configuration initialCache) event hcache
    _ = _ := OriginTargetMonitorState.weightedPotential_initial configuration initialCache event

end SphincsSecurity.Concrete
