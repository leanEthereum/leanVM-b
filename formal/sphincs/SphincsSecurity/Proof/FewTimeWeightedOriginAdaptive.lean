import SphincsSecurity.Proof.FewTimeWeightedOriginInvariant

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem originMonitoredAdversaryImpl_signer_result_weightedPotential {reuseWeight : ℝ≥0∞}
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
        OriginMonitorState configuration).weightedPotential reuseWeight event =
      (state.afterSigner secretKey request result).weightedPotential reuseWeight event := by
  rfl

noncomputable def OriginMonitorState.cappedWeightedPotential {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) → Prop) : ℝ≥0∞ := by
  classical
  exact if QueryCache.enncard state.viewed.cache ≤ q then state.weightedPotential reuseWeight event else 0

theorem OriginMonitorState.cappedWeightedPotential_le_weightedPotential {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) :
    state.cappedWeightedPotential q reuseWeight event ≤ state.weightedPotential reuseWeight event := by
  classical
  simp only [OriginMonitorState.cappedWeightedPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginMonitorState.cappedWeightedPotential_eq_of_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q) :
    state.cappedWeightedPotential q reuseWeight event = state.weightedPotential reuseWeight event := by
  classical
  simp [OriginMonitorState.cappedWeightedPotential, hcache]

theorem OriginMonitorState.cappedWeightedPotential_eq_zero_of_not_enncard_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : ¬ QueryCache.enncard state.viewed.cache ≤ q) :
    state.cappedWeightedPotential q reuseWeight event = 0 := by
  classical
  simp [OriginMonitorState.cappedWeightedPotential, hcache]

theorem OriginMonitorState.weightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcomplete : state.Complete) (hevent : event state.observation.views) :
    state.weightedPotential reuseWeight event = 1 := by
  classical
  obtain ⟨hvalid, hsources, hreuses, hviews⟩ := hcomplete
  rw [OriginMonitorState.weightedPotential, if_pos hvalid, hsources, hreuses]
  simp only [Finset.card_empty, pow_zero, one_mul]
  exact state.completionMass_eq_one_of_complete event hviews hevent

theorem OriginMonitorState.cappedWeightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcomplete : state.Complete) (hevent : event state.observation.views) :
    state.cappedWeightedPotential q reuseWeight event = 1 := by
  rw [state.cappedWeightedPotential_eq_of_enncard_le q event hcache,
    state.weightedPotential_eq_one_of_complete event hcomplete hevent]

theorem originMonitoredAdversaryImpl_expected_weightedPotential_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard state.viewed.cache ≤ q)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result | (originMonitoredAdversaryImpl configuration secretKey input).run state] *
        result.2.weightedPotential (digestReuseWeight q) event) ≤ state.weightedPotential (digestReuseWeight q) event := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
            tsum_probOutput_pure_mul]
          change (∑' result,
            Pr[= result | (romImpl (.inl uniformInput)).run state.viewed.cache] *
              state.weightedPotential (digestReuseWeight q) event) ≤ state.weightedPotential (digestReuseWeight q) event
          rw [ENNReal.tsum_mul_right]
          calc
            _ ≤ 1 * state.weightedPotential (digestReuseWeight q) event := by
              gcongr
              exact tsum_probOutput_le_one
            _ = _ := one_mul _
      | inr hashInput =>
          simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
            tsum_probOutput_pure_mul]
          change (∑' result,
            Pr[= result | (randomOracle hashInput).run state.viewed.cache] *
              (state.afterDirect hashInput result.1).weightedPotential (digestReuseWeight q) event) ≤ _
          exact state.expected_weightedPotential_afterDirect_le hashInput event hcoherent
  | inr request =>
      simp only [originMonitoredAdversaryImpl, StateT.run, tsum_probOutput_bind_mul,
        tsum_probOutput_pure_mul]
      simp_rw [originMonitoredAdversaryImpl_signer_result_weightedPotential]
      change (∑' result,
        Pr[= result |
          (simulateQ romImpl (signWithView secretKey request)).run state.viewed.cache] *
            (state.afterSigner secretKey request result).weightedPotential (digestReuseWeight q) event) ≤ _
      exact state.expected_weightedPotential_afterSigner_le secretKey request event
        (fun target P => probEvent_signWithView_fixedPrehit_le_digestReuseWeight
          secretKey request state.viewed.cache target P q hq hcache) hcoherent

theorem originMonitoredAdversaryImpl_expected_cappedWeightedPotential_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : state.ScheduleCoherent) :
    (∑' result,
      Pr[= result | (originMonitoredAdversaryImpl configuration secretKey input).run state] *
        result.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤ state.cappedWeightedPotential q (digestReuseWeight q) event := by
  classical
  by_cases hcache : QueryCache.enncard state.viewed.cache ≤ q
  · rw [state.cappedWeightedPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (originMonitoredAdversaryImpl configuration secretKey input).run state] *
            result.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤
          ∑' result,
            Pr[= result |
              (originMonitoredAdversaryImpl configuration secretKey input).run state] *
              result.2.weightedPotential (digestReuseWeight q) event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedWeightedPotential_le_weightedPotential q event)
      _ ≤ _ := originMonitoredAdversaryImpl_expected_weightedPotential_le configuration secretKey input
        state event q hq hcache hcoherent
  · rw [state.cappedWeightedPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (originMonitoredAdversaryImpl configuration secretKey input).run state] *
          result.2.cappedWeightedPotential q (digestReuseWeight q) event) = 0 := by
      apply ENNReal.tsum_eq_zero.2
      intro result
      by_cases hresult : result ∈ support
          ((originMonitoredAdversaryImpl configuration secretKey input).run state)
      · have hle := originMonitoredAdversaryImpl_query_cache_le configuration secretKey input
          state result hresult
        have hcard := QueryCache.enncard_mono hle
        have hnotFinal : ¬ QueryCache.enncard result.2.viewed.cache ≤ q := fun hfinal =>
          hcache (hcard.trans hfinal)
        rw [result.2.cappedWeightedPotential_eq_zero_of_not_enncard_le q event hnotFinal, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem originMonitoredAdversaryImpl_expected_cappedWeightedPotential_simulateQ_le
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : initialState.ScheduleCoherent) :
    (∑' result,
      Pr[= result |
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
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
              (originMonitoredAdversaryImpl configuration secretKey input).run initialState] *
              ∑' finalResult,
                Pr[= finalResult |
                  (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
                    (next result.1)).run result.2] *
                  finalResult.2.cappedWeightedPotential q (digestReuseWeight q) event) ≤
            ∑' result,
              Pr[= result |
                (originMonitoredAdversaryImpl configuration secretKey input).run initialState] *
                result.2.cappedWeightedPotential q (digestReuseWeight q) event := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support
              ((originMonitoredAdversaryImpl configuration secretKey input).run initialState)
          · apply mul_le_mul' le_rfl
            exact ih result.1 result.2
              (originMonitoredAdversaryImpl_query_scheduleCoherent configuration secretKey input
                initialState result hcoherent hresult)
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ ≤ _ := originMonitoredAdversaryImpl_expected_cappedWeightedPotential_le configuration
          secretKey input initialState event q hq hcoherent

theorem probEvent_originMonitored_complete_le_weighted_initial
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcoherent : initialState.ScheduleCoherent) :
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState] ≤ initialState.cappedWeightedPotential q (digestReuseWeight q) event := by
  let run := (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
    computation).run initialState
  calc
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedWeightedPotential q (digestReuseWeight q) event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedWeightedPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := originMonitoredAdversaryImpl_expected_cappedWeightedPotential_simulateQ_le
      configuration secretKey computation initialState event q hq hcoherent

theorem probEvent_originMonitored_complete_le_weighted_ideal
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginMonitorState configuration =>
        result.2.Complete ∧ event result.2.observation.views ∧
          QueryCache.enncard result.2.viewed.cache ≤ q |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run (OriginMonitorState.initial configuration initialCache)] ≤
      (((2 ^ randomnessBits : Nat) : ℝ≥0∞) - (q + digestAttemptLimit : Nat))⁻¹ ^
          configuration.prehit.card *
        Pr[event | ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))] := by
  calc
    _ ≤ (OriginMonitorState.initial configuration initialCache).cappedWeightedPotential q (digestReuseWeight q) event :=
      probEvent_originMonitored_complete_le_weighted_initial configuration secretKey computation
        (OriginMonitorState.initial configuration initialCache) event q hq
        (OriginMonitorState.scheduleCoherent_initial configuration initialCache)
    _ = (OriginMonitorState.initial configuration initialCache).weightedPotential (digestReuseWeight q) event :=
      (OriginMonitorState.initial configuration initialCache).cappedWeightedPotential_eq_of_enncard_le
        q event hcache
    _ = _ := by
      rw [OriginMonitorState.weightedPotential_initial, digestReuseWeight_source]

end Concrete

end SphincsSecurity
