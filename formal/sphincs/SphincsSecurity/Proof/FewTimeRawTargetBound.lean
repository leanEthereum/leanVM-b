import SphincsSecurity.Proof.FewTimeRawTargetMonitor
import SphincsSecurity.Proof.FewTimeTargetTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem OriginTargetMonitorState.rawPotential_eq_one_of_complete
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.rawPotential event = 1 := by
  obtain ⟨target, htarget⟩ := hcomplete.2.2
  simp only [rawPotential, htarget, reduceCtorEq, ↓reduceIte, one_mul]
  exact state.potential_eq_one_of_complete event hcomplete hevent

noncomputable def OriginTargetMonitorState.cappedRawPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if QueryCache.enncard state.origin.viewed.cache ≤ q then state.rawPotential event else 0

theorem OriginTargetMonitorState.cappedRawPotential_le_rawPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    state.cappedRawPotential q event ≤ state.rawPotential event := by
  classical
  simp only [OriginTargetMonitorState.cappedRawPotential]
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem OriginTargetMonitorState.cappedRawPotential_eq_of_enncard_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedRawPotential q event = state.rawPotential event := by
  simp [OriginTargetMonitorState.cappedRawPotential, hcache]

theorem OriginTargetMonitorState.cappedRawPotential_eq_zero_of_not_enncard_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : ¬ QueryCache.enncard state.origin.viewed.cache ≤ q) :
    state.cappedRawPotential q event = 0 := by
  simp [OriginTargetMonitorState.cappedRawPotential, hcache]

theorem rawTargetMonitoredAdversaryImpl_expected_cappedRawPotential_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcoherent : state.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state] * result.2.cappedRawPotential q event) ≤
      state.cappedRawPotential q event := by
  classical
  by_cases hcache : QueryCache.enncard state.origin.viewed.cache ≤ q
  · rw [state.cappedRawPotential_eq_of_enncard_le q event hcache]
    calc
      (∑' result,
          Pr[= result |
            (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
              state] * result.2.cappedRawPotential q event) ≤
          ∑' result,
            Pr[= result |
              (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                state] * result.2.rawPotential event := by
        apply ENNReal.tsum_le_tsum
        intro result
        exact mul_le_mul' le_rfl (result.2.cappedRawPotential_le_rawPotential q event)
      _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_rawPotential_le configuration
        secretKey targetOrdinal input state event q hq hcache hcoherent.1 hcoherent.2
  · rw [state.cappedRawPotential_eq_zero_of_not_enncard_le q event hcache]
    have hzero : (∑' result,
        Pr[= result |
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
            state] * result.2.cappedRawPotential q event) = 0 := by
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
        rw [result.2.cappedRawPotential_eq_zero_of_not_enncard_le q event hnotFinal,
          mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    exact hzero.le

theorem rawTargetMonitoredAdversaryImpl_expected_cappedRawPotential_simulateQ_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    (∑' result,
      Pr[= result |
        (simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] *
        result.2.cappedRawPotential q event) ≤ initialState.cappedRawPotential q event := by
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
                  finalResult.2.cappedRawPotential q event) ≤
            ∑' result,
              Pr[= result |
                (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
                  initialState] * result.2.cappedRawPotential q event := by
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
        _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_cappedRawPotential_le
          configuration secretKey targetOrdinal input initialState event q hq hcoherent

theorem OriginTargetMonitorState.cappedRawPotential_eq_one_of_complete
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (q : Nat) (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.cappedRawPotential q event = 1 := by
  rw [state.cappedRawPotential_eq_of_enncard_le q event hcache,
    state.rawPotential_eq_one_of_complete event hcomplete hevent]

theorem probEvent_rawTargetMonitored_complete_le_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcoherent : initialState.JointCoherent targetOrdinal) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState] ≤ initialState.cappedRawPotential q event := by
  let run := (simulateQ
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    computation).run initialState
  calc
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            event (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q | run] ≤
        ∑' result, Pr[= result | run] * result.2.cappedRawPotential q event := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hresult
      rw [result.2.cappedRawPotential_eq_one_of_complete q event hresult.2.2
        hresult.1 hresult.2.1]
    _ ≤ _ := rawTargetMonitoredAdversaryImpl_expected_cappedRawPotential_simulateQ_le
      configuration secretKey targetOrdinal computation initialState event q hq hcoherent

theorem OriginTargetMonitorState.rawPotential_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    (OriginTargetMonitorState.initial configuration cache).rawPotential event =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
          Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]) := by
  rw [rawPotential, potential_initial]
  simp only [initial, ↓reduceIte]

theorem probEvent_rawTargetMonitored_complete_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
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
        (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
          Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]) := by
  calc
    _ ≤ (OriginTargetMonitorState.initial configuration initialCache).cappedRawPotential
        q event :=
      probEvent_rawTargetMonitored_complete_le_initial configuration secretKey
        targetOrdinal computation (OriginTargetMonitorState.initial configuration initialCache)
          event q hq
            (OriginTargetMonitorState.jointCoherent_initial configuration initialCache
              targetOrdinal)
    _ = (OriginTargetMonitorState.initial configuration initialCache).rawPotential event :=
      OriginTargetMonitorState.cappedRawPotential_eq_of_enncard_le q
        (OriginTargetMonitorState.initial configuration initialCache) event hcache
    _ = _ := OriginTargetMonitorState.rawPotential_initial configuration initialCache event
theorem probEvent_rawTargetMonitored_complete_fixedPattern_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      Pr[configuration.RawTargetHit |
        ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] := by
  calc
    _ ≤ ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
          Pr[FixedFewTimePatternHit pattern.assignment |
            ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]) :=
      probEvent_rawTargetMonitored_complete_le_ideal configuration secretKey
        targetOrdinal computation initialCache
          (FixedFewTimePatternHit pattern.assignment) q hq hcache
    _ = Pr[configuration.RawTargetHit |
        ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] := by
      rw [probEvent_originConfiguration_rawTargetHit, probEvent_originConfiguration_hit_eq_pattern_mul]
      ac_rfl

end SphincsSecurity.Concrete
