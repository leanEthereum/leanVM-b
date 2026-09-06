import SphincsSecurity.Proof.FewTimeWeightedAdaptiveTargetBound
import SphincsSecurity.Proof.MessageCollision

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginConfiguration.targetBound
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (reuseWeight : ℝ≥0∞) : ℝ≥0∞ :=
  (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
    Pr[FixedFewTimePatternHit pattern.assignment |
      ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]

noncomputable def weightedSingletonOriginUnionBound
    (signatures sources : Nat) (reuseWeight : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ pattern : FewTimePattern signatures 1,
    ∑ configuration : OriginConfiguration pattern sources, configuration.targetBound reuseWeight

theorem probEvent_originTargetMonitored_complete_fixedPattern_le_weighted
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      configuration.targetBound (digestReuseWeight q) := by
  exact probEvent_originTargetMonitored_complete_le_weighted_ideal configuration secretKey
    targetOrdinal computation initialCache (FixedFewTimePatternHit pattern.assignment) q hq hcache

theorem probEvent_exists_fixedOrdinal_viewedEvent_le_weighted
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard initialCache ≤ q) (candidates : Nat)
    (viewedEvent : Fin candidates → α × ViewedFullTraceState → Prop)
    (himp : ∀ (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent candidate (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ candidate : Fin candidates, viewedEvent candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run
          (OriginTargetMonitorState.initial configuration initialCache).origin.viewed] ≤
      candidates * configuration.targetBound (digestReuseWeight q) := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run
      (OriginTargetMonitorState.initial configuration initialCache).origin.viewed
  calc
    Pr[fun result => ∃ candidate : Fin candidates, viewedEvent candidate result | run] =
        Pr[fun result => ∃ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          viewedEvent candidate result | run] := by
      congr 1
      funext result
      simp
    _ ≤ ∑ candidate ∈ (Finset.univ : Finset (Fin candidates)),
        Pr[viewedEvent candidate | run] :=
      probEvent_exists_finset_le_sum Finset.univ run viewedEvent
    _ ≤ ∑ _candidate ∈ (Finset.univ : Finset (Fin candidates)),
        configuration.targetBound (digestReuseWeight q) := by
      apply Finset.sum_le_sum
      intro candidate _
      calc
        Pr[viewedEvent candidate | run] ≤
            Pr[fun result : α × OriginTargetMonitorState configuration =>
                result.2.Complete ∧
                  (∀ target, result.2.targetView = some target →
                    FixedFewTimePatternHit pattern.assignment
                      (result.2.origin.observation.views, target)) ∧
                  QueryCache.enncard result.2.origin.viewed.cache ≤ q |
              (simulateQ
                (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
                computation).run
                  (OriginTargetMonitorState.initial configuration initialCache)] :=
          probEvent_viewed_le_originTargetMonitoredAdversaryImpl configuration secretKey
            candidate.val computation (OriginTargetMonitorState.initial configuration initialCache)
              (viewedEvent candidate) _ (himp candidate)
        _ ≤ _ := probEvent_originTargetMonitored_complete_fixedPattern_le_weighted
          configuration secretKey candidate.val computation initialCache q hq hcache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le_weighted
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ pattern : FewTimePattern signatures 1,
      OriginConfiguration pattern sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (pattern : FewTimePattern signatures 1)
      (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * weightedSingletonOriginUnionBound signatures sources (digestReuseWeight q) := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result | run] =
        Pr[fun result => ∃ pattern ∈
            (Finset.univ : Finset (FewTimePattern signatures 1)),
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      congr 1
      funext result
      simp
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        Pr[fun result =>
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          Pr[fun result => ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result => ∃ configuration ∈
              (Finset.univ : Finset (OriginConfiguration pattern sources)),
            ∃ candidate : Fin candidates,
              viewedEvent pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          candidates * configuration.targetBound (digestReuseWeight q) := by
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedOrdinal_viewedEvent_le_weighted configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent pattern configuration) (himp pattern configuration)
    _ = candidates * weightedSingletonOriginUnionBound signatures sources (digestReuseWeight q) := by
      rw [weightedSingletonOriginUnionBound]
      simp_rw [← Finset.mul_sum]

theorem probEvent_someFixedSingletonOriginTargetViewedTerminal_le_weighted
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * weightedSingletonOriginUnionBound signatures sources (digestReuseWeight q) := by
  unfold SomeFixedSingletonOriginTargetViewedTerminal
  apply probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le_weighted
    secretKey computation initialCache signatures sources q hq hcache candidates
      (fun _ configuration candidate =>
        FixedOriginTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult rfl
  exact ⟨hcomplete, hhit, hcacheFinal⟩

theorem probEvent_someFixedOneOriginTargetViewedTerminal_le_weighted
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedOneOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * weightedSingletonOriginUnionBound signatures sources (digestReuseWeight q) := by
  calc
    _ = Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
          signatures sources q candidates |
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] := by
      congr 1
      funext result
      exact propext (someFixedOneOriginTargetViewedTerminal_iff secretKey computation
        initialCache signatures sources q candidates result)
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le_weighted
      secretKey computation initialCache signatures sources q hq hcache candidates

end SphincsSecurity.Concrete
