import SphincsSecurity.Proof.FewTimeTargetTerminal

namespace SphincsSecurity.Concrete.Range125

open OracleComp OracleSpec ENNReal

theorem probEvent_originTargetMonitored_complete_fixedPattern_le_ideal
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
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  calc
    _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[FixedFewTimePatternHit pattern.assignment |
          ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
            ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] :=
      probEvent_originTargetMonitored_complete_le_ideal configuration secretKey
        targetOrdinal computation initialCache
          (FixedFewTimePatternHit pattern.assignment) q hq hcache
    _ = Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      rw [probEvent_originConfiguration_hit_eq_pattern_mul]
      ac_rfl

theorem probEvent_exists_fixedOrdinal_viewedEvent_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 125)
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
      candidates * Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
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
        Pr[configuration.Hit |
          ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
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
        _ ≤ _ := probEvent_originTargetMonitored_complete_fixedPattern_le_ideal
          configuration secretKey candidate.val computation initialCache q hq hcache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SphincsSecurity.Concrete.Range125
