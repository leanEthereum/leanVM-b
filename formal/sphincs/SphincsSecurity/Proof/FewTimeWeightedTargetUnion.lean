import SphincsSecurity.Proof.FewTimeWeightedTargetCount
import SphincsSecurity.Proof.FewTimeRawTargetUnion

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_exists_fixedRawOrdinal_viewedEvent_le_weighted
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
          (rawTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
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
      candidates * configuration.rawTargetBound (digestReuseWeight q) := by
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
        configuration.rawTargetBound (digestReuseWeight q) := by
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
                (rawTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
                computation).run
                  (OriginTargetMonitorState.initial configuration initialCache)] :=
          probEvent_viewed_le_rawTargetMonitoredAdversaryImpl configuration secretKey
            candidate.val computation (OriginTargetMonitorState.initial configuration initialCache)
              (viewedEvent candidate) _ (himp candidate)
        _ ≤ _ := probEvent_rawTargetMonitored_complete_fixedPattern_le_weighted
          configuration secretKey candidate.val computation initialCache q hq hcache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_weightedOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ (distinct : Nat) (pattern : FewTimePattern signatures distinct),
      OriginConfiguration pattern sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (distinct : Nat) (pattern : FewTimePattern signatures distinct)
      (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent distinct pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * weightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result | run] ≤
        ∑ distinct ∈ Finset.Icc 1 14,
          Pr[fun result =>
            ∃ pattern : FewTimePattern signatures distinct,
            ∃ configuration : OriginConfiguration pattern sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum (Finset.Icc 1 14) run fun distinct result =>
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          Pr[fun result =>
            ∃ configuration : OriginConfiguration pattern sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      calc
        _ = Pr[fun result =>
              ∃ pattern ∈ (Finset.univ : Finset (FewTimePattern signatures distinct)),
              ∃ configuration : OriginConfiguration pattern sources,
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern sources,
            Pr[fun result => ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result =>
              ∃ configuration ∈
                (Finset.univ : Finset (OriginConfiguration pattern sources)),
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern sources,
            candidates * configuration.rawTargetBound (digestReuseWeight q) := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedRawOrdinal_viewedEvent_le_weighted configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent distinct pattern configuration)
          (himp distinct pattern configuration)
    _ = candidates * weightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
      rw [weightedRawTargetOriginUnionBound]
      simp_rw [← Finset.mul_sum]

theorem probEvent_exists_fixedRawTargetViewedTerminal_le_weightedOrigin_of_candidates
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedRawTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * weightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
  unfold SomeFixedRawTargetViewedTerminal
  apply probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_weightedOrigin
    secretKey computation initialCache signatures sources q hq hcache candidates
      (fun _ _ configuration candidate =>
        FixedRawTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro distinct pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  have hprojection : (result.1, result.2.origin.viewed) =
      (result.1, result.2.origin.viewed) := rfl
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult hprojection
  exact ⟨hcomplete, hhit, hcacheFinal⟩

end SphincsSecurity.Concrete
