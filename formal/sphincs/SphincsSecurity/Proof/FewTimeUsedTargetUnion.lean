import SphincsSecurity.Proof.FewTimeWeightedTargetUnion
import SphincsSecurity.Proof.FewTimeUsedPatterns

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def usedWeightedRawTargetOriginUnionBound
    (signatures sources : Nat) (reuseWeight : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : UsedFewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern.1 sources,
        configuration.rawTargetBound reuseWeight

theorem usedWeightedRawTargetOriginUnionBound_le_weighted
    (signatures sources : Nat) (reuseWeight : ℝ≥0∞) :
    usedWeightedRawTargetOriginUnionBound signatures sources reuseWeight ≤
      weightedRawTargetOriginUnionBound signatures sources reuseWeight := by
  classical
  unfold usedWeightedRawTargetOriginUnionBound weightedRawTargetOriginUnionBound
  apply Finset.sum_le_sum
  intro distinct _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun pattern : FewTimePattern signatures distinct => Function.Surjective pattern.assignment)
    (fun pattern => ∑ configuration : OriginConfiguration pattern sources,
      configuration.rawTargetBound reuseWeight)]
  exact le_add_of_nonneg_right bot_le

@[irreducible] def SomeUsedFixedRawTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  ∃ distinct ∈ Finset.Icc 1 14,
    ∃ pattern : UsedFewTimePattern signatures distinct,
    ∃ configuration : OriginConfiguration pattern.1 sources,
    ∃ candidate : Fin candidates,
      FixedRawTargetViewedTerminal secretKey computation initialCache q
        configuration candidate.val result

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat) :
    DecidablePred (SomeUsedFixedRawTargetViewedTerminal secretKey computation
      initialCache signatures sources q candidates) :=
  fun result => Classical.propDecidable
    (SomeUsedFixedRawTargetViewedTerminal secretKey computation initialCache
      signatures sources q candidates result)

theorem probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_usedWeightedOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ (distinct : Nat) (pattern : UsedFewTimePattern signatures distinct),
      OriginConfiguration pattern.1 sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (distinct : Nat) (pattern : UsedFewTimePattern signatures distinct)
      (configuration : OriginConfiguration pattern.1 sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent distinct pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.1.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : UsedFewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern.1 sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * usedWeightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : UsedFewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern.1 sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result | run] ≤
        ∑ distinct ∈ Finset.Icc 1 14,
          Pr[fun result =>
            ∃ pattern : UsedFewTimePattern signatures distinct,
            ∃ configuration : OriginConfiguration pattern.1 sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum (Finset.Icc 1 14) run fun distinct result =>
        ∃ pattern : UsedFewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern.1 sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : UsedFewTimePattern signatures distinct,
          Pr[fun result =>
            ∃ configuration : OriginConfiguration pattern.1 sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      calc
        _ = Pr[fun result =>
              ∃ pattern ∈ (Finset.univ : Finset (UsedFewTimePattern signatures distinct)),
              ∃ configuration : OriginConfiguration pattern.1 sources,
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
          ∃ configuration : OriginConfiguration pattern.1 sources,
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : UsedFewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern.1 sources,
            Pr[fun result => ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result =>
              ∃ configuration ∈
                (Finset.univ : Finset (OriginConfiguration pattern.1 sources)),
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : UsedFewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern.1 sources,
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
    _ = candidates * usedWeightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
      rw [usedWeightedRawTargetOriginUnionBound]
      simp_rw [← Finset.mul_sum]

theorem probEvent_exists_fixedRawTargetViewedTerminal_le_usedWeightedOrigin_of_candidates
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeUsedFixedRawTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * usedWeightedRawTargetOriginUnionBound signatures sources (digestReuseWeight q) := by
  unfold SomeUsedFixedRawTargetViewedTerminal
  apply probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_usedWeightedOrigin
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
