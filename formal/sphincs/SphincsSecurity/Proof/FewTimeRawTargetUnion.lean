import SphincsSecurity.Proof.FewTimeRawTargetBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_exists_fixedRawOrdinal_viewedEvent_le_ideal
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
      candidates * Pr[configuration.RawTargetHit |
        ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] := by
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
        Pr[configuration.RawTargetHit |
          ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] := by
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
        _ ≤ _ := probEvent_rawTargetMonitored_complete_fixedPattern_le_ideal
          configuration secretKey candidate.val computation initialCache q hq hcache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_idealOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q)
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
      candidates * rawTargetOriginUnionBound signatures sources := by
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
            candidates * Pr[configuration.RawTargetHit |
              ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedRawOrdinal_viewedEvent_le_ideal configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent distinct pattern configuration)
          (himp distinct pattern configuration)
    _ = candidates * rawTargetOriginUnionBound signatures sources := by
      rw [rawTargetOriginUnionBound]
      simp_rw [← Finset.mul_sum]

def FixedRawTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat)
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  QueryCache.enncard result.2.cache ≤ q ∧
    ∀ monitored : α × OriginTargetMonitorState configuration,
      monitored ∈ support
        ((simulateQ
          (rawTargetMonitoredAdversaryImpl configuration secretKey candidate)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      (monitored.1, monitored.2.origin.viewed) = result →
      monitored.2.Complete ∧
        ∀ target, monitored.2.targetView = some target →
          FixedFewTimePatternHit pattern.assignment
            (monitored.2.origin.observation.views, target)

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat)
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Nat) :
    DecidablePred
      (FixedRawTargetViewedTerminal secretKey computation initialCache q
        configuration candidate) :=
  fun result => Classical.propDecidable
    (FixedRawTargetViewedTerminal secretKey computation initialCache q
      configuration candidate result)

@[irreducible] def SomeFixedRawTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  ∃ distinct ∈ Finset.Icc 1 14,
    ∃ pattern : FewTimePattern signatures distinct,
    ∃ configuration : OriginConfiguration pattern sources,
    ∃ candidate : Fin candidates,
      FixedRawTargetViewedTerminal secretKey computation initialCache q
        configuration candidate.val result

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat) :
    DecidablePred (SomeFixedRawTargetViewedTerminal secretKey computation
      initialCache signatures sources q candidates) :=
  fun result => Classical.propDecidable
    (SomeFixedRawTargetViewedTerminal secretKey computation initialCache
      signatures sources q candidates result)

theorem probEvent_exists_fixedRawTargetViewedTerminal_le_idealOrigin_of_candidates
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedRawTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * rawTargetOriginUnionBound signatures sources := by
  unfold SomeFixedRawTargetViewedTerminal
  apply probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_idealOrigin
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

theorem probEvent_exists_fixedRawTargetViewedTerminal_le_mul_inv131
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures q candidates : Nat)
    (hsignatures : signatures ≤ signatureLimit)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[SomeFixedRawTargetViewedTerminal secretKey computation initialCache
        signatures q q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ := by
  exact (probEvent_exists_fixedRawTargetViewedTerminal_le_idealOrigin_of_candidates
    secretKey computation initialCache signatures q q hq hcache candidates).trans
      (mul_le_mul' le_rfl (rawTargetOriginUnionBound_le_inv131 hsignatures hq))

end SphincsSecurity.Concrete
