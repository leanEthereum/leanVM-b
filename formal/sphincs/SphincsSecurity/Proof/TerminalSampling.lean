import SphincsSecurity.Proof.TerminalBudget

/-!
# Lifting residual terminal events across secret sampling

The structural and few-time bounds hold after the sampled tables are fixed. The residual opening
events do not, because their probability comes from the hidden table entries themselves. This
module keeps the sampled tables in the observational output so those events can be averaged at the
correct point in the original game.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

structure SampledSecrets where
  parameter : PublicParameter
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest

noncomputable def sampleSecrets : ProbComp SampledSecrets := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  pure ⟨parameter, otsSecret, ftsSecret⟩

theorem SampledSecrets.support_components {secrets : SampledSecrets}
    (hsecrets : secrets ∈ support sampleSecrets) :
    secrets.parameter ∈ support sampleParameter
      ∧ secrets.otsSecret ∈ support sampleOtsSecrets
      ∧ secrets.ftsSecret ∈ support sampleFtsSecrets := by
  rw [sampleSecrets, mem_support_bind_iff] at hsecrets
  obtain ⟨parameter, hparameter, hsecrets⟩ := hsecrets
  rw [mem_support_bind_iff] at hsecrets
  obtain ⟨otsSecret, hots, hsecrets⟩ := hsecrets
  rw [mem_support_bind_iff] at hsecrets
  obtain ⟨ftsSecret, hfts, hsecrets⟩ := hsecrets
  simp only [support_pure, Set.mem_singleton_iff] at hsecrets
  subst secrets
  exact ⟨hparameter, hots, hfts⟩

structure SampledViewedResult where
  secrets : SampledSecrets
  result : (Digest × Forgery × Bool) × ViewedFullTraceState

noncomputable def sampledViewedGame (adversary : Adversary) : ProbComp SampledViewedResult := do
  let secrets ← sampleSecrets
  let result ← gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
    secrets.ftsSecret
  pure ⟨secrets, result⟩

noncomputable def sampledGame (adversary : Adversary) : ProbComp Bool := do
  let secrets ← sampleSecrets
  (simulateQ romImpl
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)).run' ∅

theorem forgeAdvantage_eq_sampledGame (adversary : Adversary) :
    forgeAdvantage scheme adversary = Pr[= true | sampledGame adversary] := by
  rw [forgeAdvantage, gameCore_eq_secrets, simulateQ_romImpl_liftM_bind_run']
  simp_rw [simulateQ_romImpl_liftM_bind_run']
  simp only [sampledGame, sampleSecrets, bind_assoc, pure_bind]

def SampledViewedEvent
    (event : PublicParameter →
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) →
      ((Digest × Forgery × Bool) × ViewedFullTraceState) → Prop)
    (output : SampledViewedResult) : Prop :=
  event output.secrets.parameter output.secrets.otsSecret output.secrets.ftsSecret output.result

theorem probEvent_sampledViewedGame_eq_weighted
    (adversary : Adversary)
    (event : PublicParameter →
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) →
      ((Digest × Forgery × Bool) × ViewedFullTraceState) → Prop) :
    Pr[SampledViewedEvent event | sampledViewedGame adversary] =
      ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        Pr[event secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret] := by
  classical
  rw [sampledViewedGame, probEvent_bind_eq_tsum]
  refine tsum_congr fun secrets => ?_
  rw [probEvent_bind_eq_tsum]
  congr 1
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun result => ?_
  rw [probEvent_pure]
  by_cases hresult : event secrets.parameter secrets.otsSecret secrets.ftsSecret result
  · simp [SampledViewedEvent, hresult]
  · simp [SampledViewedEvent, hresult]

theorem probEvent_bind_le_const_add_weighted
    {Alpha Beta : Type} {oa : ProbComp Alpha} {run : Alpha → ProbComp Beta}
    {event : Beta → Prop} {cost : ℝ≥0∞} (risk : Alpha → ℝ≥0∞)
    (hbound : ∀ value ∈ support oa, Pr[event | run value] ≤ cost + risk value) :
    Pr[event | oa >>= run] ≤
      cost + ∑' value : Alpha, Pr[= value | oa] * risk value := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value : Alpha, Pr[= value | oa] * (cost + risk value) := by
      refine ENNReal.tsum_le_tsum fun value => ?_
      by_cases hvalue : value ∈ support oa
      · gcongr
        exact hbound value hvalue
      · rw [probOutput_eq_zero_of_not_mem_support hvalue, zero_mul, zero_mul]
    _ = (∑' value : Alpha, Pr[= value | oa] * cost) +
        ∑' value : Alpha, Pr[= value | oa] * risk value := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
    _ ≤ cost + ∑' value : Alpha, Pr[= value | oa] * risk value := by
      gcongr
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

def cleanFreshEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧ result.1.2.2 = true) ∧
    ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result

def cleanEncodingEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result

def cleanBackwardEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  (¬Bad parameter otsSecret ftsSecret result.2.cache ∧ result.1.2.2 = true) ∧
    ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result

def cleanMessageEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result

def cleanUncoveredEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result

noncomputable def remainingRisk (adversary : Adversary) (secrets : SampledSecrets) : ℝ≥0∞ :=
  let run := gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
    secrets.ftsSecret
  Pr[cleanFreshEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanEncodingEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanBackwardEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
      Pr[cleanUncoveredEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run])))

theorem weighted_remainingRisk_eq (adversary : Adversary) :
    (∑' secrets : SampledSecrets,
      Pr[= secrets | sampleSecrets] * remainingRisk adversary secrets) =
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) := by
  simp only [remainingRisk, mul_add, ENNReal.tsum_add]
  rw [← probEvent_sampledViewedGame_eq_weighted adversary cleanFreshEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanEncodingEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanBackwardEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanMessageEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanUncoveredEvent]

theorem forgeAdvantage_le_reserved_add_sampled_remaining
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120) :
    forgeAdvantage scheme adversary ≤
      ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary])))) := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame]
  calc
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        ∑' secrets : SampledSecrets,
          Pr[= secrets | sampleSecrets] * remainingRisk adversary secrets := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_const_add_weighted
        (oa := sampleSecrets)
        (run := fun secrets => (simulateQ romImpl
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret)).run' ∅)
        (event := fun verdict => verdict = true)
        (cost := ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹)
        (remainingRisk adversary)
      intro secrets hsecrets
      obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
      have hrisk : remainingRisk adversary secrets =
          let run := gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret
          Pr[fun result =>
              (¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret result.2.cache ∧
                result.1.2.2 = true) ∧
              ViewedFreshLayerOpeningWitness secrets.parameter secrets.otsSecret
                secrets.ftsSecret result | run] +
          (Pr[fun result => ¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret
              result.2.cache ∧ ViewedEncodingCollisionWitness secrets.parameter
                secrets.otsSecret secrets.ftsSecret result | run] +
          (Pr[fun result =>
              (¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret result.2.cache ∧
                result.1.2.2 = true) ∧
              ViewedBackwardChainOpeningWitness secrets.parameter secrets.otsSecret
                secrets.ftsSecret result | run] +
          (Pr[fun result => ¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret
              result.2.cache ∧ ViewedMessageDigestCollisionWitness secrets.parameter
                secrets.otsSecret secrets.ftsSecret result | run] +
          Pr[fun result => ¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret
              result.2.cache ∧ ViewedUncoveredFtsSecretWitness secrets.parameter
                secrets.otsSecret secrets.ftsSecret result | run]))) := by
        rfl
      rw [hrisk]
      rw [probEvent_eq_eq_probOutput]
      exact probEvent_win_le_reserved_add_remaining adversary q hq hqMax
        secrets.parameter hparameter secrets.otsSecret hots secrets.ftsSecret hfts
    _ = _ := by rw [weighted_remainingRisk_eq]

end SphincsSecurity.Concrete
