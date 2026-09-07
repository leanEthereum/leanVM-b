import SphincsSecurity.Proof.ObservedCompletion
import SphincsSecurity.Proof.OccupancyBinomialExpansion
import Mathlib.Data.List.Infix

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem SigningDigestsCached.take {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {root : Digest} {log : QueryLog SigningSpec} (hsigned : SigningDigestsCached parameter cache root log) (limit : Nat) :
    SigningDigestsCached parameter cache root (log.take limit) := by
  intro entry hentry
  exact hsigned entry (List.mem_of_mem_take hentry)

noncomputable def frozenLogBinomialOccupancy (key : SecretKey) (degree : Nat) (state : CoverLogState) : ENNReal :=
  observedLogBinomialOccupancy key degree (state.1, state.2.take signatureLimit)

noncomputable def frozenLogOccupancy (key : SecretKey) (state : CoverLogState) : ENNReal :=
  observedLogOccupancy key (state.1, state.2.take signatureLimit)

theorem frozenLogBinomialOccupancy_of_valid (key : SecretKey) (degree : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) :
    frozenLogBinomialOccupancy key degree state = observedLogBinomialOccupancy key degree state := by
  rw [frozenLogBinomialOccupancy, List.take_of_length_le hvalid]

theorem frozenLogOccupancy_of_valid (key : SecretKey) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) : frozenLogOccupancy key state = observedLogOccupancy key state := by
  rw [frozenLogOccupancy, List.take_of_length_le hvalid]

theorem observed_binomialOccupancy_prefix_mono (answers : HashInput → Option HashOutput) (root : Digest)
    (before after : QueryLog SigningSpec) (hprefix : before.IsPrefix after) (degree : Nat) :
    binomialOccupancyMoment (observedOptionalSigningViews answers root before) degree ≤
      binomialOccupancyMoment (observedOptionalSigningViews answers root after) degree := by
  obtain ⟨suffix, rfl⟩ := hprefix
  unfold binomialOccupancyMoment observedOptionalSigningViews
  apply Finset.sum_le_sum
  intro index _
  apply Nat.choose_le_choose
  simp only [signingSlotsAtIndex_log_card, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem frozenLogBinomialOccupancy_mono (key : SecretKey) (degree : Nat) (before after : CoverLogState)
    (hcache : before.1 ≤ after.1) (hprefix : before.2.IsPrefix after.2)
    (hsigned : SigningDigestsCached key.parameter before.1 key.root before.2) :
    frozenLogBinomialOccupancy key degree before ≤ frozenLogBinomialOccupancy key degree after := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before.1 after.1
    (before.2.take signatureLimit) hcache (hsigned.take signatureLimit)
  simp only [frozenLogBinomialOccupancy, observedLogBinomialOccupancy]
  rw [← hstable]
  exact Nat.cast_le.mpr (observed_binomialOccupancy_prefix_mono _ _ _ _ (hprefix.take signatureLimit) degree)

theorem frozenLogOccupancy_eq_binomial (key : SecretKey) (state : CoverLogState) :
    frozenLogOccupancy key state = ∑ degree ∈ Finset.range 14,
      (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
        frozenLogBinomialOccupancy key (degree + 1) state := by
  exact coverageOccupancyMoment_eq_positive_binomial _

theorem frozenLogOccupancy_mono (key : SecretKey) (before after : CoverLogState)
    (hcache : before.1 ≤ after.1) (hprefix : before.2.IsPrefix after.2)
    (hsigned : SigningDigestsCached key.parameter before.1 key.root before.2) :
    frozenLogOccupancy key before ≤ frozenLogOccupancy key after := by
  rw [frozenLogOccupancy_eq_binomial, frozenLogOccupancy_eq_binomial]
  exact Finset.sum_le_sum (fun degree _ => mul_le_mul' le_rfl
    (frozenLogBinomialOccupancy_mono key (degree + 1) before after hcache hprefix hsigned))

theorem logTracedMappedAdversaryImpl_log_prefix (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    state.2.IsPrefix result.2.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, _, rfl⟩ := hresult
  exact List.prefix_append _ _

theorem simulateQ_logTraced_extends {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (result : α × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)) :
    state.1 ≤ result.2.1 ∧ state.2.IsPrefix result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, List.prefix_refl _⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      obtain ⟨hcache, hprefix⟩ := ih middle.1 middle.2 hresult
      exact ⟨(logTracedMappedAdversaryImpl_cache_le key input state middle hmiddle).trans hcache,
        (logTracedMappedAdversaryImpl_log_prefix key input state middle hmiddle).trans hprefix⟩

theorem observedLogOccupancy_le_frozen_terminal {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hvalid : SigningTranscript.Valid state.2) (result : α × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)) :
    observedLogOccupancy key state ≤ frozenLogOccupancy key result.2 := by
  obtain ⟨hcache, hprefix⟩ := simulateQ_logTraced_extends key computation state result hresult
  rw [← frozenLogOccupancy_of_valid key state hvalid]
  exact frozenLogOccupancy_mono key state result.2 hcache hprefix hsigned

theorem worldCoverCharge_le_frozen_terminal {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hvalid : SigningTranscript.Valid state.2) (result : α × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state))
    (world : OracleWorld.Domain) :
    worldCoverCharge key state world ≤
      hashQueryCharge (fun cache input =>
        (if cache input = none ∧ FtsProbeSimulation.MessageHashInput key.parameter input then
          frozenLogOccupancy key result.2 else 0) * ((2 ^ 176 : Nat) : ENNReal)⁻¹) state.1 world := by
  apply (worldCoverCharge_le_observedOccupancy key state world).trans
  cases world with
  | inl _ =>
      dsimp only [hashQueryCharge, Sum.elim]
      exact le_rfl
  | inr input =>
      simp only [hashQueryCharge]
      apply mul_le_mul' ?_ le_rfl
      split_ifs
      · exact observedLogOccupancy_le_frozen_terminal key computation state hsigned hvalid result hresult
      · exact le_rfl

end SphincsSecurity.Concrete
