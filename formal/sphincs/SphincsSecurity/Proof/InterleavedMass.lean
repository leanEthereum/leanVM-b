import SphincsSecurity.Proof.FrozenSigningLog
import SphincsSecurity.Proof.DirectQueryBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_run_mass_of_query_mass {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hmass : ∀ input state, (∑' result, Pr[= result | (impl input).run state]) = 1)
    (computation : OracleComp spec α) (state : σ) :
    (∑' result, Pr[= result | (simulateQ impl computation).run state]) = 1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have h := tsum_probOutput_bind_mul ((impl input).run state)
        (fun result => (simulateQ impl (next result.1)).run result.2) (fun _ => (1 : ENNReal))
      simp only [mul_one] at h
      rw [h]
      simp_rw [ih, mul_one]
      exact hmass input state

theorem logTracedMappedAdversaryImpl_mass (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state]) = 1 := by
  rw [logTracedMappedAdversaryImpl_run_map]
  have h := tsum_probOutput_map_mul ((unloggedMappedAdversaryImpl key input).run state.1)
    (fun result => (result.1, (result.2, state.2 ++ signingLogFragment input result.1))) (fun _ => (1 : ENNReal))
  simp only [mul_one] at h
  rw [h, unloggedMappedAdversaryImpl_eq_simulateQ_expanded]
  exact simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass _ _

theorem simulateQ_logTraced_mass {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state]) = 1 :=
  simulateQ_run_mass_of_query_mass (logTracedMappedAdversaryImpl key) (logTracedMappedAdversaryImpl_mass key) computation state

theorem frozenLogOccupancy_le_expected_terminal {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    frozenLogOccupancy key state ≤
      ∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
        frozenLogOccupancy key result.2 := by
  calc
    _ = (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state]) *
        frozenLogOccupancy key state := by rw [simulateQ_logTraced_mass, one_mul]
    _ = ∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
        frozenLogOccupancy key state := ENNReal.tsum_mul_right.symm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)
      · obtain ⟨hcache, hprefix⟩ := simulateQ_logTraced_extends key computation state result hresult
        exact mul_le_mul' le_rfl (frozenLogOccupancy_mono key state result.2 hcache hprefix hsigned)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

end SphincsSecurity.Concrete
