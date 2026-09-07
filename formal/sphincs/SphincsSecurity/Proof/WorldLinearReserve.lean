import SphincsSecurity.Proof.CachedLinearReserve
import SphincsSecurity.Proof.WorldPairReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_romImpl_linearReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((romImpl input).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (romImpl input).run before] * cachedLinearReuseReserve remaining key q result.2 log) ≤
      cachedLinearReuseReserve remaining key q before log + hashQueryCharge (freshMessageReuseCharge remaining key q log) before input := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] * cachedLinearReuseReserve remaining key q result.2 log) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only [hashQueryCharge, Sum.elim_inl]
      rw [add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input => exact expected_randomOracle_linearReserve_le remaining key q before log input hsigned hcap

theorem expected_fixedLog_linearReserve_le {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] * cachedLinearReuseReserve remaining key q result.2 log) ≤
      cachedLinearReuseReserve remaining key q before log + expectedQueryCharge (freshMessageReuseCharge remaining key q log) computation before := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedQueryCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      have htail (middle : OracleWorld.Range input × QueryCache HashSpec)
          (hmiddle : middle ∈ support ((romImpl input).run before)) :
          ∀ result ∈ support ((simulateQ romImpl (next middle.1)).run middle.2), QueryCache.enncard result.2 ≤ q := by
        intro result hresult
        apply hcap result
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨middle, hmiddle, hresult⟩
      have hstep := expected_romImpl_linearReserve_le remaining key q before log input hsigned
        (fun middle hmiddle => simulateQ_romImpl_initial_cache_bound q (next middle.1) middle.2 (htail middle hmiddle))
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul, expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' middle, Pr[= middle | (romImpl input).run before] *
            (cachedLinearReuseReserve remaining key q middle.2 log +
              expectedQueryCharge (freshMessageReuseCharge remaining key q log) (next middle.1) middle.2) := by
          apply ENNReal.tsum_le_tsum
          intro middle
          by_cases hmiddle : middle ∈ support ((romImpl input).run before)
          · have hcache := simulateQ_romImpl_cache_le (OracleSpec.query input) before middle
              (by simpa only [simulateQ_spec_query] using hmiddle)
            exact mul_le_mul' le_rfl (ih middle.1 middle.2 (hsigned.mono hcache) (htail middle hmiddle))
          · rw [probOutput_eq_zero_of_not_mem_support hmiddle, zero_mul, zero_mul]
        _ = (∑' middle, Pr[= middle | (romImpl input).run before] * cachedLinearReuseReserve remaining key q middle.2 log) +
            ∑' middle, Pr[= middle | (romImpl input).run before] *
              expectedQueryCharge (freshMessageReuseCharge remaining key q log) (next middle.1) middle.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ _ := by
          rw [← add_assoc]
          exact add_le_add hstep le_rfl

theorem expected_fixedLog_linearReserve_le_of_no_message {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → before input = none)
    (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] * cachedLinearReuseReserve remaining key q result.2 log) ≤
      expectedQueryCharge (freshMessageReuseCharge remaining key q log) computation before := by
  simpa only [cachedLinearReuseReserve_of_no_message remaining key q before log hnone, zero_add] using
    expected_fixedLog_linearReserve_le remaining key q before log hsigned computation hcap

end SphincsSecurity.Concrete
