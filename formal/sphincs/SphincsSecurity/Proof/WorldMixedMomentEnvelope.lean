import SphincsSecurity.Proof.ClosedMixedSigning
import SphincsSecurity.Proof.MixedMomentEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def observedMixedDerivativeVector (key : SecretKey) (remaining : Nat) (state : CoverLogState) : MixedMomentVector :=
  fun power order => occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power state) remaining

theorem expected_logTraced_sign_mixedEnvelope_le (key : SecretKey) (q remaining : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) (power order : Nat) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedMixedDerivativeVector key remaining result.2 power order) ≤
      mixedSigningEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (observedMixedDerivativeVector key remaining state) power order := by
  apply (expected_logTraced_sign_mixedDerivative_le power order remaining key q hq state hsigned hcache message).trans_eq
  rw [occupancyDerivativePolynomial_succ]
  simp only [mixedSigningEnvelope, mixedPowerLower, observedMixedDerivativeVector, div_eq_mul_inv, mul_add, Finset.sum_add_distrib]
  ring

theorem observedMixedDerivativeVector_cacheQuery_of_nonmessage (key : SecretKey) (remaining : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : ¬ MessageHashInput key.parameter input) :
    observedMixedDerivativeVector key remaining (before.cacheQuery input output, log) =
      observedMixedDerivativeVector key remaining (before, log) := by
  funext power order
  have hstable : mixedIndexBinomialMoments key (before.cacheQuery input output) power (before.cacheQuery input output, log) =
      mixedIndexBinomialMoments key before power (before, log) := by
    funext degree
    simp only [mixedIndexBinomialMoments_cacheQuery key power degree before log input output hfresh hsigned,
      hmessage, false_and, if_false, add_zero]
  exact congrArg (fun moments => occupancyDerivativePolynomial order moments remaining) hstable

theorem expected_fresh_mixedEnvelope_le (key : SecretKey) (remaining : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (power order : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedMixedDerivativeVector key remaining (before.cacheQuery input output, log) power order) ≤
      mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))
        (observedMixedDerivativeVector key remaining (before, log)) power order := by
  by_cases hmessage : MessageHashInput key.parameter input
  · rw [show (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        observedMixedDerivativeVector key remaining (before.cacheQuery input output, log) power order) = _ from
      expected_message_mixedDerivative power order remaining key before log input hfresh hsigned hmessage]
    exact le_of_eq (by unfold mixedQueryEnvelope mixedPowerLower observedMixedDerivativeVector; rw [mul_comm])
  · have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
    simp only [observedMixedDerivativeVector_cacheQuery_of_nonmessage key remaining before log input _ hfresh hsigned hmessage,
      ENNReal.tsum_mul_right, hmass, one_mul, mixedQueryEnvelope]
    exact le_self_add

theorem expected_randomOracle_mixedEnvelope_le (key : SecretKey) (remaining : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (power order : Nat) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      observedMixedDerivativeVector key remaining (result.2, log) power order) ≤
      mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))
        (observedMixedDerivativeVector key remaining (before, log)) power order := by
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    exact expected_fresh_mixedEnvelope_le key remaining before log input hfresh hsigned power order
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    exact le_self_add

theorem expected_romImpl_mixedEnvelope_le (key : SecretKey) (remaining : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (power order : Nat) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      observedMixedDerivativeVector key remaining (result.2, log) power order) ≤
      mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))
        (observedMixedDerivativeVector key remaining (before, log)) power order := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] *
        observedMixedDerivativeVector key remaining (result.2, log) power order) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
      exact le_self_add
  | inr input => exact expected_randomOracle_mixedEnvelope_le key remaining before log input hsigned power order

theorem expected_logTraced_sign_remainingEnvelope_le (key : SecretKey) (q remaining queries signatures : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) (power order : Nat) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) queries signatures
        (observedMixedDerivativeVector key remaining result.2) power order) ≤
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) queries (signatures + 1)
        (observedMixedDerivativeVector key remaining state) power order := by
  rw [mixedRemainingEnvelope_expected]
  exact (mixedRemainingEnvelope_mono _ _ _ queries signatures
    (fun p o => expected_logTraced_sign_mixedEnvelope_le key q remaining hq state hsigned hcache message p o) power order).trans
      (mixedRemainingEnvelope_signing_le _ _ _ queries signatures _ power order)

theorem expected_fresh_remainingEnvelope_le (key : SecretKey) (q remaining queries signatures : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (power order : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) queries signatures
        (observedMixedDerivativeVector key remaining (before.cacheQuery input output, log)) power order) ≤
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) (queries + 1) signatures
        (observedMixedDerivativeVector key remaining (before, log)) power order := by
  rw [mixedRemainingEnvelope_expected, ← mixedRemainingEnvelope_query]
  exact mixedRemainingEnvelope_mono _ _ _ queries signatures
    (fun p o => expected_fresh_mixedEnvelope_le key remaining before log input hfresh hsigned p o) power order

end SphincsSecurity.Concrete
