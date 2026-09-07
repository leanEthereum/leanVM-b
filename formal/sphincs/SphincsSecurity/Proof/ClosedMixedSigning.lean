import SphincsSecurity.Proof.ExpectedSignerMixedGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_logTraced_sign_mixedGrowth_le (power order remaining : Nat) (key : SecretKey) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (mixedSigningGrowthMoments key state.1 power result.2) remaining) ≤
      (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) *
        (occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 lower state) remaining +
          occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key state.1 lower state) remaining)) /
        (Fintype.card Index : ENNReal) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  exact expected_signWithView_mixedGrowthDerivative_le power order remaining key message state.1 state.2 hsigned

theorem expected_logTraced_sign_mixedDerivative_le (power order remaining : Nat) (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key result.2.1 power result.2) remaining) ≤
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power state) (remaining + 1) +
        occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key state.1 (power + 1) state) remaining * digestReuseWeight q +
          (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) *
            (occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 lower state) remaining +
              occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key state.1 lower state) remaining)) /
            (Fintype.card Index : ENNReal) :=
  (expected_logTraced_sign_mixedDerivative_le_growth power order remaining key q hq state hsigned hcache message).trans
    (add_le_add le_rfl (expected_logTraced_sign_mixedGrowth_le power order remaining key state hsigned message))

end SphincsSecurity.Concrete
