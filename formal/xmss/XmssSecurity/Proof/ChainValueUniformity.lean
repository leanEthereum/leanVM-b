import XmssSecurity.Proof.AdaptiveFreshTarget

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem Concrete.tweakableHash_fresh_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (target : Digest)
    (hfresh : cache (tweakableHashInput parameter domain payload) = none) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.tweakableHash parameter domain payload :
          OracleComp HashSpec Digest)).run cache] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.tweakableHash
  rw [simulateQ_bind, StateT.run_bind]
  let input := tweakableHashInput parameter domain payload
  have hsimulate :
      simulateQ randomOracle
          (Concrete.oracleHash input : OracleComp HashSpec HashOutput) =
        randomOracle input := by
    simp [Concrete.oracleHash]
  rw [hsimulate]
  rw [QueryImpl.withCaching_run_none _ hfresh]
  simp only [map_eq_bind_pure_comp, bind_assoc, simulateQ_pure,
    StateT.run_pure]
  simp only [uniformSampleImpl, bind_pure_comp, LawfulApplicative.map_pure,
    Function.comp_apply]
  rw [probEvent_map]
  exact Rom.uniform_truncate_probability target

end XmssSecurity
