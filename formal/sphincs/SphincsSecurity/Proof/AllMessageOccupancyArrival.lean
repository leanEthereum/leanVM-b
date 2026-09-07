import SphincsSecurity.Proof.AllMessageReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem allMessageOccupancyReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) :
    allMessageOccupancyReuseCharge remaining key (before.cacheQuery input output) log q =
      allMessageOccupancyReuseCharge remaining key before log q +
        (if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          coverageOccupancyCompletionIncrement (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
            remaining (hashOutputFewTimeView output) else 0) * digestReuseWeight q := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before (before.cacheQuery input output) log
    (QueryCache.le_cacheQuery before hfresh) hsigned
  unfold allMessageOccupancyReuseCharge
  rw [hstable, cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh, add_mul]

theorem expected_allMessageOccupancyReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * observedLogOccupancyCompletion remaining key (before, log) * digestReuseWeight q +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        allMessageOccupancyReuseCharge remaining key (before.cacheQuery input output) log q) =
      allMessageOccupancyReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * observedLogOccupancyCompletion (remaining + 1) key (before, log) * digestReuseWeight q := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  simp only [allMessageOccupancyReuseCharge_cacheQuery remaining key before log input _ hfresh hsigned q,
    hmessage, true_and, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [expected_uniformHashOutput_admissible_weight]
  calc
    _ = allMessageOccupancyReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
          (observedLogOccupancyCompletion remaining key (before, log) +
            ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
              coverageOccupancyCompletionIncrement (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
                remaining source) * digestReuseWeight q := by ring
    _ = _ := by
      rw [observedLogOccupancyCompletion, expected_coverageOccupancyCompletionIncrement]
      rfl

theorem allMessageOccupancyReuseCharge_cacheQuery_of_not_message (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : ¬ MessageHashInput key.parameter input) (q : Nat) :
    allMessageOccupancyReuseCharge remaining key (before.cacheQuery input output) log q =
      allMessageOccupancyReuseCharge remaining key before log q := by
  rw [allMessageOccupancyReuseCharge_cacheQuery remaining key before log input output hfresh hsigned q]
  simp only [hmessage, false_and, if_false, zero_mul, add_zero]

theorem expected_randomOracle_allMessageOccupancyReuseCharge (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * observedLogOccupancyCompletion remaining key (before, log) * digestReuseWeight q +
      (∑' result, Pr[= result | (randomOracle input).run before] * allMessageOccupancyReuseCharge remaining key result.2 log q) =
      allMessageOccupancyReuseCharge remaining key before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * observedLogOccupancyCompletion (remaining + 1) key (before, log) * digestReuseWeight q := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
  exact expected_allMessageOccupancyReuseCharge_cacheQuery remaining key before log input hfresh hsigned hmessage q

end SphincsSecurity.Concrete
