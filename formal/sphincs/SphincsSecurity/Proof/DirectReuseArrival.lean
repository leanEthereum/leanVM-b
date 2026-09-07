import SphincsSecurity.Proof.UniformReuseIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_allMessageTargetReuseCharge_le_increments (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      allMessageTargetReuseCharge remaining key (before.cacheQuery input output) log q) ≤
      allMessageTargetReuseCharge remaining key before log q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * digestReuseWeight q) * cachedUniformIncrement remaining key before log +
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ * allMessageOccupancyReuseCharge remaining key before log q := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [allMessageTargetReuseCharge_cacheQuery remaining key before log input _ hfresh hsigned q,
    hmessage, true_and, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [expected_uniformHashOutput_admissible_weight, expected_fresh_cachedTargetFutureIncrement_eq remaining key before log input hfresh]
  apply (add_le_add le_rfl (mul_le_mul' (add_le_add
    (expected_allMessageTargetRow_le remaining key before log input hfresh hsigned hmessage) le_rfl) le_rfl)).trans_eq
  unfold allMessageOccupancyReuseCharge
  ring

theorem expected_allMessageOccupancyReuseCharge_eq_increment (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      allMessageOccupancyReuseCharge remaining key (before.cacheQuery input output) log q) =
      allMessageOccupancyReuseCharge remaining key before log q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * digestReuseWeight q) * uniformOccupancyIncrement remaining key before log := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [allMessageOccupancyReuseCharge_cacheQuery remaining key before log input _ hfresh hsigned q,
    hmessage, true_and, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [expected_uniformHashOutput_admissible_weight]
  unfold uniformOccupancyIncrement
  ring

end SphincsSecurity.Concrete
