import SphincsSecurity.Proof.CachedReuseArrival

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedSourceOccupancyIncrement (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  ∑' sourceInput, cachedSignerInputWeight key message before (fun _ source =>
    coverageOccupancyCompletionIncrement
      (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) sourceInput

theorem expected_freshSourceReuseColumn_le (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        cachedSignerInputWeight key message (before.cacheQuery input output)
          (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input) ≤
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log := by
  apply le_trans ?_ (le_of_eq (expected_freshHashOutput_cachedTargetFutureIncrement remaining key before log input hfresh))
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  rw [cachedSignerInputWeight_freshSource remaining key message before log input output hfresh hsigned]
  split_ifs <;> simp_all only [and_false, zero_le, le_refl]

theorem expected_cachedFutureCoverageReuseCharge_cacheQuery_le (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log * digestReuseWeight q +
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        cachedFutureCoverageReuseCharge remaining key message (before.cacheQuery input output) log q) ≤
      cachedFutureCoverageReuseCharge remaining key message before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        cachedSourceOccupancyIncrement remaining key message before log * digestReuseWeight q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  let row := fun output => ∑' sourceInput,
    cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput
  let column := fun output => cachedSignerInputWeight key message (before.cacheQuery input output)
    (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  have heq : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedFutureCoverageReuseCharge remaining key message (before.cacheQuery input output) log q) =
      cachedFutureCoverageReuseCharge remaining key message before log q +
        ((∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * row output) +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * column output) * digestReuseWeight q := by
    simp only [cachedFutureCoverageReuseCharge_cacheQuery remaining key message before log input _ hfresh hsigned q,
      row, column, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, add_mul]
  calc
    _ = cachedFutureCoverageReuseCharge remaining key message before log q +
        (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * row output) * digestReuseWeight q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log +
          ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * column output) * digestReuseWeight q := by
      rw [heq]
      ring
    _ ≤ cachedFutureCoverageReuseCharge remaining key message before log q +
        (cachedSourceOccupancyIncrement remaining key message before log * ((2 ^ 176 : Nat) : ENNReal)⁻¹) * digestReuseWeight q +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log) * digestReuseWeight q :=
      add_le_add (add_le_add le_rfl (mul_le_mul'
        (expected_freshTargetReuseRow_le remaining key message before log input hfresh hsigned hmessage) le_rfl))
        (mul_le_mul' (expected_freshSourceReuseColumn_le remaining key message before log input hfresh hsigned) le_rfl)
    _ = _ := by ring

theorem expected_randomOracle_cachedFutureCoverageReuseCharge_le (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (q : Nat) :
    ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage remaining key.parameter key.root before log * digestReuseWeight q +
      (∑' result, Pr[= result | (randomOracle input).run before] *
        cachedFutureCoverageReuseCharge remaining key message result.2 log q) ≤
      cachedFutureCoverageReuseCharge remaining key message before log q +
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * cachedFutureCoverage (remaining + 1) key.parameter key.root before log * digestReuseWeight q +
        cachedSourceOccupancyIncrement remaining key message before log * digestReuseWeight q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
  exact expected_cachedFutureCoverageReuseCharge_cacheQuery_le remaining key message before log input hfresh hsigned hmessage q

end SphincsSecurity.Concrete
