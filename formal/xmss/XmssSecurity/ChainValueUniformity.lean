import XmssSecurity.AdaptiveFreshTarget
import XmssSecurity.CacheQuerySupport
import XmssSecurity.ConcreteQueryBound
import XmssSecurity.HiddenValue

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

theorem Concrete.chainHash_fresh_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (step : ChainStep) (value target : Digest)
    (hfresh : cache (Concrete.CacheView.chainInput parameter epoch chain step value) = none) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.chainHash parameter epoch chain step value :
          OracleComp HashSpec Digest)).run cache] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.chainHash Concrete.tweakableHash
  rw [simulateQ_bind, StateT.run_bind]
  let input := tweakableHashInput parameter (.chain epoch chain step)
    (Concrete.digestBytes value)
  change cache input = none at hfresh
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

/-- The last valid step of a WOTS chain is uniform whenever its typed address is absent from the initial cache. -/
theorem Concrete.chainWalk_positive_probability_from_cache_le
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value target : Digest)
    (hvalid : position + steps < chainLength - 1)
    (initialCache : QueryCache HashSpec)
    (habsent : ∀ input,
      AtHashAddress parameter (.chain epoch chain ⟨position + steps, hvalid⟩) input →
        initialCache input = none) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position (steps + 1) value :
          OracleComp HashSpec Digest)).run initialCache] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  let lastStep : ChainStep := ⟨position + steps, hvalid⟩
  rw [Concrete.chainWalk]
  simp only [hvalid, ↓reduceDIte, simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro prefixResult hprefix
  have haddressBound :
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest).IsQueryBoundP
          (AtHashAddress parameter (.chain epoch chain lastStep)) 0 := by
    apply Concrete.chainWalk_queryBound_zero_of_avoids
    intro offset hoffset hoffsetValid heq
    simp only [HashDomain.chain.injEq] at heq
    have hposition := congrArg Fin.val heq.2.2
    dsimp only [lastStep] at hposition
    omega
  have hexactBound :
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest).IsQueryBoundP
          (· = Concrete.CacheView.chainInput parameter epoch chain lastStep prefixResult.1) 0 :=
    OracleComp.IsQueryBoundP.of_imp
      (fun input heq => by
        subst input
        rw [Concrete.CacheView.chainInput]
        exact (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)
      haddressBound
  have hfresh : prefixResult.2
      (Concrete.CacheView.chainInput parameter epoch chain lastStep prefixResult.1) = none :=
    Concrete.CacheReplay.cache_none_of_zero_query_bound
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest)
      (Concrete.CacheView.chainInput parameter epoch chain lastStep prefixResult.1)
      initialCache prefixResult.2 prefixResult.1 hexactBound
      (habsent _ ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)) hprefix
  exact (Concrete.chainHash_fresh_probability prefixResult.2 parameter epoch chain lastStep
    prefixResult.1 target hfresh).le

theorem Concrete.chainWalk_positive_probability_le
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value target : Digest)
    (hvalid : position + steps < chainLength - 1) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position (steps + 1) value :
          OracleComp HashSpec Digest)).run ∅] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  exact Concrete.chainWalk_positive_probability_from_cache_le parameter epoch chain
    position steps value target hvalid ∅ (fun input _ => by simp)

/-- Arbitrary earlier random-oracle work does not reduce the entropy of the last chain step when it avoids that typed address. -/
theorem Concrete.chainWalk_positive_after_prefix_probability_le {α : Type}
    (prefixComputation : OracleComp HashSpec α) (start : α → Digest)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (target : Digest)
    (hvalid : position + steps < chainLength - 1)
    (hprefixBound : prefixComputation.IsQueryBoundP
      (AtHashAddress parameter (.chain epoch chain ⟨position + steps, hvalid⟩)) 0) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (prefixComputation >>= fun prefixValue =>
          Concrete.chainWalk parameter epoch chain position (steps + 1)
            (start prefixValue))).run ∅] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro prefixResult hprefix
  apply Concrete.chainWalk_positive_probability_from_cache_le
  intro input haddress
  exact Concrete.CacheReplay.cache_none_of_zero_query_bound prefixComputation input
    ∅ prefixResult.2 prefixResult.1
    (OracleComp.IsQueryBoundP.of_imp
      (fun candidate heq => by simpa [heq] using haddress) hprefixBound)
    (by simp) hprefix

noncomputable def isolatedChainValueExperiment (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (digit : Digit) : ProbComp (Digest × QueryCache HashSpec) := do
  let secret ← $ᵗ Digest
  (simulateQ randomOracle
    (Concrete.chainWalk parameter epoch chain 0 digit.val secret :
      OracleComp HashSpec Digest)).run ∅

/-- Every fixed position of an isolated random-oracle WOTS chain has 128 bits of pointwise entropy. -/
theorem isolatedChainValue_probability_le (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (digit : Digit) (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      isolatedChainValueExperiment parameter epoch chain digit] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hzero : digit.val = 0
  · unfold isolatedChainValueExperiment
    simp only [hzero, Concrete.chainWalk, simulateQ_pure, StateT.run_pure]
    rw [probEvent_bind_eq_tsum]
    calc
      ∑' secret : Digest, Pr[= secret | $ᵗ Digest] *
          Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
            pure (secret, ∅)] =
        Pr[= target | $ᵗ Digest] := by
          rw [← probEvent_eq_eq_probOutput, probEvent_eq_tsum_ite]
          apply tsum_congr
          intro secret
          by_cases heq : secret = target <;> simp [heq]
      _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
        HiddenValue.uniform_digest_point_probability target
      _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := le_rfl
  · let steps := digit.val - 1
    have hdigit : digit.val = steps + 1 := by
      dsimp only [steps]
      omega
    unfold isolatedChainValueExperiment
    rw [hdigit]
    apply probEvent_bind_le_of_forall_le
    intro secret _
    apply Concrete.chainWalk_positive_probability_le
    have hdigitLt := digit.isLt
    dsimp only [steps]
    omega

end XmssSecurity
