import SphincsSecurity.Proof.ExpectedRawIndexGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem targetIndexMoments_eq_frozen_add_growth (key : SecretKey) (before : QueryCache HashSpec)
    (power : Nat) (after : CoverLogState) (hcache : before ≤ after.1) (degree : Nat) :
    targetIndexMoments key after.1 after.2 power degree =
      observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter before index ^ power) key after degree +
        rawIndexSigningGrowth key before power after degree := by
  have hweights (index : Index) : cachedIndexMultiplicity key.parameter after.1 index ^ power =
      cachedIndexMultiplicity key.parameter before index ^ power +
        (cachedIndexMultiplicity key.parameter after.1 index ^ power - cachedIndexMultiplicity key.parameter before index ^ power) :=
    (add_tsub_cancel_of_le (pow_le_pow_left' (cachedIndexMultiplicity_mono key.parameter before after.1 hcache index) power)).symm
  unfold targetIndexMoments rawIndexSigningGrowth observedWeightedPowerMoments weightedPowerMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  dsimp only
  conv_lhs => rw [hweights]
  rw [add_mul]

theorem expected_signWithView_targetIndexMoments_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) ≤
        targetIndexSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q) (targetIndexMoments key before log) power degree := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) =
      (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter before index ^ power) key
          (result.2, log ++ [⟨message, result.1.1⟩]) degree) +
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · have hsplit := targetIndexMoments_eq_frozen_add_growth key before power (result.2, log ++ [(⟨message, result.1.1⟩ : SigningEntry)])
        (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) degree
      dsimp only at hsplit
      rw [hsplit, mul_add]
    · rw [probOutput_eq_zero_of_not_mem_support hresult]
      simp only [zero_mul, zero_add]
  rw [heq]
  apply (add_le_add (expected_signWithView_frozenRawIndex_le key message before log power degree hsigned q hq hcache)
    ((expected_signWithView_rawIndexGrowth_le_uniform key message before log power degree hsigned).trans_eq
      (expected_newRawIndexWeight key before log power degree))).trans_eq
  unfold targetIndexSigning
  ring

end SphincsSecurity.Concrete
