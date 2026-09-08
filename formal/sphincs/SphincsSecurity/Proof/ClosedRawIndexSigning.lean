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

theorem expected_signWithView_targetIndexMoments_le_of_reuseWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuseWeight : ENNReal)
    (hreuse : ∀ input, Pr[PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) |
      (simulateQ romImpl (signWithView key message)).run before] ≤ reuseWeight) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) ≤
        targetIndexSigning (freshDigestSelectionProbability key message before *
          (Fintype.card Index : ENNReal)⁻¹) (reuseWeight) (targetIndexMoments key before log) power degree := by
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
  apply (add_le_add (expected_signWithView_frozenRawIndex_le_of_reuseWeight key message before log power degree hsigned reuseWeight hreuse)
    ((expected_signWithView_rawIndexGrowth_le_mass_mul_uniform key message before log power degree hsigned).trans_eq
      (congrArg (fun value => freshDigestSelectionProbability key message before * value)
        (expected_newRawIndexWeight key before log power degree)))).trans_eq
  unfold targetIndexSigning
  ring

theorem expected_signWithView_targetIndexMoments_le_freshMass (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) ≤
        targetIndexSigning (freshDigestSelectionProbability key message before *
          (Fintype.card Index : ENNReal)⁻¹) (digestReuseWeight q) (targetIndexMoments key before log) power degree :=
  expected_signWithView_targetIndexMoments_le_of_reuseWeight key message before log power degree hsigned
    (digestReuseWeight q) (fun input =>
      probEvent_signWithView_fixedPrehit_le_digestReuseWeight key message before input (fun _ => True) q hq hcache)

theorem expected_signWithView_targetIndexMoments_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) ≤
        targetIndexSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q) (targetIndexMoments key before log) power degree := by
  apply (expected_signWithView_targetIndexMoments_le_freshMass key message before log power degree hsigned q hq hcache).trans
  unfold targetIndexSigning
  exact add_le_add (add_le_add le_rfl (mul_le_mul'
    (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)) le_rfl

end SphincsSecurity.Concrete
