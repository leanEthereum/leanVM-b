import SphincsSecurity.Proof.NormalizedTargetLogSigning
import SphincsSecurity.Proof.TargetSigningCacheGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetMixedMoment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    normalizedTargetLogProduct key cache log payload target required

noncomputable def targetMixedSigningEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (q : Nat) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    (normalizedTargetLogProduct key cache log payload target required +
      (Fintype.card Index : ENNReal)⁻¹ * (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key cache log payload target (required \ selected)) +
      (∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected)) * digestReuseWeight q) +
    (Fintype.card Index : ENNReal)⁻¹ *
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
        ∑ trees ∈ required.powerset,
          (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected,
            normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target (groups slot)) *
              normalizedTargetLogProduct key cache log payload target (required \ trees)

theorem normalizedTargetMixedMoment_eq_frozen_add_growth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (hcache : before ≤ after) :
    normalizedTargetMixedMoment key after log payload target groups required =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        normalizedTargetLogProduct key after log payload target required +
          targetMixedSigningGrowth key before after log payload target groups required := by
  have hmono : normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups ≤
      normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups :=
    Finset.prod_le_prod' (fun slot _ => normalizedCachedTargetSubsetMatch_mono key.parameter before after _ target (groups slot) hcache)
  unfold normalizedTargetMixedMoment targetMixedSigningGrowth
  rw [← add_mul, add_tsub_cancel_of_le hmono]

theorem expected_signWithView_normalizedTargetMixedMoment_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      normalizedTargetMixedMoment key result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required) ≤
      targetMixedSigningEnvelope key before log payload target groups required q := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      normalizedTargetMixedMoment key result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required) =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
          normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required) +
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [normalizedTargetMixedMoment_eq_frozen_add_growth key before result.2 _ payload target groups required
        (simulateQ_romImpl_cache_le (signWithView key message) before result hresult)]
      ring
    · rw [probOutput_eq_zero_of_not_mem_support hresult]
      simp only [zero_mul, mul_zero, add_zero]
  rw [heq]
  apply add_le_add
  · exact mul_le_mul' le_rfl (expected_signWithView_normalizedTargetLogProduct_le key message before log payload target required hsigned q hq hcache)
  · apply (expected_signWithView_targetMixedGrowth_le_uniform key message before log payload target groups required hsigned).trans_eq
    exact expected_targetMixedGrowthPolynomial _ _ groups required target hgroups hdisjoint hremaining

end SphincsSecurity.Concrete
