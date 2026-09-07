import SphincsSecurity.Proof.TargetShapeReindex

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetShapeMoments (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) : TargetShapeVector :=
  fun groups remaining =>
    (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
      (tweakableHashInput key.parameter .message payload) target group) *
        normalizedTargetLogProduct key cache log payload target remaining

theorem targetShapeMoments_eq_indexed (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeMoments key cache log payload target groups remaining =
      normalizedTargetMixedMoment key cache log payload target (targetGroupAt groups) remaining := by
  simp only [targetShapeMoments, normalizedTargetMixedMoment, normalizedTargetCacheProduct, prod_targetGroupAt]

theorem targetShapeMoments_cacheLower_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (targetShapeMoments key cache log payload target) groups remaining =
      (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
        ∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target remaining := by
  rw [sum_targetGroupAt_removed_products, Finset.sum_mul]
  rfl

theorem targetShapeMoments_reuse_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (targetShapeMoments key cache log payload target) groups remaining =
      (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) target group) *
          ∑ selected ∈ remaining.powerset.erase ∅,
            normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
              normalizedTargetLogProduct key cache log payload target (remaining \ selected) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected hselected
  have hnot := hvalid.new_group (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2)
  simp only [targetShapeMoments, Finset.prod_insert hnot]
  ring

theorem targetShapeMoments_cross_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      ∑ trees ∈ remaining.powerset,
        (∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target (remaining \ trees)) =
      targetCacheLower (targetShapeMoments key cache log payload target) groups remaining +
        targetCacheLower (targetTreeLower (targetShapeMoments key cache log payload target)) groups remaining := by
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_targetGroupAt_removed_products, Finset.sum_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset remaining)]
  simp only [Finset.sdiff_empty, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rfl

theorem targetShapeSigning_eq_indexedEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) (q : Nat) :
    targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (targetShapeMoments key cache log payload target) groups remaining =
        targetMixedSigningEnvelope key cache log payload target (targetGroupAt groups) remaining q := by
  unfold targetMixedSigningEnvelope
  rw [targetShapeMoments_cross_eq]
  simp only [normalizedTargetCacheProduct, prod_targetGroupAt]
  unfold targetShapeSigning
  rw [targetShapeMoments_reuse_eq key cache log payload target groups remaining hvalid]
  have htree : targetTreeLower (targetShapeMoments key cache log payload target) groups remaining =
      (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) target group) *
          ∑ trees ∈ remaining.powerset.erase ∅, normalizedTargetLogProduct key cache log payload target (remaining \ trees) := by
    simp only [targetTreeLower, targetShapeMoments, Finset.mul_sum]
  rw [htree]
  unfold targetShapeMoments
  ring

theorem expected_signWithView_targetShapeMoments_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
          (targetShapeMoments key before log payload target) groups remaining := by
  simp only [targetShapeMoments_eq_indexed]
  rw [targetShapeSigning_eq_indexedEnvelope key before log payload target groups remaining hvalid q]
  exact expected_signWithView_normalizedTargetMixedMoment_le key message before log payload target (targetGroupAt groups) remaining
    (fun slot => hvalid.nonempty _ (targetGroupAt_mem groups slot))
    (fun i j hij => hvalid.disjoint _ (targetGroupAt_mem groups i) _ (targetGroupAt_mem groups j)
      (fun heq => hij (targetGroupAt_injective groups heq)))
    (fun slot => hvalid.remaining _ (targetGroupAt_mem groups slot)) hsigned q hq hcache

end SphincsSecurity.Concrete
