import SphincsSecurity.Proof.ParentReleaseQueryBound
import SphincsSecurity.Proof.ParentReserveBound

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem probEvent_parentSettlement_le_direct_release
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput} (hfresh : cache input = none) :
    Pr[ParentSettlement parameter otsSecret ftsSecret cache input | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (directParentRelease parameter otsSecret ftsSecret (fun _ => True) cache input : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hex : ∃ answer, ParentSettlement parameter otsSecret ftsSecret cache input answer
  · obtain ⟨answer, _, child, parent, hat, hb, ha, hp, hparent⟩ := hex
    have hmem := Position.mem_children_iff.mpr hp
    have hother := otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hmem hparent
    have hready : ReadyParentRelease parameter otsSecret ftsSecret cache input parent := ⟨child, hat, hp, hb, ⟨answer, ha⟩, hother⟩
    have hcount : directParentRelease parameter otsSecret ftsSecret (fun _ => True) cache input = (cachedAt parameter cache parent).ncard := by
      rw [directParentRelease_eq_contribution_of_ready parameter otsSecret ftsSecret _ hready, parentReserveContribution,
        if_pos ⟨trivial, fun hall => hb (hall child hmem)⟩]
    have hcover : ∀ output, ParentSettlement parameter otsSecret ftsSecret cache input output →
        truncateHash output ∈ slotTargets parameter cache hfinite child parent := by
      rintro output ⟨_, candidate, ancestor, hc, _, _, hp', hs⟩
      have heq := atPosition_unique parameter hc hat
      subst candidate
      have heq' := Option.some.inj (hp'.symm.trans hp)
      subst ancestor
      by_contra havoid
      exact not_settled_parent_of_avoids_slotTargets parameter otsSecret ftsSecret hfinite hfresh hat hb
        (settled_cacheQuery_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hb ha output) hmem havoid hs
    calc
      _ ≤ Pr[fun output => truncateHash output ∈ slotTargets parameter cache hfinite child parent | ($ᵗ HashOutput : ProbComp HashOutput)] :=
        probEvent_mono (fun output _ h => hcover output h)
      _ ≤ ((slotTargets parameter cache hfinite child parent).card : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
        probEvent_mem_targets_le (fun target => by rw [← probOutput_map]; exact probOutput_truncateHash_le target) _
      _ ≤ _ := by
        rw [hcount]
        exact mul_le_mul' (Nat.cast_le.mpr (slotTargets_card_le parameter cache hfinite child parent)) le_rfl
  · have hz : Pr[ParentSettlement parameter otsSecret ftsSecret cache input | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      rw [probEvent_eq_tsum_ite]
      apply ENNReal.tsum_eq_zero.mpr
      intro answer
      exact if_neg (fun h => hex ⟨answer, h⟩)
    rw [hz]
    exact zero_le

theorem parentSettlementReleaseCharge_le_direct_scaled
    (eligible : Position → Prop) {cache : QueryCache HashSpec} (hfinite : Finite cache) (input : HashInput) :
    parentSettlementReleaseCharge parameter otsSecret ftsSecret eligible cache input ≤
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) *
        directParentQueryCharge parameter otsSecret ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hfresh : cache input = none
  · rw [parentSettlementReleaseCharge_eq_mul_prob parameter otsSecret ftsSecret eligible hfresh,
      directParentQueryCharge, if_pos hfresh, mul_assoc]
    exact mul_le_mul' le_rfl (probEvent_parentSettlement_le_direct_release parameter otsSecret ftsSecret hfinite hfresh)
  · rw [parentSettlementReleaseCharge, directParentQueryCharge, if_neg hfresh, if_neg hfresh, mul_zero, zero_mul]

theorem releasedParentQueryCharge_le_direct_add_scaled
    (eligible : Position → Prop) {cache : QueryCache HashSpec} (hfinite : Finite cache) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input ≤
      directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
        (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) *
          directParentQueryCharge parameter otsSecret ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (releasedParentQueryCharge_le_direct_add_settlement parameter otsSecret ftsSecret eligible cache input).trans
    (add_le_add le_rfl (parentSettlementReleaseCharge_le_direct_scaled parameter otsSecret ftsSecret eligible hfinite input))

end SphincsSecurity
