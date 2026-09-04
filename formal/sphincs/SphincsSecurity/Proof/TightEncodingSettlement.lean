import SphincsSecurity.Proof.TightChargePotential
import SphincsSecurity.Proof.EncodingSelectionPotential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem PrematureLayerMessageSettlement.mem_tightSettlingTargets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none)
    (hpremature : PrematureLayerMessageSettlement cache secretKey input answer) :
    ∃ queriedPosition : Position,
      AtPosition secretKey.parameter input queriedPosition ∧
        ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          cache queriedPosition ∧
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (cache.cacheQuery input answer) queriedPosition ∧
        truncateHash answer ∈
          tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition := by
  obtain ⟨encodingPosition, index, htree, hleaf, htargetUnsettled,
    htargetSettled, hnotTarget⟩ := hpremature
  let targetPosition := layerMessagePosition index encodingPosition.lay
  have htargetUnsettled' : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache targetPosition := by
    simpa only [targetPosition] using htargetUnsettled
  have htargetSettled' : Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (cache.cacheQuery input answer) targetPosition := by
    simpa only [targetPosition] using htargetSettled
  have hnotTarget' : ¬ AtPosition secretKey.parameter input targetPosition := by
    simpa only [targetPosition] using hnotTarget
  have hat : ∃ queriedPosition, AtPosition secretKey.parameter input queriedPosition := by
    by_contra hnone
    apply htargetUnsettled'
    exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached (p₀ := none)
      (fun position hposition => (hnone ⟨position, hposition⟩).elim)
      (by simp) (targetPosition.depth + 1) targetPosition (by omega) (by simp)
      htargetSettled'
  obtain ⟨queriedPosition, hqueried⟩ := hat
  have hqueriedNe : queriedPosition ≠ targetPosition := by
    intro heq
    exact hnotTarget' (heq ▸ hqueried)
  have hqueriedUnsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache queriedPosition := by
    intro hsettled
    apply htargetUnsettled'
    exact settled_of_cacheQuery_at_settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached hqueried hsettled
      (targetPosition.depth + 1) targetPosition (by omega) htargetSettled'
  have hpositionRule : ∀ position,
      AtPosition secretKey.parameter input position →
        some queriedPosition = some position := by
    intro position hposition
    exact congrArg some (atPosition_unique secretKey.parameter hqueried hposition)
  obtain ⟨parent, hparent, hparentSettled⟩ : ∃ parent,
      queriedPosition.parentOf = some parent ∧
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (cache.cacheQuery input answer) parent := by
    cases hparent : queriedPosition.parentOf with
    | none =>
        exfalso
        apply htargetUnsettled'
        exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret huncached (p₀ := some queriedPosition) hpositionRule
          (by
            intro position parent heq hparent'
            have hpositionEq : position = queriedPosition := Option.some.inj heq.symm
            subst position
            rw [hparent] at hparent'
            simp at hparent')
          (targetPosition.depth + 1) targetPosition (by omega)
          (by
            intro heq
            exact hqueriedNe (Option.some.inj heq)) htargetSettled'
    | some parent =>
        by_cases hsettledParent : Settled secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (cache.cacheQuery input answer) parent
        · exact ⟨parent, rfl, hsettledParent⟩
        · exfalso
          apply htargetUnsettled'
          exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret huncached (p₀ := some queriedPosition) hpositionRule
            (by
              intro position candidateParent heq hparent'
              have hpositionEq : position = queriedPosition := Option.some.inj heq.symm
              subst position
              rw [hparent] at hparent'
              have : candidateParent = parent := Option.some.inj hparent'.symm
              subst candidateParent
              exact hsettledParent)
            (targetPosition.depth + 1) targetPosition (by omega)
            (by
              intro heq
              exact hqueriedNe (Option.some.inj heq)) htargetSettled'
  have hchild : queriedPosition ∈ parent.children :=
    Position.mem_children_iff.mpr hparent
  have hqueriedSettled : Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (cache.cacheQuery input answer) queriedPosition :=
    hparentSettled.children queriedPosition hchild
  have hslot : truncateHash answer ∈ slotTargets secretKey.parameter cache hfinite
      queriedPosition parent := by
    by_contra havoid
    exact (not_settled_parent_of_avoids_slotTargets secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret hfinite huncached hqueried
      hqueriedUnsettled hqueriedSettled hchild havoid) hparentSettled
  refine ⟨queriedPosition, hqueried, hqueriedUnsettled, hqueriedSettled, ?_⟩
  have hother := otherChildrenSettled_of_parent_settled_cacheQuery secretKey.parameter
    secretKey.otsSecret secretKey.ftsSecret huncached hqueried hchild hparentSettled
  simp only [tightSettlingTargets, hparent]
  rw [if_pos hother]
  exact Finset.mem_union_right _ hslot


end SphincsSecurity.Concrete
