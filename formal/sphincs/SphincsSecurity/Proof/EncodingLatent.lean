import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingCharge

/-!
# Latent encoding collisions

A fully cached encoding search can become canonical when a missing earlier retry receives an
inadmissible answer. The collision itself is older: its target is already the least admissible
cached counter for the settled layer message. This cache event records that older witness without
requiring every smaller counter to be cached.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option maxRecDepth 100000

def EncodingMessageSettledAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ index : Index,
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)

theorem EncodingMessageSettledAt.mono {cache cache' : QueryCache HashSpec}
    {secretKey : SecretKey} {position : EncodingPosition} (hle : cache ≤ cache')
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    EncodingMessageSettledAt cache' secretKey position := by
  obtain ⟨index, htree, hleaf, hposition⟩ := hsettled
  exact ⟨index, htree, hleaf, hposition.mono hle⟩

def LatentEncodingBadAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ (index : Index) (counter : Counter)
      (targetPayload otherPayload : HashInput) (targetAnswer otherAnswer : HashOutput),
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)
      ∧ targetPayload = digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret
          (layerMessagePosition index position.lay)) ++ counterBytes counter
      ∧ cache (tweakableHashInput secretKey.parameter position.domain targetPayload) =
          some targetAnswer
      ∧ TargetSum.ValidDigest (truncateHash targetAnswer)
      ∧ (∀ candidate : Counter, candidate.toNat < counter.toNat →
        ∀ answer : HashOutput,
          cache (tweakableHashInput secretKey.parameter position.domain
            (digestBytes (honestValue (fromCache cache) secretKey.parameter
              secretKey.otsSecret secretKey.ftsSecret
              (layerMessagePosition index position.lay)) ++ counterBytes candidate)) =
              some answer →
            ¬ TargetSum.ValidDigest (truncateHash answer))
      ∧ targetPayload ≠ otherPayload
      ∧ cache (tweakableHashInput secretKey.parameter position.domain otherPayload) =
          some otherAnswer
      ∧ truncateHash targetAnswer = truncateHash otherAnswer

theorem latentEncodingBadAt_message_hit_of_settling_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {queryIndex : Index}
    (huncached : cache input = none)
    (htree : treeIndexAt queryIndex position.lay = position.tree)
    (hleaf : leafIndexAt queryIndex position.lay = position.leafIdx)
    (hposition : AtPosition secretKey.parameter input
      (layerMessagePosition queryIndex position.lay))
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition queryIndex position.lay))
    (hbad : LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position) :
    truncateHash answer ∈
      encodingMessageTargets secretKey.parameter cache hfinite position := by
  obtain ⟨targetIndex, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htargetTree, htargetLeaf, hsettledAfter, hpayload,
    htargetAnswer, htargetValid, hbefore, hpayloadNe, hotherAnswer,
    hcollision⟩ := hbad
  have hmessagePosition : layerMessagePosition queryIndex position.lay =
      layerMessagePosition targetIndex position.lay :=
    layerMessagePosition_eq_of_position_eq queryIndex targetIndex position.lay
      (htree.trans htargetTree.symm) (hleaf.trans htargetLeaf.symm)
  have htargetPosition : AtPosition secretKey.parameter input
      (layerMessagePosition targetIndex position.lay) := by
    rwa [← hmessagePosition]
  have htargetUnsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition targetIndex position.lay) := by
    rwa [← hmessagePosition]
  have hmessage := honestValue_cacheQuery_self_of_settled secretKey.parameter
    secretKey.otsSecret secretKey.ftsSecret huncached htargetPosition
    htargetUnsettled hsettledAfter
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  have htargetInputNe : targetInput ≠ input := by
    intro heq
    exact (show AtEncodingPosition secretKey.parameter targetInput position from
      ⟨targetPayload, rfl⟩).not_atPosition
        (layerMessagePosition targetIndex position.lay) (heq ▸ htargetPosition)
  have htargetOld : cache targetInput ≠ none := by
    have htargetAfter : cache.cacheQuery input answer targetInput ≠ none := by
      simp [targetInput, htargetAnswer]
    rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at htargetAfter
  have hmem := slotDigest_mem_encodingMessageTargets hfinite htargetOld
    (show AtEncodingPosition secretKey.parameter targetInput position from
      ⟨targetPayload, rfl⟩)
  have hslot : slotDigest 0 targetInput =
      honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition targetIndex position.lay) := by
    dsimp only [targetInput]
    rw [hpayload]
    exact slotDigest_zero_encodingInput secretKey.parameter position
      (honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition targetIndex position.lay)) counter
  rw [hslot, hmessage] at hmem
  exact hmem

def PrematureLayerMessageSettlement (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (position : EncodingPosition) (index : Index),
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (cache.cacheQuery input answer) (layerMessagePosition index position.lay)
      ∧ ¬ AtPosition secretKey.parameter input
        (layerMessagePosition index position.lay)

theorem PrematureLayerMessageSettlement.mem_settlingTargets
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
          settlingTargets secretKey.parameter cache hfinite queriedPosition := by
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
  rw [settlingTargets, hparent]
  exact Finset.mem_union_right _ hslot

end SphincsSecurity.Concrete
