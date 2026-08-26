import SphincsSecurity.Proof.EncodingTarget
import SphincsSecurity.Proof.RootCache

/-!
# Amortized charge for encoding collisions

The cache-local encoding target at one one-time position is unique. Inputs cached at that encoding
tweak before the target is pinned pay one unit each for the answer that pins it. Once pinned, a
fresh encoding query has only that one target.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

structure EncodingPosition where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  deriving DecidableEq, Fintype

def EncodingPosition.domain (position : EncodingPosition) : HashDomain :=
  .encoding position.lay position.tree position.leafIdx

def AtEncodingPosition (parameter : PublicParameter) (input : HashInput)
    (position : EncodingPosition) : Prop :=
  ∃ payload, input = tweakableHashInput parameter position.domain payload

theorem atEncodingPosition_unique {parameter : PublicParameter} {input : HashInput}
    {left right : EncodingPosition} (hleft : AtEncodingPosition parameter input left)
    (hright : AtEncodingPosition parameter input right) : left = right := by
  obtain ⟨leftPayload, hleft⟩ := hleft
  obtain ⟨rightPayload, hright⟩ := hright
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
    (hleft.symm.trans hright)).1
  obtain ⟨leftLay, leftTree, leftLeaf⟩ := left
  obtain ⟨rightLay, rightTree, rightLeaf⟩ := right
  simp only [EncodingPosition.domain, HashDomain.encoding.injEq] at hdomain
  obtain ⟨rfl, rfl, rfl⟩ := hdomain
  rfl

theorem atEncodingPosition_ne {parameter : PublicParameter} {leftInput rightInput : HashInput}
    {leftPosition rightPosition : EncodingPosition}
    (hleft : AtEncodingPosition parameter leftInput leftPosition)
    (hright : AtEncodingPosition parameter rightInput rightPosition)
    (hne : leftPosition ≠ rightPosition) : leftInput ≠ rightInput := by
  intro heq
  exact hne (atEncodingPosition_unique hleft (heq ▸ hright))

theorem AtEncodingPosition.not_atPosition {parameter : PublicParameter} {input : HashInput}
    {encodingPosition : EncodingPosition} (hencoding : AtEncodingPosition parameter input encodingPosition)
    (position : Position) : ¬ AtPosition parameter input position := by
  rintro ⟨structuralPayload, hstructural⟩
  obtain ⟨encodingPayload, hencodingInput⟩ := hencoding
  have hdomain := (tweakableHashInput_injective parameter (by trivial)
    position.domain_inRange (hencodingInput.symm.trans hstructural)).1
  cases position <;> simp [EncodingPosition.domain, Position.domain] at hdomain

def QueriesAtEncodingPositionOrPositions {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (position : EncodingPosition)
    (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f oa →
    AtEncodingPosition parameter input position ∨
      ∃ structuralPosition : Position, AtPosition parameter input structuralPosition

theorem QueriesAtEncodingPositionOrPositions.pure {alpha : Type}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (position : EncodingPosition)
    (value : alpha) :
    QueriesAtEncodingPositionOrPositions parameter f position (pure value) := by
  simp [QueriesAtEncodingPositionOrPositions]

theorem QueriesAtEncodingPositionOrPositions.bind {alpha beta : Type}
    {parameter : PublicParameter} {f : QueryImpl HashSpec Id} {position : EncodingPosition}
    {oa : OracleComp HashSpec alpha} {next : alpha → OracleComp HashSpec beta}
    (hleft : QueriesAtEncodingPositionOrPositions parameter f position oa)
    (hright : QueriesAtEncodingPositionOrPositions parameter f position
      (next (evalWithAnswerFn f oa))) :
    QueriesAtEncodingPositionOrPositions parameter f position (oa >>= next) := by
  intro input hinput
  rw [queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact hleft input hinput
  · exact hright input hinput

theorem QueriesAtEncodingPositionOrPositions.encode (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (position : EncodingPosition) (message : Digest)
    (counter : Counter) :
    QueriesAtEncodingPositionOrPositions parameter f position
      (encode parameter position.lay position.tree position.leafIdx message counter) := by
  intro input hinput
  rw [SphincsSecurity.Concrete.encode, queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
    exact Or.inl ⟨_, hinput⟩
  · simp at hinput

theorem QueriesAtEncodingPositionOrPositions.structural {alpha : Type}
    {parameter : PublicParameter} {f : QueryImpl HashSpec Id} {position : EncodingPosition}
    {oa : OracleComp HashSpec alpha} (hrun : QueriesAtPositions parameter f oa) :
    QueriesAtEncodingPositionOrPositions parameter f position oa := by
  intro input hinput
  obtain ⟨structuralPosition, payload, heq⟩ := hrun input hinput
  exact Or.inr ⟨structuralPosition, payload, heq⟩

theorem queriesAtEncodingPositionOrPositions_otsSignFrom (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (position : EncodingPosition)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    QueriesAtEncodingPositionOrPositions parameter f position
      (otsSignFrom parameter position.lay position.tree position.leafIdx secret message
        attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact QueriesAtEncodingPositionOrPositions.pure parameter f position _
  | succ attempts ih =>
      rw [otsSignFrom]
      apply QueriesAtEncodingPositionOrPositions.bind
        (QueriesAtEncodingPositionOrPositions.encode parameter f position message _)
      split
      · apply QueriesAtEncodingPositionOrPositions.bind
        · apply QueriesAtEncodingPositionOrPositions.structural
          apply queriesAtPositions_sequenceFin
          intro chainIdx
          exact queriesAtPositions_chainWalk parameter f position.lay position.tree
            position.leafIdx chainIdx 0 _ _
        · exact QueriesAtEncodingPositionOrPositions.pure parameter f position _
      · exact ih (counter + 1)

theorem queriesAtEncodingPositionOrPositions_otsSign (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (position : EncodingPosition)
    (secret : ChainIndex → Digest) (message : Digest) :
    QueriesAtEncodingPositionOrPositions parameter f position
      (otsSign parameter position.lay position.tree position.leafIdx secret message) := by
  exact queriesAtEncodingPositionOrPositions_otsSignFrom parameter f position secret message
    encodingAttemptLimit 0

theorem encodingPosition_eq_of_mem_otsSign {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {queriedPosition runPosition : EncodingPosition}
    {input : HashInput} {secret : ChainIndex → Digest} {message : Digest}
    (hposition : AtEncodingPosition parameter input queriedPosition)
    (hinput : input ∈ queriedInputs f
      (otsSign parameter runPosition.lay runPosition.tree runPosition.leafIdx secret message)) :
    queriedPosition = runPosition := by
  rcases queriesAtEncodingPositionOrPositions_otsSign parameter f runPosition secret message
      input hinput with hrun | ⟨structuralPosition, hstructural⟩
  · exact atEncodingPosition_unique hposition hrun
  · exact absurd hstructural (hposition.not_atPosition structuralPosition)

def encodingCachedAt (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) : Set HashInput :=
  {input | cache input ≠ none ∧ AtEncodingPosition parameter input position}

theorem encodingCachedAt_finite {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingCachedAt parameter cache position).Finite :=
  hfinite.subset fun _ hinput => hinput.1

def HasEncodingTarget (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ payload, CachedSignedEncodingPayloadAt cache secretKey position.lay position.tree
    position.leafIdx payload

theorem HasEncodingTarget.mono {cache cache' : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition} (hle : cache ≤ cache')
    (htarget : HasEncodingTarget cache secretKey position) :
    HasEncodingTarget cache' secretKey position := by
  obtain ⟨payload, hpayload⟩ := htarget
  exact ⟨payload, hpayload.mono hle⟩

theorem HasEncodingTarget.payload_unique {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition} {leftPayload rightPayload : HashInput}
    (left : CachedSignedEncodingPayloadAt cache secretKey position.lay position.tree
      position.leafIdx leftPayload)
    (right : CachedSignedEncodingPayloadAt cache secretKey position.lay position.tree
      position.leafIdx rightPayload) : leftPayload = rightPayload :=
  cachedSignedEncodingPayloadAt_unique left right

theorem CachedSignedEncodingPayloadAt.of_cacheQuery_of_other_encodingPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput}
    {answer : HashOutput} {queriedPosition : EncodingPosition} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {payload : HashInput}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hne : queriedPosition ≠ ⟨lay, tree, leafIdx⟩)
    (htarget : CachedSignedEncodingPayloadAt (cache.cacheQuery input answer) secretKey
      lay tree leafIdx payload) :
    CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload := by
  obtain ⟨index, part, htree, hleaf, hsettledAfter, hrunAfter, hevalAfter, hpayload,
    hcachedAfter⟩ := htarget
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  have hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (layerMessagePosition index lay) := by
    exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached (p₀ := none)
      (fun position hposition => absurd hposition (hqueried.not_atPosition position))
      (by simp) ((layerMessagePosition index lay).depth + 1)
      (layerMessagePosition index lay) (by omega) (by simp) hsettledAfter
  have hmessage := honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) hsettled
  have hnotMem : input ∉ queriedInputs (fromCache (cache.cacheQuery input answer))
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        (honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index lay))) := by
    intro hmem
    apply hne
    have hposition := encodingPosition_eq_of_mem_otsSign
      (parameter := secretKey.parameter)
      (f := fromCache (cache.cacheQuery input answer))
      (queriedPosition := queriedPosition)
      (runPosition := ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩)
      (input := input)
      (secret := secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
      (message := honestValue (fromCache (cache.cacheQuery input answer))
        secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (layerMessagePosition index lay)) hqueried hmem
    simpa only [htree, hleaf] using hposition
  have hrunOldAnswer := hrunAfter.of_cacheQuery_of_not_mem hnotMem
  rw [hmessage] at hrunOldAnswer hevalAfter
  have hrun := hrunOldAnswer.changeAnswerFn
    (agreesWithFn_fromCache_of_le hle) (agreesWithFn_fromCache cache)
  have hevalEq := hrunOldAnswer.eval_eq
    (agreesWithFn_fromCache_of_le hle) (agreesWithFn_fromCache cache)
  have htargetNe : tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) payload ≠
      input := by
    intro heq
    apply hne
    have hposition := atEncodingPosition_unique hqueried
      (show AtEncodingPosition secretKey.parameter input ⟨lay, tree, leafIdx⟩ from
        ⟨payload, heq.symm⟩)
    exact hposition
  have hcached : cache
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) payload) ≠ none := by
    rwa [QueryCache.cacheQuery_of_ne _ _ htargetNe] at hcachedAfter
  refine ⟨index, part, htree, hleaf, hsettled, hrun, ?_, ?_, hcached⟩
  · exact hevalEq.symm.trans hevalAfter
  · rwa [hmessage] at hpayload

theorem HasEncodingTarget.of_cacheQuery_of_other_encodingPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput}
    {answer : HashOutput} {queriedPosition targetPosition : EncodingPosition}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hne : queriedPosition ≠ targetPosition)
    (htarget : HasEncodingTarget (cache.cacheQuery input answer) secretKey targetPosition) :
    HasEncodingTarget cache secretKey targetPosition := by
  obtain ⟨payload, hpayload⟩ := htarget
  exact ⟨payload, hpayload.of_cacheQuery_of_other_encodingPosition huncached hqueried hne⟩

theorem clean_encodingBad_cacheQuery_of_existing_target
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput}
    {answer : HashOutput} {position : EncodingPosition} {targetPayload : HashInput}
    {targetAnswer : HashOutput}
    (hclean : ¬ EncodingBad cache secretKey) (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position)
    (htarget : CachedSignedEncodingPayloadAt cache secretKey position.lay position.tree
      position.leafIdx targetPayload)
    (htargetAnswer : cache (tweakableHashInput secretKey.parameter position.domain targetPayload) =
      some targetAnswer)
    (havoid : truncateHash answer ≠ truncateHash targetAnswer) :
    ¬ EncodingBad (cache.cacheQuery input answer) secretKey := by
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rintro ⟨badLay, badTree, badLeaf, badTargetPayload, otherPayload, badTargetAnswer,
    otherAnswer, hbadTarget, hpayloadNe, hbadTargetAnswer, hotherAnswer, hcollision⟩
  let badPosition : EncodingPosition := ⟨badLay, badTree, badLeaf⟩
  by_cases heq : position = badPosition
  · have htarget' : CachedSignedEncodingPayloadAt cache secretKey badLay badTree badLeaf
        targetPayload := by
      simpa only [badPosition, heq] using htarget
    have htargetAnswer' : cache
        (tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
          targetPayload) = some targetAnswer := by
      have := htargetAnswer
      rw [heq] at this
      simpa only [badPosition, EncodingPosition.domain] using this
    have hpayload : targetPayload = badTargetPayload :=
      cachedSignedEncodingPayloadAt_unique (htarget'.mono hle) hbadTarget
    have htargetOld : CachedSignedEncodingPayloadAt cache secretKey badLay badTree badLeaf
        badTargetPayload := by
      rwa [← hpayload]
    have htargetInputNe :
        tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
          badTargetPayload ≠ input := by
      intro hinput
      rw [← hpayload] at hinput
      have hnone := huncached
      rw [← hinput, htargetAnswer'] at hnone
      simp at hnone
    have htargetAnswerEq : badTargetAnswer = targetAnswer := by
      have hcached := hbadTargetAnswer
      rw [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at hcached
      rw [← hpayload] at hcached
      exact Option.some.inj (hcached.symm.trans htargetAnswer')
    by_cases hother : tweakableHashInput secretKey.parameter
        (.encoding badLay badTree badLeaf) otherPayload = input
    · have hanswerEq : otherAnswer = answer := by
        have hcached := hotherAnswer
        rw [hother, QueryCache.cacheQuery_self] at hcached
        exact Option.some.inj hcached.symm
      apply havoid
      rw [← hanswerEq, ← htargetAnswerEq]
      exact hcollision.symm
    · apply hclean
      refine ⟨badLay, badTree, badLeaf, badTargetPayload, otherPayload,
        badTargetAnswer, otherAnswer, htargetOld, hpayloadNe, ?_, ?_, hcollision⟩
      · rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at hbadTargetAnswer
      · rwa [QueryCache.cacheQuery_of_ne _ _ hother] at hotherAnswer
  · have hne : position ≠ ⟨badLay, badTree, badLeaf⟩ := by
      simpa only [badPosition] using heq
    have hbadTargetOld := hbadTarget.of_cacheQuery_of_other_encodingPosition
      huncached hposition hne
    have htargetInputNe :
        tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
          badTargetPayload ≠ input :=
      atEncodingPosition_ne
        (show AtEncodingPosition secretKey.parameter
          (tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
            badTargetPayload) ⟨badLay, badTree, badLeaf⟩ from ⟨_, rfl⟩)
        hposition hne.symm
    have hotherInputNe :
        tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
          otherPayload ≠ input :=
      atEncodingPosition_ne
        (show AtEncodingPosition secretKey.parameter
          (tweakableHashInput secretKey.parameter (.encoding badLay badTree badLeaf)
            otherPayload) ⟨badLay, badTree, badLeaf⟩ from ⟨_, rfl⟩)
        hposition hne.symm
    apply hclean
    refine ⟨badLay, badTree, badLeaf, badTargetPayload, otherPayload, badTargetAnswer,
      otherAnswer, hbadTargetOld, hpayloadNe, ?_, ?_, hcollision⟩
    · rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at hbadTargetAnswer
    · rwa [QueryCache.cacheQuery_of_ne _ _ hotherInputNe] at hotherAnswer

noncomputable def encodingContribution (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Nat :=
  open Classical in
  if HasEncodingTarget cache secretKey position then 0
  else (encodingCachedAt secretKey.parameter cache position).ncard

noncomputable def encodingPotential (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : Nat :=
  open Classical in
  ∑ position : EncodingPosition, encodingContribution cache secretKey position

theorem encodingPotential_empty (secretKey : SecretKey) :
    encodingPotential ∅ secretKey = 0 := by
  classical
  rw [encodingPotential]
  refine Finset.sum_eq_zero fun position _ => ?_
  rw [encodingContribution]
  split
  · rfl
  · have hempty : encodingCachedAt secretKey.parameter (∅ : QueryCache HashSpec) position = ∅ := by
      ext input
      simp [encodingCachedAt]
    rw [hempty, Set.ncard_empty]

theorem encodingCachedAt_cacheQuery_of_not_atPosition
    {parameter : PublicParameter} {cache : QueryCache HashSpec} {input : HashInput}
    {answer : HashOutput} {position : EncodingPosition}
    (hposition : ¬ AtEncodingPosition parameter input position) :
    encodingCachedAt parameter (cache.cacheQuery input answer) position =
      encodingCachedAt parameter cache position := by
  ext candidate
  by_cases heq : candidate = input
  · subst candidate
    simp only [encodingCachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self]
    exact ⟨fun h => absurd h.2 hposition, fun h => absurd h.2 hposition⟩
  · simp only [encodingCachedAt, Set.mem_setOf_eq,
      QueryCache.cacheQuery_of_ne _ _ heq]

theorem encodingCachedAt_cacheQuery_self {parameter : PublicParameter}
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} (hposition : AtEncodingPosition parameter input position) :
    encodingCachedAt parameter (cache.cacheQuery input answer) position =
      insert input (encodingCachedAt parameter cache position) := by
  ext candidate
  by_cases heq : candidate = input
  · subst candidate
    simp only [encodingCachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self,
      Set.mem_insert_iff, true_or, ne_eq, reduceCtorEq, not_false_eq_true, hposition, and_self]
  · simp only [encodingCachedAt, Set.mem_setOf_eq,
      QueryCache.cacheQuery_of_ne _ _ heq, Set.mem_insert_iff, heq, false_or]

theorem encodingContribution_cacheQuery_le_of_not_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput}
    {answer : HashOutput} {position : EncodingPosition} (huncached : cache input = none)
    (hposition : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingContribution cache secretKey position := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingContribution, encodingContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      omega
    · rw [if_neg htarget', encodingCachedAt_cacheQuery_of_not_atPosition hposition]

theorem encodingContribution_cacheQuery_le_of_atPosition
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {input : HashInput}
    {answer : HashOutput} {position : EncodingPosition} (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    encodingContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingContribution cache secretKey position + 1 := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingContribution, encodingContribution]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget, if_pos (htarget.mono hle)]
    exact Nat.zero_le _
  · rw [if_neg htarget]
    by_cases htarget' : HasEncodingTarget (cache.cacheQuery input answer) secretKey position
    · rw [if_pos htarget']
      omega
    · rw [if_neg htarget', encodingCachedAt_cacheQuery_self hposition]
      exact Set.ncard_insert_le _ _

theorem encodingPotential_cacheQuery_le {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none) :
    encodingPotential (cache.cacheQuery input answer) secretKey ≤
      encodingPotential cache secretKey + 1 := by
  classical
  by_cases hat : ∃ position, AtEncodingPosition secretKey.parameter input position
  · obtain ⟨queriedPosition, hqueried⟩ := hat
    rw [encodingPotential, encodingPotential]
    calc
      ∑ position : EncodingPosition,
          encodingContribution (cache.cacheQuery input answer) secretKey position ≤
          ∑ position : EncodingPosition,
            (encodingContribution cache secretKey position +
              if position = queriedPosition then 1 else 0) := by
        apply Finset.sum_le_sum
        intro position _
        by_cases heq : position = queriedPosition
        · rw [if_pos heq]
          simpa only [heq] using
            encodingContribution_cacheQuery_le_of_atPosition huncached hqueried
        · rw [if_neg heq, Nat.add_zero]
          apply encodingContribution_cacheQuery_le_of_not_atPosition huncached
          intro hposition
          exact heq (atEncodingPosition_unique hposition hqueried)
      _ = (∑ position : EncodingPosition,
            encodingContribution cache secretKey position) + 1 := by
        rw [Finset.sum_add_distrib]
        rw [Fintype.sum_ite_eq']
  · rw [encodingPotential, encodingPotential]
    calc
      ∑ position : EncodingPosition,
          encodingContribution (cache.cacheQuery input answer) secretKey position ≤
          ∑ position : EncodingPosition, encodingContribution cache secretKey position := by
        apply Finset.sum_le_sum
        intro position _
        exact encodingContribution_cacheQuery_le_of_not_atPosition huncached
          (fun hposition => hat ⟨position, hposition⟩)
      _ ≤ _ := Nat.le_add_right _ 1

theorem encodingPotential_cacheQuery_le_of_target {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position)
    (htarget : HasEncodingTarget cache secretKey position) :
    encodingPotential (cache.cacheQuery input answer) secretKey ≤
      encodingPotential cache secretKey := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingPotential, encodingPotential]
  apply Finset.sum_le_sum
  intro otherPosition _
  by_cases heq : otherPosition = position
  · rw [heq, encodingContribution, encodingContribution, if_pos htarget,
      if_pos (htarget.mono hle)]
  · apply encodingContribution_cacheQuery_le_of_not_atPosition huncached
    intro hother
    exact heq (atEncodingPosition_unique hother hposition)

theorem encodingBad_step_of_existing_target {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (hclean : ¬ EncodingBad cache secretKey) (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position)
    (htarget : HasEncodingTarget cache secretKey position) :
    ∃ targets : Finset Digest, targets.card ≤ encodingPotential cache secretKey + 1
      ∧ ∀ answer : HashOutput, truncateHash answer ∉ targets →
        ¬ EncodingBad (cache.cacheQuery input answer) secretKey
          ∧ encodingPotential (cache.cacheQuery input answer) secretKey + targets.card ≤
            encodingPotential cache secretKey + 1 := by
  classical
  obtain ⟨targetPayload, htargetPayload⟩ := htarget
  have htargetData := htargetPayload
  obtain ⟨_, _, _, _, _, _, _, _, htargetCached⟩ := htargetData
  obtain ⟨targetAnswer, htargetAnswer⟩ := Option.ne_none_iff_exists'.mp htargetCached
  let target := truncateHash targetAnswer
  refine ⟨{target}, ?_, ?_⟩
  · simp only [Finset.card_singleton]
    omega
  · intro answer hanswer
    have havoid : truncateHash answer ≠ truncateHash targetAnswer := by
      simpa only [Finset.mem_singleton, target] using hanswer
    refine ⟨clean_encodingBad_cacheQuery_of_existing_target hclean huncached hposition
      htargetPayload htargetAnswer havoid, ?_⟩
    simpa only [Finset.card_singleton] using Nat.add_le_add_right
      (encodingPotential_cacheQuery_le_of_target huncached hposition
        ⟨targetPayload, htargetPayload⟩) 1

end SphincsSecurity.Concrete
