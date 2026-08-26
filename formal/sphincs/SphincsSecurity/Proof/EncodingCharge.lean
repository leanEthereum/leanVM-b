import SphincsSecurity.Proof.EncodingTarget
import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.MessagePrehit
import SphincsSecurity.Proof.NoMessage
import SphincsSecurity.Proof.RootCache
import SphincsSecurity.Proof.SignerDigestSource
import SphincsSecurity.Proof.SigningTrace

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

def AvoidsEncodingQueries {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ (position : EncodingPosition) (payload : HashInput),
    tweakableHashInput parameter position.domain payload ∉ queriedInputs f oa

theorem AvoidsEncodingQueries.pure {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    AvoidsEncodingQueries parameter f (pure value) := by
  simp [AvoidsEncodingQueries]

theorem AvoidsEncodingQueries.bind {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : AvoidsEncodingQueries parameter f oa)
    (hright : AvoidsEncodingQueries parameter f (next (evalWithAnswerFn f oa))) :
    AvoidsEncodingQueries parameter f (oa >>= next) := by
  intro position payload hinput
  rw [queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact hleft position payload hinput
  · exact hright position payload hinput

theorem AvoidsEncodingQueries.tweakableHash (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (domain : HashDomain)
    (hdomain : ∀ position : EncodingPosition, domain ≠ position.domain)
    (payload : HashInput) : AvoidsEncodingQueries parameter f
      (tweakableHash parameter domain payload) := by
  intro position encodingPayload hinput
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  cases domain with
  | encoding lay tree leafIdx =>
      apply hdomain position
      exact (tweakBytes_injective (by trivial) (by trivial) htweak).symm
  | chain | leaf | node | ftsLeaf | ftsNode | ftsRoots | message =>
      rw [tweakBytes_eq_iff] at htweak
      simp [hashDomainFields, EncodingPosition.domain, TweakFields.mk.injEq] at htweak

theorem QueriesAtPositions.avoidsEncoding {alpha : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hrun : QueriesAtPositions parameter f oa) : AvoidsEncodingQueries parameter f oa := by
  intro position payload hinput
  obtain ⟨structuralPosition, structuralPayload, heq⟩ := hrun _ hinput
  exact (show AtEncodingPosition parameter
    (tweakableHashInput parameter position.domain payload) position from ⟨_, rfl⟩).not_atPosition
      structuralPosition ⟨structuralPayload, heq⟩

theorem avoidsEncodingQueries_sequenceFin {alpha : Type} {n : Nat}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, AvoidsEncodingQueries parameter f (computation index)) :
    AvoidsEncodingQueries parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact AvoidsEncodingQueries.pure parameter f _
  | succ n ih =>
      rw [sequenceFin]
      apply AvoidsEncodingQueries.bind (hcomputation 0)
      apply AvoidsEncodingQueries.bind
      · exact ih (fun index : Fin n => computation index.succ)
          (fun index => hcomputation index.succ)
      · exact AvoidsEncodingQueries.pure parameter f _

theorem not_mem_queriedInputs_sequenceFin {alpha : Type} {n : Nat}
    (f : QueryImpl HashSpec Id) (computation : Fin n → OracleComp HashSpec alpha)
    (input : HashInput) (hcomputation : ∀ index, input ∉ queriedInputs f (computation index)) :
    input ∉ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, queriedInputs_bind]
      intro hinput
      rcases List.mem_append.mp hinput with hhead | hrest
      · exact hcomputation 0 hhead
      · rw [queriedInputs_bind] at hrest
        rcases List.mem_append.mp hrest with htail | hpure
        · exact ih (fun index : Fin n => computation index.succ)
            (fun index : Fin n => hcomputation index.succ) htail
        · simp at hpure

theorem avoidsEncodingQueries_treeNode (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    AvoidsEncodingQueries parameter f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      apply AvoidsEncodingQueries.bind
      · exact QueriesAtPositions.avoidsEncoding
          (queriesAtPositions_oneTimePublicKey parameter f lay tree (leafOfNat nodeIdx)
            (secret (leafOfNat nodeIdx)))
      · apply AvoidsEncodingQueries.tweakableHash
        intro position
        simp [EncodingPosition.domain]
  | succ level ih =>
      rw [treeNode_succ_eq]
      apply AvoidsEncodingQueries.bind (ih (2 * nodeIdx))
      apply AvoidsEncodingQueries.bind (ih (2 * nodeIdx + 1))
      apply AvoidsEncodingQueries.tweakableHash
      intro position
      simp [EncodingPosition.domain]

theorem avoidsEncodingQueries_treePath (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leafIdx : LeafIndex) :
    AvoidsEncodingQueries parameter f (treePath parameter lay tree secret leafIdx) := by
  apply avoidsEncodingQueries_sequenceFin
  intro level
  split
  · exact avoidsEncodingQueries_treeNode parameter f lay tree secret _ _
  · exact AvoidsEncodingQueries.pure parameter f _

theorem avoidsEncodingQueries_ftsNode (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    AvoidsEncodingQueries parameter f (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      apply AvoidsEncodingQueries.tweakableHash
      intro position
      simp [EncodingPosition.domain]
  | succ level ih =>
      rw [ftsNode_succ_eq]
      apply AvoidsEncodingQueries.bind (ih (2 * nodeIdx))
      apply AvoidsEncodingQueries.bind (ih (2 * nodeIdx + 1))
      apply AvoidsEncodingQueries.tweakableHash
      intro position
      simp [EncodingPosition.domain]

theorem avoidsEncodingQueries_ftsKey (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsEncodingQueries parameter f (ftsKey parameter index secret) := by
  rw [ftsKey]
  apply AvoidsEncodingQueries.bind
  · apply avoidsEncodingQueries_sequenceFin
    intro tree
    exact avoidsEncodingQueries_ftsNode parameter f index tree (secret tree) ftsTreeHeight 0
  · apply AvoidsEncodingQueries.tweakableHash
    intro position
    simp [EncodingPosition.domain]

theorem avoidsEncodingQueries_ftsOpen (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsEncodingQueries parameter f (ftsOpen parameter index leaves secret) := by
  apply avoidsEncodingQueries_sequenceFin
  intro tree
  apply avoidsEncodingQueries_sequenceFin
  intro level
  exact avoidsEncodingQueries_ftsNode parameter f index tree (secret tree) level.val _

theorem avoidsEncodingQueries_layerMessage (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    AvoidsEncodingQueries secretKey.parameter f (layerMessage secretKey index lay) := by
  rw [layerMessage]
  split
  · exact avoidsEncodingQueries_treeNode secretKey.parameter f _ _ _ _ _
  · exact avoidsEncodingQueries_ftsKey secretKey.parameter f index (secretKey.ftsSecret index)

theorem signDigestLoop_cache_encoding_none (attempts : Nat) (secretKey : SecretKey)
    (message : Message) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)))
    (hmem : (result, afterCache) ∈ support
      ((simulateQ romImpl (signDigestLoop attempts secretKey message)).run beforeCache))
    (target : HashInput) (position : EncodingPosition)
    (hposition : AtEncodingPosition secretKey.parameter target position)
    (hbefore : beforeCache target = none) : afterCache target = none := by
  induction attempts generalizing beforeCache afterCache result with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hbefore
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsampleRun : (randomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [romImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsampleRun
      obtain ⟨sampledRandomness, _, heq⟩ := hsampleRun
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAttempt secretKey message randomness)).run beforeCache) := by
        simpa only [simulateQ_romImpl_liftM] using hattempt
      have hne : target ≠ tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness) := by
        intro heq
        obtain ⟨payload, htarget⟩ := hposition
        have hdomain := (tweakableHashInput_injective secretKey.parameter (by trivial)
          (by trivial) (htarget.symm.trans heq)).1
        cases position
        simp [EncodingPosition.domain] at hdomain
      have hattemptNone : attemptCache target = none :=
        signAttempt_cache_other_none secretKey message randomness beforeCache attemptCache
          attempt hattempt' target hbefore hne
      cases attempt with
      | none => exact ih attemptCache afterCache result hfinish hattemptNone
      | some selected =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hfinish
          obtain ⟨rfl, rfl⟩ := hfinish
          exact hattemptNone

theorem sign_cache_encoding_none_of_digest_eval
    (secretKey : SecretKey) (message : Message) (signature : Signature)
    (beforeCache afterCache : QueryCache HashSpec)
    (hmem : (some signature, afterCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run beforeCache))
    (f : QueryImpl HashSpec Id) (hf : afterCache.AgreesWithFn f)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (hdigest : evalWithAnswerFn f
      (signAttempt secretKey message signature.randomness) = some (index, leaves))
    (target : HashInput) (position : EncodingPosition)
    (hposition : AtEncodingPosition secretKey.parameter target position)
    (hbefore : beforeCache target = none)
    (havoid : target ∉ queriedInputs f
      (signAfterDigest secretKey signature.randomness index leaves)) :
    afterCache target = none := by
  rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hfinish
      cases hfinish.1
  | some selected =>
      obtain ⟨randomness, actualIndex, actualLeaves⟩ := selected
      have hloopNone := signDigestLoop_cache_encoding_none digestAttemptLimit secretKey message
        beforeCache loopCache (some (randomness, actualIndex, actualLeaves)) hloop target
        position hposition hbefore
      have hfinish' : (some signature, afterCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest secretKey randomness actualIndex actualLeaves)).run loopCache) := by
        simpa only [simulateQ_romImpl_liftM] using hfinish
      have hloopLe : loopCache ≤ afterCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAfterDigest secretKey randomness actualIndex actualLeaves) :
            OracleComp OracleWorld (Option Signature)) loopCache _ hfinish
      have hfLoop : loopCache.AgreesWithFn f := fun _ _ hcached => hf (hloopLe hcached)
      have hloopReplay := replayRom_of_mem_support
        (signDigestLoop digestAttemptLimit secretKey message) beforeCache
        (some (randomness, actualIndex, actualLeaves)) loopCache hloop f hfLoop
      have hactualDigest := successfulDigestLoop_of_mem_support f secretKey message
        digestAttemptLimit randomness actualIndex actualLeaves beforeCache loopCache afterCache
        hloopReplay hloopLe hf
      have hrandomness : randomness = signature.randomness :=
        (signAfterDigest_support_some_randomness secretKey randomness actualIndex actualLeaves
          loopCache afterCache signature hfinish').symm
      have hselected : actualIndex = index ∧ actualLeaves = leaves := by
        have hactual := hactualDigest.2.1
        have hexpected := hdigest
        rw [hrandomness] at hactual
        exact Prod.mk.inj (Option.some.inj (hactual.symm.trans hexpected))
      rw [hselected.1, hselected.2] at hfinish'
      subst randomness
      apply cache_eq_none_of_not_mem_queriedInputs
        (signAfterDigest secretKey signature.randomness index leaves) loopCache
        (some signature) afterCache hfinish' f hf target hloopNone
      exact havoid

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

theorem encodingInput_mem_signLayer_otsSign {f : QueryImpl HashSpec Id}
    {secretKey : SecretKey} {index : Index} {lay : Layer} {input : HashInput}
    {position : EncodingPosition} (hposition : AtEncodingPosition secretKey.parameter input position)
    (hinput : input ∈ queriedInputs f (signLayer secretKey index lay)) :
    position = ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩
      ∧ input ∈ queriedInputs f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay))) := by
  obtain ⟨payload, hpayload⟩ := hposition
  rw [signLayer, queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hmessage | hrest
  · exact absurd hmessage (by
      rw [hpayload]
      exact avoidsEncodingQueries_layerMessage f secretKey index lay position payload)
  · rw [queriedInputs_bind] at hrest
    rcases List.mem_append.mp hrest with hots | hafter
    · exact ⟨encodingPosition_eq_of_mem_otsSign ⟨payload, hpayload⟩ hots, hots⟩
    · let signed := evalWithAnswerFn f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay)))
      have havoidAfter : AvoidsEncodingQueries secretKey.parameter f
          (match signed with
          | none => pure none
          | some (counter, values) => do
              let path ← treePath secretKey.parameter lay (treeIndexAt index lay)
                (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay)
              pure (some (counter, values, path))) := by
        cases signed with
        | none => exact AvoidsEncodingQueries.pure secretKey.parameter f _
        | some part =>
            apply AvoidsEncodingQueries.bind
            · exact avoidsEncodingQueries_treePath secretKey.parameter f lay
                (treeIndexAt index lay) (secretKey.otsSecret lay (treeIndexAt index lay))
                (leafIndexAt index lay)
            · exact AvoidsEncodingQueries.pure secretKey.parameter f _
      dsimp only [signed] at havoidAfter
      rw [hpayload] at hafter
      exact (havoidAfter position payload hafter).elim

theorem other_valid_encoding_not_mem_otsSignFrom (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message otherMessage : Digest) (attempts counter : Nat)
    (resultCounter otherCounter : Counter) (values : ChainIndex → Digest)
    (otherCodeword : Encoding)
    (hsign : evalWithAnswerFn f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter) =
        some (resultCounter, values))
    (hother : evalWithAnswerFn f
      (encode parameter lay tree leafIdx otherMessage otherCounter) = some otherCodeword)
    (hne : tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes resultCounter) ≠
      tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes otherMessage ++ counterBytes otherCounter)) :
    tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes otherMessage ++ counterBytes otherCounter) ∉
      queriedInputs f
        (otsSignFrom parameter lay tree leafIdx secret message attempts counter) := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom]
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind] at hsign
      rw [otsSignFrom, queriedInputs_bind]
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hsign
          intro hmem
          rcases List.mem_append.mp hmem with hcurrent | hrest
          · simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash,
              queriedInputs_pure, List.append_nil, List.mem_singleton] at hcurrent
            have hdecodeNone := hencode
            have hdecodeSome := hother
            simp only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
              eval_tweakableHash] at hdecodeNone hdecodeSome
            rw [hcurrent] at hdecodeSome
            rw [hdecodeNone] at hdecodeSome
            simp at hdecodeSome
          · exact ih (counter + 1) hsign hrest
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
            evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hsign
          have hcounter : BitVec.ofNat counterBits counter = resultCounter := hsign.1
          intro hmem
          rcases List.mem_append.mp hmem with hcurrent | hrest
          · simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash,
              queriedInputs_pure, List.append_nil, List.mem_singleton] at hcurrent
            apply hne
            rw [← hcounter]
            exact hcurrent.symm
          · have hstructural : QueriesAtPositions parameter f (do
                let signedValues ← sequenceFin fun chainIdx =>
                  chainWalk parameter lay tree leafIdx chainIdx 0 (codeword chainIdx).val
                    (secret chainIdx)
                pure (some (BitVec.ofNat counterBits counter, signedValues))) := by
              apply QueriesAtPositions.bind
              · apply queriesAtPositions_sequenceFin
                intro chainIdx
                exact queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx 0 _ _
              · exact QueriesAtPositions.pure parameter f _
            obtain ⟨position, payload, hinput⟩ := hstructural _ hrest
            exact (show AtEncodingPosition parameter
              (tweakableHashInput parameter (.encoding lay tree leafIdx)
                (digestBytes otherMessage ++ counterBytes otherCounter))
              ⟨lay, tree, leafIdx⟩ from ⟨_, rfl⟩).not_atPosition position ⟨payload, hinput⟩

theorem other_valid_encoding_not_mem_otsSign (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message otherMessage : Digest)
    (resultCounter otherCounter : Counter) (values : ChainIndex → Digest)
    (otherCodeword : Encoding)
    (hsign : evalWithAnswerFn f (otsSign parameter lay tree leafIdx secret message) =
      some (resultCounter, values))
    (hother : evalWithAnswerFn f
      (encode parameter lay tree leafIdx otherMessage otherCounter) = some otherCodeword)
    (hne : tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes resultCounter) ≠
      tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes otherMessage ++ counterBytes otherCounter)) :
    tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes otherMessage ++ counterBytes otherCounter) ∉
      queriedInputs f (otsSign parameter lay tree leafIdx secret message) := by
  exact other_valid_encoding_not_mem_otsSignFrom f parameter lay tree leafIdx secret message
    otherMessage encodingAttemptLimit 0 resultCounter otherCounter values otherCodeword
    (by simpa only [otsSign] using hsign) hother hne

theorem EncodingCollision.forged_encoding_not_mem_signed_otsSign
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
        (forgedMessage : Digest) (forgedCounter : Counter) (index : Index),
      treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
            (digestBytes forgedMessage ++ counterBytes forgedCounter) ∉
          queriedInputs f
            (otsSign secretKey.parameter lay tree leafIdx
              (secretKey.otsSecret lay tree leafIdx)
              (evalWithAnswerFn f (layerMessage secretKey index lay))) := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, _, _, _, signature, index,
    leaves, _, hforgedOpening, _, _, hrun, hdigest, htree, hleaf, _, _, _, hhit⟩ := hcollision
  obtain ⟨forgedCodeword, hforgedEncode, _, _⟩ := hforgedOpening
  obtain ⟨part, hcounter, _, hlayer⟩ := hrun.layerRun_of_digest hdigest lay
  obtain ⟨hots, _⟩ := hlayer.otsSign_eval_cached
  have hnotMem := other_valid_encoding_not_mem_otsSign f secretKey.parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay)
    (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
    (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage part.1 forgedCounter
    part.2.1 forgedCodeword hots (by simpa only [htree, hleaf] using hforgedEncode) (by
      rw [← hcounter, htree, hleaf]
      exact hhit.1)
  exact ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, index, htree, hleaf,
    by simpa only [htree, hleaf] using hnotMem⟩

theorem EncodingCollision.forged_encoding_not_mem_signLayers
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
        (forgedMessage : Digest) (forgedCounter : Counter) (index : Index),
      treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ ∀ otherLayer : Layer,
          tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
              (digestBytes forgedMessage ++ counterBytes forgedCounter) ∉
            queriedInputs f (signLayer secretKey index otherLayer) := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, _, _, _, _, index, leaves, _,
    hforgedOpening, _, _, hrun, hdigest, htree, hleaf, _, _, _, hhit⟩ := hcollision
  obtain ⟨forgedCodeword, hforgedEncode, _, _⟩ := hforgedOpening
  obtain ⟨part, hcounter, _, hlayer⟩ := hrun.layerRun_of_digest hdigest lay
  obtain ⟨hots, _⟩ := hlayer.otsSign_eval_cached
  have hnotOts := other_valid_encoding_not_mem_otsSign f secretKey.parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay)
    (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
    (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage part.1 forgedCounter
    part.2.1 forgedCodeword hots (by simpa only [htree, hleaf] using hforgedEncode) (by
      rw [← hcounter, htree, hleaf]
      exact hhit.1)
  refine ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, index, htree, hleaf, ?_⟩
  intro otherLayer hmem
  have hlocated := encodingInput_mem_signLayer_otsSign
    (show AtEncodingPosition secretKey.parameter
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes forgedMessage ++ counterBytes forgedCounter)) ⟨lay, tree, leafIdx⟩ from
      ⟨_, rfl⟩) hmem
  have hlayer : lay = otherLayer := congrArg EncodingPosition.lay hlocated.1
  subst otherLayer
  rw [htree, hleaf] at hnotOts
  rw [htree, hleaf] at hlocated
  exact hnotOts hlocated.2

theorem EncodingCollision.forged_encoding_not_mem_signAfterDigest
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
        (forgedMessage : Digest) (forgedCounter : Counter)
        (entry : (request : SignRequest) × SigningSpec.Range request)
        (signature : Signature) (index : Index) (leaves : DigestTree → FtsLeaf),
      entry ∈ signingLog
        ∧ entry.2 = some signature
        ∧ SuccessfulSignRun f cache secretKey entry.1 signature
        ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
        ∧ treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
            (digestBytes forgedMessage ++ counterBytes forgedCounter)) ≠ none
        ∧ tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
            (digestBytes forgedMessage ++ counterBytes forgedCounter) ∉
          queriedInputs f (signAfterDigest secretKey signature.randomness index leaves) := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, _, _, entry, signature, index,
    leaves, hforgedRun, hforgedOpening, hentry, hresponse, hrun, hdigest, htree, hleaf, _, _, _,
    hhit⟩ :=
    hcollision
  obtain ⟨forgedCodeword, hforgedEncode, _, _⟩ := hforgedOpening
  obtain ⟨part, hcounter, _, hlayer⟩ := hrun.layerRun_of_digest hdigest lay
  obtain ⟨hots, _⟩ := hlayer.otsSign_eval_cached
  have hnotOts := other_valid_encoding_not_mem_otsSign f secretKey.parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay)
    (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
    (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage part.1 forgedCounter
    part.2.1 forgedCodeword hots (by simpa only [htree, hleaf] using hforgedEncode) (by
      rw [← hcounter, htree, hleaf]
      exact hhit.1)
  let forgedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
    (digestBytes forgedMessage ++ counterBytes forgedCounter)
  have hnotLayers : ∀ otherLayer : Layer,
      forgedInput ∉ queriedInputs f (signLayer secretKey index otherLayer) := by
    intro otherLayer hmem
    have hlocated := encodingInput_mem_signLayer_otsSign
      (show AtEncodingPosition secretKey.parameter forgedInput ⟨lay, tree, leafIdx⟩ from
        ⟨_, rfl⟩) hmem
    have hlayer : lay = otherLayer := congrArg EncodingPosition.lay hlocated.1
    subst otherLayer
    rw [htree, hleaf] at hnotOts hlocated
    exact hnotOts hlocated.2
  have hnotAfter : forgedInput ∉
      queriedInputs f (signAfterDigest secretKey signature.randomness index leaves) := by
    rw [signAfterDigest, queriedInputs_bind]
    intro hmem
    rcases List.mem_append.mp hmem with hfts | hrest
    · exact avoidsEncodingQueries_ftsOpen secretKey.parameter f index leaves
        (secretKey.ftsSecret index) ⟨lay, tree, leafIdx⟩
          (digestBytes forgedMessage ++ counterBytes forgedCounter) hfts
    · rw [queriedInputs_bind] at hrest
      rcases List.mem_append.mp hrest with hlayers | hfinal
      · exact not_mem_queriedInputs_sequenceFin f (fun otherLayer =>
          signLayer secretKey index otherLayer) forgedInput hnotLayers hlayers
      · split at hfinal <;> simp at hfinal
  exact ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, entry, signature, index, leaves,
    hentry, hresponse, hrun, hdigest, htree, hleaf,
    CachedRun.otsLeaf_encode_cached hforgedRun,
    by simpa only [forgedInput] using hnotAfter⟩

theorem SigningCacheTrace.exists_cacheEntry_of_mem_toSigningLog
    {trace : SigningCacheTrace}
    {entry : (request : SignRequest) × SigningSpec.Range request}
    (hentry : entry ∈ trace.toSigningLog) :
    ∃ cacheEntry : SigningCacheEntry, cacheEntry ∈ trace
      ∧ (⟨cacheEntry.request, cacheEntry.signature⟩ :
        (request : SignRequest) × SigningSpec.Range request) = entry := by
  rw [SigningCacheTrace.toSigningLog, List.mem_map] at hentry
  obtain ⟨cacheEntry, hcacheEntry, heq⟩ := hentry
  exact ⟨cacheEntry, hcacheEntry, heq⟩

theorem EncodingCollision.signingInterval_prehit_or_final_miss
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {trace : SigningCacheTrace} {signingLog : QueryLog SigningSpec}
    (hcollision : EncodingCollision f cache secretKey signingLog)
    (hlog : trace.toSigningLog = signingLog) (hvalid : trace.ValidRuns secretKey)
    (hcaches : trace.CachesLe cache) (hf : cache.AgreesWithFn f) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
        (forgedMessage : Digest) (forgedCounter : Counter)
        (cacheEntry : SigningCacheEntry) (signature : Signature)
        (index : Index),
      cacheEntry ∈ trace
        ∧ cacheEntry.signature = some signature
        ∧ treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ let forgedInput := tweakableHashInput secretKey.parameter
            (.encoding lay tree leafIdx)
            (digestBytes forgedMessage ++ counterBytes forgedCounter)
          cache forgedInput ≠ none ∧
            (cacheEntry.initialCache forgedInput ≠ none ∨
              cacheEntry.finalCache forgedInput = none) := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, entry, signature, index,
    leaves, hentry, hresponse, _, hdigest, htree, hleaf, hforgedCached, havoid⟩ :=
    hcollision.forged_encoding_not_mem_signAfterDigest
  have hentry' : entry ∈ trace.toSigningLog := by rwa [hlog]
  obtain ⟨cacheEntry, hcacheEntry, heq⟩ :=
    SigningCacheTrace.exists_cacheEntry_of_mem_toSigningLog hentry'
  subst entry
  have hfinalLe := (hcaches cacheEntry hcacheEntry).2
  have hfinalAgree : cacheEntry.finalCache.AgreesWithFn f :=
    fun _ _ hcached => hf (hfinalLe hcached)
  let forgedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
    (digestBytes forgedMessage ++ counterBytes forgedCounter)
  have hposition : AtEncodingPosition secretKey.parameter forgedInput ⟨lay, tree, leafIdx⟩ :=
    ⟨_, rfl⟩
  refine ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, cacheEntry, signature, index,
    hcacheEntry, hresponse, htree, hleaf, hforgedCached, ?_⟩
  by_cases hinitial : cacheEntry.initialCache forgedInput = none
  · right
    have hvalidRun := hvalid cacheEntry hcacheEntry
    change cacheEntry.signature = some signature at hresponse
    rw [SigningCacheEntry.ValidRun, hresponse] at hvalidRun
    exact sign_cache_encoding_none_of_digest_eval secretKey cacheEntry.request signature
      cacheEntry.initialCache cacheEntry.finalCache hvalidRun f hfinalAgree index leaves
      hdigest.2.1 forgedInput ⟨lay, tree, leafIdx⟩ hposition hinitial (by
        simpa only [forgedInput] using havoid)
  · exact Or.inl hinitial

theorem EncodingCollision.signingInterval_prehit_or_later_source
    {f : QueryImpl HashSpec Id} {cache rootCache adversaryCache : QueryCache HashSpec}
    {secretKey : SecretKey} {trace : FullAdversaryTrace}
    (hcollision : EncodingCollision f cache secretKey trace.signing.toSigningLog)
    (hvalidRuns : trace.signing.ValidRuns secretKey)
    (hcaches : trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    (hconsistent : trace.Consistent)
    (hchain : FullAdversaryTrace.CacheChain rootCache trace.intervals adversaryCache)
    (hchronological : FullAdversaryTrace.Chronological trace.intervals)
    (hvalidIntervals : trace.ValidIntervals secretKey) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
        (forgedMessage : Digest) (forgedCounter : Counter)
        (cacheEntry : SigningCacheEntry) (signature : Signature) (index : Index)
        (selected : Fin trace.intervals.length),
      cacheEntry ∈ trace.signing
        ∧ cacheEntry.signature = some signature
        ∧ treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ AdversaryCacheEntry.signingEntry? (trace.intervals.get selected) = some cacheEntry
        ∧ let forgedInput := tweakableHashInput secretKey.parameter
            (.encoding lay tree leafIdx)
            (digestBytes forgedMessage ++ counterBytes forgedCounter)
          cache forgedInput ≠ none ∧
            (cacheEntry.initialCache forgedInput ≠ none ∨
              (∃ source : Fin trace.intervals.length,
                selected.val < source.val
                  ∧ (trace.intervals.get source).initialCache forgedInput = none
                  ∧ (trace.intervals.get source).finalCache forgedInput ≠ none) ∨
              (adversaryCache forgedInput = none ∧ cache forgedInput ≠ none)) := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, cacheEntry, signature, index,
    hcacheEntry, hresponse, htree, hleaf, hforgedCached, hcase⟩ :=
    hcollision.signingInterval_prehit_or_final_miss rfl hvalidRuns hcaches hf
  obtain ⟨selected, hselected⟩ :=
    trace.exists_intervalPosition_of_signingEntry hconsistent cacheEntry hcacheEntry
  refine ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, cacheEntry, signature, index,
    selected, hcacheEntry, hresponse, htree, hleaf, hselected, hforgedCached, ?_⟩
  rcases hcase with hprehit | hfinalMiss
  · exact Or.inl hprehit
  · right
    by_cases hadversary : adversaryCache (tweakableHashInput secretKey.parameter
        (.encoding lay tree leafIdx)
        (digestBytes forgedMessage ++ counterBytes forgedCounter)) = none
    · exact Or.inr ⟨hadversary, hforgedCached⟩
    · left
      have hmono : ∀ entry ∈ trace.intervals,
          entry.initialCache ≤ entry.finalCache := by
        intro entry hentry
        exact unloggedMappedAdversaryImpl_cache_le secretKey entry.input entry.initialCache
          (entry.output, entry.finalCache) (hvalidIntervals entry hentry)
      apply hchain.transition_after hchronological hmono selected
      · rwa [(trace.intervals.get selected).finalCache_eq_of_signingEntry?_eq_some hselected]
      · exact hadversary

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
