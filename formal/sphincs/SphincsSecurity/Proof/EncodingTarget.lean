import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingCached
import SphincsSecurity.Proof.OneTimeEvents

/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if lay = topLayer then
    .node middleLayer (treeIndexAt index middleLayer)
      ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middleLayer then
    .node bottomLayer (treeIndexAt index bottomLayer)
      ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else .ftsRoots index

private theorem topLayer_ne_middleLayer : topLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [topLayer, middleLayer] at this

private theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, topLayer, numLayers] at this

private theorem bottomLayer_ne_middleLayer : bottomLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, middleLayer, numLayers] at this

@[simp] theorem layerMessagePosition_top (index : Index) :
    layerMessagePosition index topLayer =
      .node middleLayer (treeIndexAt index middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_pos rfl]

@[simp] theorem layerMessagePosition_middle (index : Index) :
    layerMessagePosition index middleLayer =
      .node bottomLayer (treeIndexAt index bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg topLayer_ne_middleLayer.symm, if_pos rfl]

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  rw [layerMessagePosition, if_neg bottomLayer_ne_topLayer,
    if_neg bottomLayer_ne_middleLayer]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)]
    rw [layerMessagePosition_top, honestValue_node]
    simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)]
    rw [layerMessagePosition_middle, honestValue_node]
    simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl]
    rfl
  · rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

theorem layerMessagePosition_settled_of_cachedRun {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {index : Index} {lay : Layer}
    (hf : cache.AgreesWithFn f)
    (hmessage : CachedRun cache f (layerMessage secretKey index lay)) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (layerMessagePosition index lay) := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)] at hmessage
    rw [layerMessagePosition_top]
    simpa only [
      show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl] using
      settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf middleLayer
        (treeIndexAt index middleLayer) hmessage
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)] at hmessage
    rw [layerMessagePosition_middle]
    simpa only [
      show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl] using
      settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf bottomLayer
        (treeIndexAt index bottomLayer) hmessage
  · rw [layerMessage_bottomLayer secretKey index] at hmessage
    rw [layerMessagePosition_bottom]
    exact settled_ftsRoots_of_cachedRun (otsSecret := secretKey.otsSecret) hf index hmessage

theorem SuccessfulSignRun.layerMessagePosition_settled {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hf : cache.AgreesWithFn f)
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (layerMessagePosition index lay) := by
  exact layerMessagePosition_settled_of_cachedRun hf
    (hrun.honest_layer_at_of_digest hdigest lay).1

theorem layerMessagePosition_eq_of_position_eq (left right : Index) (lay : Layer)
    (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessagePosition left lay = layerMessagePosition right lay := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessagePosition_top, layerMessagePosition_top,
      middleTree_eq_of_top_position_eq left right htree hleaf]
  · rw [layerMessagePosition_middle, layerMessagePosition_middle,
      bottomTree_eq_of_middle_position_eq left right htree hleaf]
  · rw [layerMessagePosition_bottom, layerMessagePosition_bottom,
      index_eq_of_bottom_position_eq htree hleaf]

def SignedEncodingPayloadAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (payload : HashInput) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ payload = digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
        counterBytes (signature.counter lay)

def encodingSearchFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    Nat → Nat → OracleComp HashSpec (Option Counter)
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter) with
      | some _ => pure (some (BitVec.ofNat counterBits counter))
      | none => encodingSearchFrom parameter lay tree leafIdx message attempts (counter + 1)

def encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : OracleComp HashSpec (Option Counter) :=
  encodingSearchFrom parameter lay tree leafIdx message encodingAttemptLimit 0

theorem encodingSearchFrom_selected_mem (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (selected : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearchFrom parameter lay tree leafIdx message attempts counter) = some selected) :
    tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes selected) ∈
      queriedInputs f
        (encodingSearchFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => simp [encodingSearchFrom] at hselected
  | succ attempts ih =>
      rw [encodingSearchFrom, evalWithAnswerFn_bind] at hselected
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hselected
          rw [encodingSearchFrom, queriedInputs_bind]
          apply List.mem_append_right
          simp only [hencode]
          exact ih (counter + 1) hselected
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_pure, Option.some.injEq] at hselected
          subst selected
          rw [encodingSearchFrom, queriedInputs_bind]
          apply List.mem_append_left
          simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash,
            queriedInputs_pure, List.append_nil, List.mem_singleton]

theorem encodingSearch_selected_mem (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (selected : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearch parameter lay tree leafIdx message) = some selected) :
    tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes selected) ∈
      queriedInputs f (encodingSearch parameter lay tree leafIdx message) := by
  exact encodingSearchFrom_selected_mem f parameter lay tree leafIdx message
    encodingAttemptLimit 0 selected (by simpa only [encodingSearch] using hselected)

theorem encodingSearchFrom_selected_encode_ne_none (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (selected : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearchFrom parameter lay tree leafIdx message attempts counter) = some selected) :
    evalWithAnswerFn f (encode parameter lay tree leafIdx message selected) ≠ none := by
  induction attempts generalizing counter with
  | zero => simp [encodingSearchFrom] at hselected
  | succ attempts ih =>
      rw [encodingSearchFrom, evalWithAnswerFn_bind] at hselected
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hselected
          exact ih (counter + 1) hselected
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_pure, Option.some.injEq] at hselected
          subst selected
          rw [hencode]
          simp

theorem encodingSearch_selected_encode_ne_none (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (selected : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearch parameter lay tree leafIdx message) = some selected) :
    evalWithAnswerFn f (encode parameter lay tree leafIdx message selected) ≠ none := by
  exact encodingSearchFrom_selected_encode_ne_none f parameter lay tree leafIdx message
    encodingAttemptLimit 0 selected (by simpa only [encodingSearch] using hselected)

theorem encodingSearchFrom_rejected_before (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (selected : Counter)
    (hbound : counter + attempts ≤ 2 ^ counterBits)
    (hselected : evalWithAnswerFn f
      (encodingSearchFrom parameter lay tree leafIdx message attempts counter) = some selected)
    (candidate : Nat) (hlower : counter ≤ candidate) (hbefore : candidate < selected.toNat) :
    evalWithAnswerFn f
      (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits candidate)) = none := by
  induction attempts generalizing counter candidate with
  | zero => simp [encodingSearchFrom] at hselected
  | succ attempts ih =>
      have hcounterLt : counter < 2 ^ counterBits := by omega
      rw [encodingSearchFrom, evalWithAnswerFn_bind] at hselected
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hselected
          by_cases heq : candidate = counter
          · subst candidate
            exact hencode
          · exact ih (counter + 1) (by omega) hselected candidate (by omega) hbefore
      | some codeword =>
          have hselectedEq : BitVec.ofNat counterBits counter = selected := by
            simpa only [hencode, evalWithAnswerFn_pure, Option.some.injEq] using hselected
          have hselectedNat : selected.toNat = counter := by
            rw [← hselectedEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcounterLt]
          omega

theorem encodingSearch_rejected_before (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (selected candidate : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearch parameter lay tree leafIdx message) = some selected)
    (hbefore : candidate.toNat < selected.toNat) :
    evalWithAnswerFn f (encode parameter lay tree leafIdx message candidate) = none := by
  have hrejected := encodingSearchFrom_rejected_before f parameter lay tree leafIdx message
    encodingAttemptLimit 0 selected (by norm_num [encodingAttemptLimit, counterBits])
    (by simpa only [encodingSearch] using hselected) candidate.toNat (by omega) hbefore
  simpa using hrejected

theorem otsSignFrom_encodingSearchFrom_some_cached (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat) (resultCounter : Counter)
    (values : ChainIndex → Digest)
    (hsign : evalWithAnswerFn f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter) =
        some (resultCounter, values))
    (hrun : CachedRun cache f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter)) :
    evalWithAnswerFn f
        (encodingSearchFrom parameter lay tree leafIdx message attempts counter) =
          some resultCounter
      ∧ CachedRun cache f
        (encodingSearchFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom] at hsign
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind] at hsign
      rw [otsSignFrom] at hrun
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hsign
          have hrest := ih (counter + 1) hsign (by
            have := hrun.bind_right
            simpa only [hencode] using this)
          refine ⟨?_, ?_⟩
          · simp only [encodingSearchFrom, evalWithAnswerFn_bind, hencode]
            exact hrest.1
          · intro input hinput
            rw [encodingSearchFrom, queriedInputs_bind] at hinput
            rcases List.mem_append.mp hinput with hinput | hinput
            · exact hrun.bind_left input hinput
            · simp only [hencode] at hinput
              exact hrest.2 input hinput
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
            evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hsign
          have hcounter : BitVec.ofNat counterBits counter = resultCounter := hsign.1
          subst resultCounter
          refine ⟨?_, ?_⟩
          · simp [encodingSearchFrom, evalWithAnswerFn_bind, hencode]
          · intro input hinput
            rw [encodingSearchFrom, queriedInputs_bind] at hinput
            rcases List.mem_append.mp hinput with hinput | hinput
            · exact hrun.bind_left input hinput
            · simp [hencode] at hinput

theorem otsSign_encodingSearch_some_cached (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (resultCounter : Counter) (values : ChainIndex → Digest)
    (hsign : evalWithAnswerFn f
      (otsSign parameter lay tree leafIdx secret message) = some (resultCounter, values))
    (hrun : CachedRun cache f (otsSign parameter lay tree leafIdx secret message)) :
    evalWithAnswerFn f (encodingSearch parameter lay tree leafIdx message) = some resultCounter
      ∧ CachedRun cache f (encodingSearch parameter lay tree leafIdx message) := by
  simpa only [otsSign, encodingSearch] using
    otsSignFrom_encodingSearchFrom_some_cached f cache parameter lay tree leafIdx secret message
      encodingAttemptLimit 0 resultCounter values hsign hrun

def CachedSignedEncodingPayloadAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (payload : HashInput) : Prop :=
  ∃ (index : Index) (counter : Counter),
    treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index lay)
      ∧ CachedRun cache (fromCache cache)
        (encodingSearch secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (layerMessagePosition index lay)))
      ∧ evalWithAnswerFn (fromCache cache)
        (encodingSearch secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (layerMessagePosition index lay))) = some counter
      ∧ payload = digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index lay)) ++
        counterBytes counter
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) payload) ≠ none

theorem CachedSignedEncodingPayloadAt.target_valid
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex} {payload : HashInput}
    (htarget : CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload) :
    TargetSum.ValidDigest (truncateHash (fromCache cache
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) payload))) := by
  obtain ⟨index, counter, htree, hleaf, _, _, heval, hpayload, _⟩ := htarget
  have hselected := encodingSearch_selected_encode_ne_none (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (layerMessagePosition index lay)) counter heval
  have hvalid := (eval_encode_ne_none_iff_validDigest (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (layerMessagePosition index lay)) counter).mp hselected
  rwa [htree, hleaf, ← hpayload] at hvalid

theorem SignedEncodingPayloadAt.cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex} {payload : HashInput}
    (hf : cache.AgreesWithFn f)
    (hsigned : SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx payload) :
    CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload := by
  obtain ⟨_, signature, index, leaves, _, _, hrun, hdigest, htree, hleaf, hpayload⟩ := hsigned
  obtain ⟨part, hcounter, _, hlayer⟩ := hrun.layerRun_of_digest hdigest lay
  obtain ⟨hotsEval, hotsCached⟩ := hlayer.otsSign_eval_cached
  have hselection := otsSign_encodingSearch_some_cached f cache secretKey.parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay)
    (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
    (evalWithAnswerFn f (layerMessage secretKey index lay)) part.1 part.2.1 hotsEval hotsCached
  have hsettled := hrun.layerMessagePosition_settled hf hdigest lay
  have hmessage : evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
    rw [eval_layerMessage_eq_honestValue]
    exact honestValue_eq_of_settled hf hsettled
  rw [hmessage] at hselection
  have heval := hselection.2.eval_eq hf (agreesWithFn_fromCache cache)
  have htargetCached := hrun.signed_encode_cached_of_digest hdigest lay
  refine ⟨index, part.1, htree, hleaf, hsettled,
    hselection.2.changeAnswerFn hf (agreesWithFn_fromCache cache), ?_, ?_, ?_⟩
  · exact heval.symm.trans hselection.1
  · rw [hpayload, hmessage, hcounter]
  · rw [hpayload]
    rw [htree, hleaf] at htargetCached
    exact htargetCached

theorem CachedSignedEncodingPayloadAt.mono {cache cache' : QueryCache HashSpec}
    {secretKey : SecretKey} {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    {payload : HashInput} (hle : cache ≤ cache')
    (htarget : CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload) :
    CachedSignedEncodingPayloadAt cache' secretKey lay tree leafIdx payload := by
  obtain ⟨index, counter, htree, hleaf, hsettled, hrun, heval, hpayload, hcached⟩ := htarget
  have hagrees : cache.AgreesWithFn (fromCache cache') := agreesWithFn_fromCache_of_le hle
  have hvalue := honestValue_eq_of_settled hagrees hsettled
  rw [← hvalue] at hrun heval
  have hevalEq := hrun.eval_eq (agreesWithFn_fromCache cache) hagrees
  have hrun' := (hrun.changeAnswerFn (agreesWithFn_fromCache cache) hagrees).mono hle
  refine ⟨index, counter, htree, hleaf, hsettled.mono hle, hrun',
    hevalEq.symm.trans heval, ?_, ?_⟩
  · rw [hpayload, hvalue]
  · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
    rw [hle hanswer]
    simp

def EncodingCollisionAtSignedPayload (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (signedPayload forgedPayload : HashInput) (signedAnswer forgedAnswer : HashOutput),
    SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx signedPayload
      ∧ signedPayload ≠ forgedPayload
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload) =
        some signedAnswer
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) forgedPayload) =
        some forgedAnswer
      ∧ truncateHash signedAnswer = truncateHash forgedAnswer

def EncodingBad (cache : QueryCache HashSpec) (secretKey : SecretKey) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (signedPayload otherPayload : HashInput) (signedAnswer otherAnswer : HashOutput),
    CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx signedPayload
      ∧ signedPayload ≠ otherPayload
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload) =
        some signedAnswer
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) otherPayload) =
        some otherAnswer
      ∧ truncateHash signedAnswer = truncateHash otherAnswer

theorem EncodingCollision.at_signed_payload {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    EncodingCollisionAtSignedPayload f cache secretKey signingLog := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, _, entry, signature,
    index, leaves, hforgedRun, _, hentry, hresponse, hrun, hdigest, htree, hleaf, _, _,
    hsignedCached, hhit⟩ := hcollision
  let signedPayload := digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
    counterBytes (signature.counter lay)
  let forgedPayload := digestBytes forgedMessage ++ counterBytes forgedCounter
  let signedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload
  let forgedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) forgedPayload
  obtain ⟨signedAnswer, hsignedAnswer⟩ := Option.ne_none_iff_exists'.mp hsignedCached
  have hforgedCached : cache forgedInput ≠ none :=
    CachedRun.otsLeaf_encode_cached hforgedRun
  obtain ⟨forgedAnswer, hforgedAnswer⟩ := Option.ne_none_iff_exists'.mp hforgedCached
  change signedInput ≠ forgedInput ∧ truncateHash (f signedInput) = truncateHash (f forgedInput)
    at hhit
  refine ⟨lay, tree, leafIdx, signedPayload, forgedPayload, signedAnswer, forgedAnswer,
    ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, rfl⟩,
    ?_, hsignedAnswer, hforgedAnswer, ?_⟩
  · exact fun heq => hhit.1 (congrArg
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)) heq)
  · rw [← hf hsignedAnswer, ← hf hforgedAnswer]
    exact hhit.2

theorem EncodingCollisionAtSignedPayload.encodingBad {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollisionAtSignedPayload f cache secretKey signingLog) :
    EncodingBad cache secretKey := by
  obtain ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned, hne, hsignedCached, hotherCached, hvalue⟩ := hcollision
  exact ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned.cached hf, hne, hsignedCached, hotherCached, hvalue⟩

theorem EncodingCollision.encodingBad {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    EncodingBad cache secretKey :=
  (hcollision.at_signed_payload hf).encodingBad hf

end SphincsSecurity.Concrete
