import SphincsSecurity.Proof.ForgeryClassify

/-!
# Replay and message-digest collisions

If one signing entry has the forgery's complete admissible digest, a fully honest opening is the
returned signature unless the two distinct message-digest inputs have the same answer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def MessageDigestCollision (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ CachedRun cache f (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness)
      ∧ tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root entry.1 signature.randomness)
        ≠ tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root forgery.message forgery.signature.randomness)
      ∧ evalWithAnswerFn f
          (messageDigest secretKey.parameter secretKey.root entry.1 signature.randomness)
        = evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root forgery.message
            forgery.signature.randomness)

def ProperFewTimeLeak (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) : Prop :=
  FewTimeLeak f cache secretKey signingLog index leaves
    ∧ ∀ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature),
      entry ∈ signingLog → entry.2 = some signature →
      SuccessfulSignRun f cache secretKey entry.1 signature →
      ¬ HonestFtsSignAt f cache secretKey entry.1 signature index leaves

theorem messageDigestPayload_injective (root : Digest) {leftMessage rightMessage : Message}
    {leftRandomness rightRandomness : Randomness}
    (h : messageDigestPayload root leftMessage leftRandomness
      = messageDigestPayload root rightMessage rightRandomness) :
    leftMessage = rightMessage ∧ leftRandomness = rightRandomness := by
  simp only [messageDigestPayload] at h
  obtain ⟨hrandomness, hrest⟩ := List.append_inj h (by simp [randomnessBytes, bytesLE_length])
  have hrandomness' := List.append_cancel_right hrandomness
  exact ⟨bytesLE_injective hrest, bytesLE_injective hrandomness'⟩

theorem fullyHonest_layers_exact_or_obstacle (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (signingLog : QueryLog SigningSpec)
    (forgery : Forgery) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hfull : FullyHonestOpening f cache secretKey index leaves forgery.signature)
    (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
    (hentry : entry ∈ signingLog) (hresponse : entry.2 = some signature)
    (hrun : SuccessfulSignRun f cache secretKey entry.1 signature)
    (hsignedFts : HonestFtsSignAt f cache secretKey entry.1 signature index leaves) :
    (∀ lay,
        signature.counter lay = forgery.signature.counter lay
          ∧ signature.chainValue lay = forgery.signature.chainValue lay
          ∧ ∀ level, level < layerHeight lay →
            signaturePath signature lay level = signaturePath forgery.signature lay level)
      ∨ ForgedLayerObstacle f cache secretKey signingLog index forgery.signature := by
  by_cases hobstacle : ForgedLayerObstacle f cache secretKey signingLog index forgery.signature
  · exact Or.inr hobstacle
  · left
    intro lay
    obtain ⟨hsignedMessage, hsignedOpening⟩ :=
      hrun.honest_layer_at_of_digest hsignedFts.1 lay
    have hsignedEncoding := hrun.signed_encode_cached_of_digest hsignedFts.1 lay
    rcases honestLayerOpening_compare f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay))
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (forgery.signature.counter lay) (signature.chainValue lay)
        (forgery.signature.chainValue lay) (signaturePath signature lay)
        (signaturePath forgery.signature lay) hsignedOpening (hfull.1 lay).1 with
      hexact | hencoding | hearlier
    · exact ⟨hexact.2.1, hexact.2.2.1, hexact.2.2.2⟩
    · exact (hobstacle ⟨lay, evalWithAnswerFn f (layerMessage secretKey index lay),
        (hfull.1 lay).1, (hfull.1 lay).2,
        Or.inr ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hsignedFts.1,
          rfl, rfl, hsignedMessage, hsignedOpening, hsignedEncoding, Or.inl hencoding⟩⟩).elim
    · exact (hobstacle ⟨lay, evalWithAnswerFn f (layerMessage secretKey index lay),
        (hfull.1 lay).1, (hfull.1 lay).2,
        Or.inr ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hsignedFts.1,
          rfl, rfl, hsignedMessage, hsignedOpening, hsignedEncoding, Or.inr hearlier⟩⟩).elim

theorem fullyHonest_replay_or_digestCollision (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (signingLog : QueryLog SigningSpec)
    (forgery : Forgery) (forgedDigest : MessageDigest) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hforgedDigest : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root
      forgery.message forgery.signature.randomness) = forgedDigest)
    (hforgedRun : CachedRun cache f (messageDigest secretKey.parameter secretKey.root
      forgery.message forgery.signature.randomness))
    (hindex : index = digestIndex forgedDigest) (hleaves : leaves = digestLeaves forgedDigest)
    (hfull : FullyHonestOpening f cache secretKey index leaves forgery.signature)
    (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
    (hentry : entry ∈ signingLog) (hresponse : entry.2 = some signature)
    (hrun : SuccessfulSignRun f cache secretKey entry.1 signature)
    (hsignedFts : HonestFtsSignAt f cache secretKey entry.1 signature index leaves) :
    SigningTranscript.Contains signingLog forgery
      ∨ MessageDigestCollision f cache secretKey signingLog forgery
      ∨ ForgedLayerObstacle f cache secretKey signingLog index forgery.signature := by
  obtain ⟨_, signedDigest, hsignedDigest, _, hsignedIndex, hsignedLeaves, _⟩ :=
    hsignedFts.1.extract
  have hdigest : signedDigest = forgedDigest := by
    apply messageDigest_eq_of_index_leaves_eq
    · rw [← hsignedIndex, hindex]
    · rw [← hsignedLeaves, hleaves]
  let signedInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root entry.1 signature.randomness)
  let forgedInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root forgery.message forgery.signature.randomness)
  by_cases hinput : signedInput = forgedInput
  · have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
      hinput).2
    obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective secretKey.root hpayload
    by_cases hobstacle : ForgedLayerObstacle f cache secretKey signingLog index forgery.signature
    · exact Or.inr (Or.inr hobstacle)
    have hlayers := (fullyHonest_layers_exact_or_obstacle f cache secretKey signingLog forgery
      index leaves hfull entry signature hentry hresponse hrun hsignedFts).resolve_right hobstacle
    have hftsSecret : signature.ftsSecret = forgery.signature.ftsSecret := by
      funext tree
      rw [congrFun hsignedFts.2.1 tree, (hfull.2.1 tree).1]
    have hftsPath : signature.ftsPath = forgery.signature.ftsPath := by
      funext tree level
      rw [congrFun (congrFun hsignedFts.2.2 tree) level]
      exact (hfull.2.1 tree).2 level.val level.isLt |>.symm
    have hcounter : signature.counter = forgery.signature.counter := by
      funext lay
      exact (hlayers lay).1
    have hchainValue : signature.chainValue = forgery.signature.chainValue := by
      funext lay
      exact (hlayers lay).2.1
    have hauthPath : signature.authPath = forgery.signature.authPath := by
      funext position
      obtain ⟨lay, level, hlevel, hposition⟩ := authPath_exhausted position
      have hpath := (hlayers lay).2.2 level.val hlevel
      have hsum : heightAbove lay + level.val < totalHeight := by
        rw [hposition]
        exact position.isLt
      simp only [signaturePath, dif_pos hsum] at hpath
      have hfin : (⟨heightAbove lay + level.val, hsum⟩ : PathIndex) = position :=
        Fin.ext hposition
      simpa only [hfin] using hpath
    have hsignature : signature = forgery.signature := by
      change Signature.mk signature.randomness signature.ftsSecret signature.ftsPath
        signature.counter signature.chainValue signature.authPath =
        Signature.mk forgery.signature.randomness forgery.signature.ftsSecret
          forgery.signature.ftsPath forgery.signature.counter forgery.signature.chainValue
          forgery.signature.authPath
      rw [Signature.mk.injEq]
      exact ⟨hrandomness, hftsSecret, hftsPath, hcounter, hchainValue, hauthPath⟩
    left
    exact ⟨entry, hentry, hmessage, hresponse.trans (congrArg some hsignature)⟩
  · right
    left
    exact ⟨entry, signature, hentry, hresponse, hrun, hforgedRun, hinput,
      hsignedDigest.trans (hdigest.trans hforgedDigest.symm)⟩

theorem fullyHonest_leak_classify (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (forgery : Forgery)
    (forgedDigest : MessageDigest) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hforgedDigest : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root
      forgery.message forgery.signature.randomness) = forgedDigest)
    (hforgedRun : CachedRun cache f (messageDigest secretKey.parameter secretKey.root
      forgery.message forgery.signature.randomness))
    (hindex : index = digestIndex forgedDigest) (hleaves : leaves = digestLeaves forgedDigest)
    (hfull : FullyHonestOpening f cache secretKey index leaves forgery.signature)
    (hnotContains : ¬ SigningTranscript.Contains signingLog forgery)
    (hleak : FewTimeLeak f cache secretKey signingLog index leaves) :
    MessageDigestCollision f cache secretKey signingLog forgery
      ∨ ForgedLayerObstacle f cache secretKey signingLog index forgery.signature
      ∨ ProperFewTimeLeak f cache secretKey signingLog index leaves := by
  by_cases hfullEntry : ∃ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature),
    entry ∈ signingLog ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ HonestFtsSignAt f cache secretKey entry.1 signature index leaves
  · obtain ⟨entry, signature, hentry, hresponse, hrun, hsignedFts⟩ := hfullEntry
    rcases fullyHonest_replay_or_digestCollision f cache secretKey signingLog forgery
        forgedDigest index leaves hforgedDigest hforgedRun hindex hleaves hfull entry signature hentry
        hresponse hrun hsignedFts with hreplay | hcollision | hobstacle
    · exact (hnotContains hreplay).elim
    · exact Or.inl hcollision
    · exact Or.inr (Or.inl hobstacle)
  · right
    right
    refine ⟨hleak, ?_⟩
    intro entry signature hentry hresponse hrun hsignedFts
    exact hfullEntry ⟨entry, signature, hentry, hresponse, hrun, hsignedFts⟩

end SphincsSecurity.Concrete
