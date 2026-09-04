import SphincsSecurity.Proof.OneTimeEvents

/-!
# Finite witnesses for the few-time leak

A leak chooses one successful signing entry for each of the fourteen opened trees.  Keeping the
range of that choice as a finset exposes the number of distinct signatures used by the opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev SigningEntry := (request : SignRequest) × SigningSpec.Range request
abbrev FlatSigningEntry := SignRequest × Option Signature

def SigningEntry.flat (entry : SigningEntry) : FlatSigningEntry :=
  (entry.1, entry.2)

structure FtsCoverAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (targetLeaves : DigestTree → FtsLeaf) (tree : FtsTree) where
  entry : SigningEntry
  signature : Signature
  signedLeaves : DigestTree → FtsLeaf
  entry_mem : entry ∈ signingLog
  response_eq : entry.2 = some signature
  successful : SuccessfulSignRun f cache secretKey entry.1 signature
  honest : HonestFtsSignAt f cache secretKey entry.1 signature index signedLeaves
  leaf_eq : signedLeaves (ftsIndexOf tree) = targetLeaves (ftsIndexOf tree)

structure FewTimeCover (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (targetLeaves : DigestTree → FtsLeaf) where
  select : ∀ tree, FtsCoverAt f cache secretKey signingLog index targetLeaves tree

noncomputable def FewTimeLeak.cover {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hleak : FewTimeLeak f cache secretKey signingLog index targetLeaves) :
    FewTimeCover f cache secretKey signingLog index targetLeaves := by
  classical
  refine ⟨fun tree => ?_⟩
  let entry := Classical.choose (hleak tree)
  have hsignatureExists := Classical.choose_spec (hleak tree)
  let signature := Classical.choose hsignatureExists
  have hleavesExists := Classical.choose_spec hsignatureExists
  let signedLeaves := Classical.choose hleavesExists
  have hproperties := Classical.choose_spec hleavesExists
  exact ⟨entry, signature, signedLeaves, hproperties.1, hproperties.2.1,
    hproperties.2.2.1, hproperties.2.2.2.1, hproperties.2.2.2.2⟩

noncomputable def FewTimeCover.entries {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Finset FlatSigningEntry :=
  Finset.univ.image fun tree => (cover.select tree).entry.flat

theorem FewTimeCover.entry_mem_entries {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) (tree : FtsTree) :
    (cover.select tree).entry.flat ∈ cover.entries := by
  classical
  exact Finset.mem_image.2 ⟨tree, Finset.mem_univ _, rfl⟩

theorem FewTimeCover.entries_subset_log {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    ↑cover.entries ⊆ ↑(signingLog.map SigningEntry.flat).toFinset := by
  classical
  intro entry hentry
  obtain ⟨tree, _, rfl⟩ := Finset.mem_image.1 hentry
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨_, (cover.select tree).entry_mem, rfl⟩)

theorem FewTimeCover.entries_card_pos {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    0 < cover.entries.card := by
  classical
  have hmem := cover.entry_mem_entries (⟨0, by decide⟩ : FtsTree)
  exact Finset.card_pos.2 ⟨_, hmem⟩

theorem FewTimeCover.entries_card_le_trees {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.entries.card ≤ ftsTrees - 1 := by
  classical
  calc
    cover.entries.card ≤ (Finset.univ : Finset FtsTree).card := Finset.card_image_le
    _ = ftsTrees - 1 := Fintype.card_fin _

theorem FewTimeCover.entries_card_le_log_length {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.entries.card ≤ signingLog.length := by
  classical
  calc
    cover.entries.card ≤ (signingLog.map SigningEntry.flat).toFinset.card :=
      Finset.card_le_card cover.entries_subset_log
    _ ≤ (signingLog.map SigningEntry.flat).length :=
      List.toFinset_card_le (signingLog.map SigningEntry.flat)
    _ = signingLog.length := List.length_map SigningEntry.flat

theorem FewTimeCover.entries_card_le_signatureLimit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (hvalid : SigningTranscript.Valid signingLog) :
    cover.entries.card ≤ signatureLimit :=
  cover.entries_card_le_log_length.trans hvalid

theorem flatSigningEntry_has_log_index (signingLog : QueryLog SigningSpec)
    (entry : FlatSigningEntry) (hentry : entry ∈ signingLog.map SigningEntry.flat) :
    ∃ position : Fin signingLog.length, SigningEntry.flat (signingLog.get position) = entry := by
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.1 hentry
  obtain ⟨position, hposition⟩ := List.mem_iff_get.1 horiginal
  exact ⟨position, congrArg SigningEntry.flat hposition⟩

theorem List.get_ne_of_lt_idxOf [BEq α] [LawfulBEq α] (list : List α) (value : α)
    (position : Fin list.length) (hlt : position.val < list.idxOf value) :
    list.get position ≠ value := by
  induction list with
  | nil => exact Fin.elim0 position
  | cons head rest ih =>
      obtain ⟨position, hposition⟩ := position
      cases position with
      | zero =>
        intro heq
        have hhead : head = value := by simpa using heq
        subst head
        simp at hlt
      | succ position =>
        cases hbeq : head == value with
        | true =>
          have hhead : head = value := by simpa using hbeq
          subst head
          simp at hlt
        | false =>
          have hhead : head ≠ value := by
            intro heq
            subst head
            simp at hbeq
          have hlt' : position < rest.idxOf value := by
            simpa [List.idxOf_cons_ne rest hhead] using hlt
          simpa using ih ⟨position, by simpa using hposition⟩ hlt'

noncomputable def FewTimeCover.logIndex {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : Fin signingLog.length :=
  ⟨(signingLog.map SigningEntry.flat).idxOf entry.1, by
    simpa only [List.length_map] using List.idxOf_lt_length_iff.2
      (List.mem_toFinset.1 (cover.entries_subset_log entry.2))⟩

theorem FewTimeCover.logIndex_spec {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) :
    SigningEntry.flat (signingLog.get (cover.logIndex entry)) = entry.1 :=
  by
    classical
    have hmem : entry.1 ∈ signingLog.map SigningEntry.flat :=
      List.mem_toFinset.1 (cover.entries_subset_log entry.2)
    have hlt := List.idxOf_lt_length_iff.2 hmem
    let i := (signingLog.map SigningEntry.flat).idxOf entry.1
    have hi : i < signingLog.length := by simpa only [i, List.length_map] using hlt
    have hget : (signingLog.map SigningEntry.flat).get ⟨i, by simpa only [i] using hlt⟩
        = entry.1 := List.idxOf_get _
    have hmap : (signingLog.map SigningEntry.flat).get ⟨i, by simpa only [i] using hlt⟩ =
        SigningEntry.flat (signingLog.get ⟨i, hi⟩) := by simp
    simpa only [FewTimeCover.logIndex, i] using hmap.symm.trans hget

theorem FewTimeCover.logIndex_first {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) (position : Fin signingLog.length)
    (hposition : position.val < (cover.logIndex entry).val) :
    SigningEntry.flat (signingLog.get position) ≠ entry.1 := by
  classical
  let mappedPosition : Fin (signingLog.map SigningEntry.flat).length :=
    ⟨position.val, by simpa only [List.length_map] using position.isLt⟩
  have hlt : mappedPosition.val < (signingLog.map SigningEntry.flat).idxOf entry.1 := by
    simpa only [mappedPosition, FewTimeCover.logIndex] using hposition
  have hne := List.get_ne_of_lt_idxOf
    (signingLog.map SigningEntry.flat) entry.1 mappedPosition hlt
  simpa only [mappedPosition, List.get_eq_getElem, List.getElem_map] using hne

theorem FewTimeCover.logIndex_injective {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Function.Injective cover.logIndex := by
  intro left right heq
  apply Subtype.ext
  have hleft := cover.logIndex_spec left
  have hright := cover.logIndex_spec right
  rw [heq] at hleft
  exact hleft.symm.trans hright

noncomputable def FewTimeCover.logIndices {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Finset (Fin signingLog.length) :=
  Finset.univ.image cover.logIndex

theorem FewTimeCover.logIndices_card {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.logIndices.card = cover.entries.card := by
  classical
  rw [FewTimeCover.logIndices,
    Finset.card_image_of_injective _ cover.logIndex_injective,
    Finset.card_univ, Fintype.card_coe]

noncomputable def FewTimeCover.representativeTree {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : FtsTree :=
  Classical.choose (Finset.mem_image.1 entry.2)

theorem FewTimeCover.representativeTree_spec {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) :
    (cover.select (cover.representativeTree entry)).entry.flat = entry.1 :=
  (Classical.choose_spec (Finset.mem_image.1 entry.2)).2

noncomputable def FewTimeCover.entryDigest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : MessageDigest :=
  Classical.choose (cover.select (cover.representativeTree entry)).honest.1.extract.2

noncomputable def FewTimeCover.entryDigestInput {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : HashInput :=
  let selected := cover.select (cover.representativeTree entry)
  tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root selected.entry.1 selected.signature.randomness)

theorem FewTimeCover.entryDigest_spec {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) :
    let selected := cover.select (cover.representativeTree entry)
    evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root selected.entry.1
        selected.signature.randomness) = cover.entryDigest entry
      ∧ Admissible (cover.entryDigest entry)
      ∧ index = digestIndex (cover.entryDigest entry)
      ∧ selected.signedLeaves = digestLeaves (cover.entryDigest entry) := by
  let selected := cover.select (cover.representativeTree entry)
  have hspec := Classical.choose_spec selected.honest.1.extract.2
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩

noncomputable def FewTimeCover.entryAssignment {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (tree : FtsTree) : cover.entries :=
  ⟨(cover.select tree).entry.flat, cover.entry_mem_entries tree⟩

theorem FewTimeCover.entryDigest_index {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) : digestIndex (cover.entryDigest entry) = index :=
  (cover.entryDigest_spec entry).2.2.1.symm

theorem honestFtsSignAt_index_leaves_unique {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} {leftIndex rightIndex : Index}
    {leftLeaves rightLeaves : DigestTree → FtsLeaf}
    (hleft : HonestFtsSignAt f cache secretKey message signature leftIndex leftLeaves)
    (hright : HonestFtsSignAt f cache secretKey message signature rightIndex rightLeaves) :
    leftIndex = rightIndex ∧ leftLeaves = rightLeaves := by
  have heq := hleft.1.2.1.symm.trans hright.1.2.1
  exact Prod.mk.inj (Option.some.inj heq)

theorem successfulSignRun_signature_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {leftMessage rightMessage : Message} {leftSignature rightSignature : Signature}
    (hleft : SuccessfulSignRun f cache secretKey leftMessage leftSignature)
    (hright : SuccessfulSignRun f cache secretKey rightMessage rightSignature)
    (hmessage : leftMessage = rightMessage)
    (hrandomness : leftSignature.randomness = rightSignature.randomness) :
    leftSignature = rightSignature := by
  obtain ⟨leftIndex, leftLeaves, leftParts, leftDigest, leftSecret, leftPath, leftCounter,
      leftValues, leftAuth, _, leftLayers, _⟩ := hleft
  obtain ⟨rightIndex, rightLeaves, rightParts, rightDigest, rightSecret, rightPath, rightCounter,
      rightValues, rightAuth, _, rightLayers, _⟩ := hright
  have hdigestEval := leftDigest.2.1
  rw [hmessage, hrandomness] at hdigestEval
  have hindexLeaves := Prod.mk.inj (Option.some.inj (hdigestEval.symm.trans rightDigest.2.1))
  have hparts : leftParts = rightParts := by
    funext lay
    have heval := leftLayers lay
    rw [hindexLeaves.1] at heval
    exact Option.some.inj (heval.symm.trans (rightLayers lay))
  have hsecret : leftSignature.ftsSecret = rightSignature.ftsSecret := by
    rw [leftSecret, rightSecret, hindexLeaves.1, hindexLeaves.2]
  have hpath : leftSignature.ftsPath = rightSignature.ftsPath := by
    rw [leftPath, rightPath, hindexLeaves.1, hindexLeaves.2]
  have hcounter : leftSignature.counter = rightSignature.counter := by
    rw [leftCounter, rightCounter, hparts]
  have hvalues : leftSignature.chainValue = rightSignature.chainValue := by
    rw [leftValues, rightValues, hparts]
  have hauth : leftSignature.authPath = rightSignature.authPath := by
    rw [leftAuth, rightAuth, hparts]
  change Signature.mk leftSignature.randomness leftSignature.ftsSecret leftSignature.ftsPath
      leftSignature.counter leftSignature.chainValue leftSignature.authPath =
    Signature.mk rightSignature.randomness rightSignature.ftsSecret rightSignature.ftsPath
      rightSignature.counter rightSignature.chainValue rightSignature.authPath
  rw [Signature.mk.injEq]
  exact ⟨hrandomness, hsecret, hpath, hcounter, hvalues, hauth⟩

theorem FtsCoverAt.signature_eq_of_flat_entry_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf} {leftTree rightTree : FtsTree}
    (left : FtsCoverAt f cache secretKey signingLog index targetLeaves leftTree)
    (right : FtsCoverAt f cache secretKey signingLog index targetLeaves rightTree)
    (hentry : left.entry.flat = right.entry.flat) : left.signature = right.signature := by
  have hresponse := congrArg Prod.snd hentry
  exact Option.some.inj (left.response_eq.symm.trans (hresponse.trans right.response_eq))

theorem FtsCoverAt.signedLeaves_eq_of_flat_entry_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf} {leftTree rightTree : FtsTree}
    (left : FtsCoverAt f cache secretKey signingLog index targetLeaves leftTree)
    (right : FtsCoverAt f cache secretKey signingLog index targetLeaves rightTree)
    (hentry : left.entry.flat = right.entry.flat) :
    left.signedLeaves = right.signedLeaves := by
  have hmessage := congrArg Prod.fst hentry
  have hsignature := left.signature_eq_of_flat_entry_eq right hentry
  change left.entry.1 = right.entry.1 at hmessage
  have heval := left.honest.1.2.1
  rw [hmessage, hsignature] at heval
  have hpairs := Option.some.inj (heval.symm.trans right.honest.1.2.1)
  exact (Prod.mk.inj hpairs).2

theorem FtsCoverAt.bottom_ots_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf} {leftTree rightTree : FtsTree}
    (left : FtsCoverAt f cache secretKey signingLog index targetLeaves leftTree)
    (right : FtsCoverAt f cache secretKey signingLog index targetLeaves rightTree) :
    left.signature.counter bottomLayer = right.signature.counter bottomLayer
      ∧ left.signature.chainValue bottomLayer = right.signature.chainValue bottomLayer := by
  obtain ⟨leftPart, hleftEval, hleftCounter, hleftValues⟩ :=
    left.successful.signature_part_of_digest left.honest.1 bottomLayer
  obtain ⟨rightPart, hrightEval, hrightCounter, hrightValues⟩ :=
    right.successful.signature_part_of_digest right.honest.1 bottomLayer
  have hpart : leftPart = rightPart := Option.some.inj (hleftEval.symm.trans hrightEval)
  subst rightPart
  exact ⟨hleftCounter.trans hrightCounter.symm, hleftValues.trans hrightValues.symm⟩

theorem FtsCoverAt.flat_entry_eq_of_digest_input_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf} {leftTree rightTree : FtsTree}
    (left : FtsCoverAt f cache secretKey signingLog index targetLeaves leftTree)
    (right : FtsCoverAt f cache secretKey signingLog index targetLeaves rightTree)
    (hinput : tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root left.entry.1 left.signature.randomness)
      = tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root right.entry.1 right.signature.randomness)) :
    left.entry.flat = right.entry.flat := by
  have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
    hinput).2
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective secretKey.root hpayload
  have hsignature := successfulSignRun_signature_eq left.successful right.successful
    hmessage hrandomness
  apply Prod.ext
  · exact hmessage
  · simpa only [SigningEntry.flat] using left.response_eq.trans
      ((congrArg some hsignature).trans right.response_eq.symm)

theorem FtsCoverAt.digest_input_ne_of_flat_entry_ne {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf} {leftTree rightTree : FtsTree}
    (left : FtsCoverAt f cache secretKey signingLog index targetLeaves leftTree)
    (right : FtsCoverAt f cache secretKey signingLog index targetLeaves rightTree)
    (hentry : left.entry.flat ≠ right.entry.flat) :
    tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root left.entry.1 left.signature.randomness)
      ≠ tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root right.entry.1 right.signature.randomness) := by
  intro hinput
  exact hentry (left.flat_entry_eq_of_digest_input_eq right hinput)

theorem FewTimeCover.entryDigest_assigned_leaf {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) (tree : FtsTree) :
    digestLeaves (cover.entryDigest (cover.entryAssignment tree)) (ftsIndexOf tree) =
      targetLeaves (ftsIndexOf tree) := by
  let representative := cover.select
    (cover.representativeTree (cover.entryAssignment tree))
  have hflat : representative.entry.flat = (cover.select tree).entry.flat :=
    cover.representativeTree_spec (cover.entryAssignment tree)
  have hleaves := representative.signedLeaves_eq_of_flat_entry_eq (cover.select tree) hflat
  rw [← (cover.entryDigest_spec (cover.entryAssignment tree)).2.2.2]
  rw [congrFun hleaves (ftsIndexOf tree), (cover.select tree).leaf_eq]

theorem FewTimeCover.entryDigestInput_injective {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Function.Injective cover.entryDigestInput := by
  intro left right hinput
  let leftSelected := cover.select (cover.representativeTree left)
  let rightSelected := cover.select (cover.representativeTree right)
  have hflat : leftSelected.entry.flat = rightSelected.entry.flat :=
    leftSelected.flat_entry_eq_of_digest_input_eq rightSelected hinput
  apply Subtype.ext
  rw [← cover.representativeTree_spec left, ← cover.representativeTree_spec right]
  exact hflat

theorem digestTree_eq_ftsIndexOf_or_last (tree : DigestTree) :
    (∃ ftsTree : FtsTree, tree = ftsIndexOf ftsTree) ∨ tree = lastDigestTree := by
  by_cases htree : tree.val < ftsTrees - 1
  · left
    let ftsTree : FtsTree := ⟨tree.val, htree⟩
    refine ⟨ftsTree, Fin.ext ?_⟩
    rfl
  · right
    apply Fin.ext
    change tree.val = 14
    change ¬ tree.val < 14 at htree
    have hlt := tree.isLt
    change tree.val < 15 at hlt
    omega

theorem HonestFtsSignAt.last_leaf_eq_zero {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} {index : Index} {leaves : DigestTree → FtsLeaf}
    (hhonest : HonestFtsSignAt f cache secretKey message signature index leaves) :
    leaves lastDigestTree = 0 := by
  obtain ⟨_, digest, _, hadmissible, _, hleaves, _⟩ := hhonest.1.extract
  rw [hleaves, hadmissible]

theorem ProperFewTimeLeak.forged_digest_input_ne_entryDigestInput
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index targetLeaves)
    (forgery : Forgery) (forgedDigest : MessageDigest)
    (hforgedDigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness) = forgedDigest)
    (hleaves : targetLeaves = digestLeaves forgedDigest)
    (entry : hproper.1.cover.entries) :
    tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root forgery.message forgery.signature.randomness)
      ≠ hproper.1.cover.entryDigestInput entry := by
  intro hinput
  let cover := hproper.1.cover
  let selected := cover.select (cover.representativeTree entry)
  have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
    hinput).2
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective secretKey.root hpayload
  have hdigest : cover.entryDigest entry = forgedDigest := by
    have hentryDigest := (cover.entryDigest_spec entry).1
    rw [hmessage, hrandomness] at hforgedDigest
    exact hentryDigest.symm.trans hforgedDigest
  have hsignedLeaves : selected.signedLeaves = targetLeaves := by
    calc
      selected.signedLeaves = digestLeaves (cover.entryDigest entry) :=
        (cover.entryDigest_spec entry).2.2.2
      _ = digestLeaves forgedDigest := by rw [hdigest]
      _ = targetLeaves := hleaves.symm
  apply hproper.2 selected.entry selected.signature selected.entry_mem selected.response_eq
    selected.successful
  simpa only [hsignedLeaves] using selected.honest

theorem ProperFewTimeLeak.two_le_cover_entries_card {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index targetLeaves)
    (htargetLast : targetLeaves lastDigestTree = 0) :
    2 ≤ hproper.1.cover.entries.card := by
  classical
  let cover := hproper.1.cover
  change 2 ≤ cover.entries.card
  by_contra hcard
  have hcardOne : cover.entries.card = 1 := by
    have hpos := cover.entries_card_pos
    omega
  let baseTree : FtsTree := ⟨0, by decide⟩
  let base := cover.select baseTree
  have hentryEq : ∀ tree, (cover.select tree).entry.flat = base.entry.flat := by
    intro tree
    apply Finset.card_le_one_iff.1 (Nat.le_of_eq hcardOne)
    · exact cover.entry_mem_entries tree
    · exact cover.entry_mem_entries baseTree
  have hleaves : base.signedLeaves = targetLeaves := by
    funext digestTree
    rcases digestTree_eq_ftsIndexOf_or_last digestTree with ⟨tree, rfl⟩ | rfl
    · have hselected :=
        (cover.select tree).signedLeaves_eq_of_flat_entry_eq base (hentryEq tree)
      rw [← (cover.select tree).leaf_eq]
      exact congrFun hselected (ftsIndexOf tree) |>.symm
    · exact base.honest.last_leaf_eq_zero.trans htargetLast.symm
  have hhonest : HonestFtsSignAt f cache secretKey base.entry.1 base.signature index
      targetLeaves := by
    simpa only [hleaves] using base.honest
  exact hproper.2 base.entry base.signature base.entry_mem base.response_eq base.successful hhonest

end SphincsSecurity.Concrete
