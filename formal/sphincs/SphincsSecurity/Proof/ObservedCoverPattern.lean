import SphincsSecurity.Proof.ObservedMessagePatterns
import SphincsSecurity.Proof.FewTimeUsedPatterns

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedSigningView? (answers : HashInput → Option HashOutput) (root : Digest) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  let answer ← answers (messageDigestPayload root entry.1 signature.randomness)
  pure (hashOutputFewTimeView answer)

def observedSigningViews (answers : HashInput → Option HashOutput) (root : Digest) (log : QueryLog SigningSpec) : Fin log.length → FewTimeView :=
  fun slot => (observedSigningView? answers root (log.get slot)).getD default

theorem observedSigningView?_eq_some {answers : HashInput → Option HashOutput} {root : Digest}
    {entry : SigningEntry} {signature : Signature} {digest : MessageDigest}
    (hresponse : entry.2 = some signature) (hdigest : ObservedMessageDigest answers root entry.1 signature.randomness digest) :
    observedSigningView? answers root entry = some (fewTimeTargetView (digestIndex digest) (digestLeaves digest)) := by
  obtain ⟨answer, hanswer, htruncate⟩ := hdigest
  simp [observedSigningView?, hresponse, hanswer, hashOutputFewTimeView, htruncate, fewTimeTargetView]

theorem observedFewTimeCover_has_usedPattern {answers : HashInput → Option HashOutput} {root : Digest}
    {log : QueryLog SigningSpec} {forgery : Forgery}
    (hcover : ObservedFewTimeCover answers root log forgery) :
    ∃ digest, ObservedMessageDigest answers root forgery.message forgery.signature.randomness digest ∧ Admissible digest ∧
      ∃ distinct ∈ Finset.Icc 1 14, ∃ pattern : UsedFewTimePattern log.length distinct,
        pattern.1.Hit (observedSigningViews answers root log, fewTimeTargetView (digestIndex digest) (digestLeaves digest)) ∧
        ∀ selected ∈ pattern.1.selected, ∃ (signature : Signature) (signedDigest : MessageDigest),
          (log.get selected).2 = some signature ∧ Admissible signedDigest ∧
          ObservedMessageDigest answers root (log.get selected).1 signature.randomness signedDigest ∧
          messageDigestPayload root (log.get selected).1 signature.randomness ≠
            messageDigestPayload root forgery.message forgery.signature.randomness := by
  obtain ⟨digest, htarget, hadmissible, hcover⟩ := hcover
  have hslots : ∀ tree : FtsTree, ∃ (slot : Fin log.length) (signature : Signature) (signedDigest : MessageDigest),
      (log.get slot).2 = some signature ∧ Admissible signedDigest ∧
        ObservedMessageDigest answers root (log.get slot).1 signature.randomness signedDigest ∧
        messageDigestPayload root (log.get slot).1 signature.randomness ≠ messageDigestPayload root forgery.message forgery.signature.randomness ∧
        digestIndex signedDigest = digestIndex digest ∧
        digestLeaves signedDigest (ftsIndexOf tree) = digestLeaves digest (ftsIndexOf tree) := by
    intro tree
    obtain ⟨entry, signature, signedDigest, hentry, hrest⟩ := hcover tree
    obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
    exact ⟨slot, signature, signedDigest, hslot ▸ hrest⟩
  choose slot signature signedDigest hresponse hsignedAdmissible hsigned hne hindex hleaf using hslots
  let selected : Finset (Fin log.length) := Finset.univ.image slot
  let assignment : FtsTree → selected := fun tree => ⟨slot tree, Finset.mem_image.mpr ⟨tree, Finset.mem_univ _, rfl⟩⟩
  let pattern : FewTimePattern log.length selected.card := ⟨selected, rfl, assignment⟩
  have hsurjective : Function.Surjective pattern.assignment := by
    intro entry
    obtain ⟨tree, _, htree⟩ := Finset.mem_image.mp entry.2
    exact ⟨tree, Subtype.ext htree⟩
  have hpos : 1 ≤ selected.card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    exact ⟨slot (⟨0, by decide⟩ : FtsTree), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hle : selected.card ≤ 14 := by
    calc
      _ ≤ (Finset.univ : Finset FtsTree).card := Finset.card_image_le
      _ = 14 := by simp [FtsTree, ftsTrees]
  have hview (tree : FtsTree) : observedSigningViews answers root log (slot tree) =
      fewTimeTargetView (digestIndex (signedDigest tree)) (digestLeaves (signedDigest tree)) := by
    simp only [observedSigningViews, observedSigningView?_eq_some (hresponse tree) (hsigned tree), Option.getD_some]
  refine ⟨digest, htarget, hadmissible, selected.card, Finset.mem_Icc.mpr ⟨hpos, hle⟩, ⟨pattern, hsurjective⟩, ?_, ?_⟩
  · constructor
    · intro entry
      obtain ⟨tree, _, htree⟩ := Finset.mem_image.mp entry.2
      change (observedSigningViews answers root log entry.1).1 = digestIndex digest
      rw [← htree, hview]
      exact hindex tree
    · intro tree
      change digestLeaves digest (ftsIndexOf tree) = (observedSigningViews answers root log (slot tree)).2 tree
      rw [hview]
      exact (hleaf tree).symm
  · intro entry hentry
    obtain ⟨tree, _, htree⟩ := Finset.mem_image.mp hentry
    rw [← htree]
    exact ⟨signature tree, signedDigest tree, hresponse tree, hsignedAdmissible tree, hsigned tree, hne tree⟩

end SphincsSecurity.Concrete
