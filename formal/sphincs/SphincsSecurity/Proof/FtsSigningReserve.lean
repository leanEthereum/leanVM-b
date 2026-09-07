import SphincsSecurity.Proof.PreExceptionSurvivalCost
import SphincsSecurity.Proof.SigningEncodingReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem tweakableHashInput_tag_eq (parameter : PublicParameter) (first second : HashDomain)
    (firstPayload secondPayload : HashInput)
    (heq : tweakableHashInput parameter first firstPayload = tweakableHashInput parameter second secondPayload) :
    (hashDomainFields first).tag = (hashDomainFields second).tag := by
  simp only [tweakableHashInput] at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact congrArg TweakFields.tag (tweakBytes_eq_iff.mp htweak)

theorem nonMessageNonEncodingHashCharge_eq_one_of_tag (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (domain : HashDomain) (payload : HashInput) (hmessage : (hashDomainFields domain).tag ≠ 9#8)
    (hencoding : (hashDomainFields domain).tag ≠ 4#8) :
    nonMessageNonEncodingHashCharge parameter cache (tweakableHashInput parameter domain payload) = 1 := by
  have hm : ¬ MessageHashInput parameter (tweakableHashInput parameter domain payload) := by
    rintro ⟨messagePayload, heq⟩
    exact hmessage (tweakableHashInput_tag_eq parameter domain .message payload messagePayload heq.symm)
  have he : ¬ ∃ position : EncodingPosition, AtEncodingPosition parameter (tweakableHashInput parameter domain payload) position := by
    rintro ⟨position, otherPayload, heq⟩
    exact hencoding (tweakableHashInput_tag_eq parameter domain position.domain payload otherPayload heq)
  simp only [nonMessageNonEncodingHashCharge, if_neg hm, if_neg he]

theorem preExceptionSurvivalCost_reserved_tweakableHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (hmessage : (hashDomainFields domain).tag ≠ 9#8)
    (hencoding : (hashDomainFields domain).tag ≠ 4#8) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (tweakableHash parameter domain payload : OracleComp HashSpec Digest)) 1 := by
  change PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput parameter domain payload)))) >>= fun output => pure (truncateHash output)) 1
  apply preExceptionSurvivalCost_bind _ _ _ _ 1 0
  · apply preExceptionSurvivalCost_hash
    intro cache
    rw [nonMessageNonEncodingHashCharge_eq_one_of_tag parameter cache domain payload hmessage hencoding]
  · intro output
    exact preExceptionSurvivalCost_zero _ _ _

theorem preExceptionSurvivalCost_lift_sequenceFin
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, PreExceptionSurvivalCost exception charge (liftM (computation i)) (cost i)) :
    PreExceptionSurvivalCost exception charge (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact preExceptionSurvivalCost_zero _ _ _
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind, ← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact preExceptionSurvivalCost_zero _ _ _

theorem preExceptionSurvivalCost_reserved_ftsNode
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest)) (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact preExceptionSurvivalCost_reserved_tweakableHash exception parameter (.ftsLeaf index tree (ftsLeafOfNat nodeIdx))
        (digestBytes (secret (ftsLeafOfNat nodeIdx))) (by simp [hashDomainFields]) (by simp [hashDomainFields])
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (ih _)
      intro right
      exact preExceptionSurvivalCost_reserved_tweakableHash exception parameter (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right) (by simp [hashDomainFields]) (by simp [hashDomainFields])

theorem preExceptionSurvivalCost_reserved_ftsOpen
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _))
      (∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1)) := by
  unfold ftsOpen
  apply preExceptionSurvivalCost_lift_sequenceFin
  intro tree
  apply preExceptionSurvivalCost_lift_sequenceFin
  intro level
  exact preExceptionSurvivalCost_reserved_ftsNode _ _ _ _ _ _ _

theorem expected_reserved_ftsOpen_ge_survival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest)
    (cache : QueryCache HashSpec) (hit : Bool) :
    (28504 : ENNReal) * Pr[fun result => result.2 = false |
      runExceptionMonitor exception (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _)) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge parameter)
        (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _)) cache hit := by
  apply le_trans ?_ (preExceptionSurvivalCost_reserved_ftsOpen exception parameter index leaves secret cache hit)
  apply mul_le_mul' _ le_rfl
  exact_mod_cast (show 28504 ≤ ∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1) from by decide)

end SphincsSecurity.Concrete.FtsProbeSimulation
