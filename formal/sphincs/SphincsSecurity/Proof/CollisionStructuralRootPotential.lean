import SphincsSecurity.Proof.CollisionStructuralPotential
import SphincsSecurity.Proof.RootStructuralCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition
set_option backward.isDefEq.respectTransparency false

theorem collisionParentStoppedEncodingQueryCharge_eq_of_not_atEncoding
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hnot : ¬ ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position) :
    collisionParentStoppedEncodingQueryCharge key cache input = parentStoppedEncodingQueryCharge key cache input := by
  unfold collisionParentStoppedEncodingQueryCharge encodingPairIncrementCharge
  rw [if_neg hnot, add_zero]
  unfold collisionParentStoppedEncodingBaseCharge parentStoppedEncodingQueryCharge
  by_cases hfresh : cache input = none
  · rw [if_pos hfresh, if_pos hfresh, if_neg hnot, dif_neg hnot]
  · rw [if_neg hfresh, if_neg hfresh]

theorem collisionStructuralCharge_eq_zero_at_supported_honest_query
    (key : SecretKey) (computation : OracleComp HashSpec α)
    (hsettling : ∀ f, SettlingRun key.parameter key.otsSecret key.ftsSecret f computation)
    (hhonest : ∀ f, HonestStructuralQueries key.parameter key.otsSecret key.ftsSecret f computation)
    (ordinal : Nat) (initialCache cache : QueryCache HashSpec)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (hcut : (.query input next, cache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache)) :
    collisionSigningStructuralCharge key cache input = 0 := by
  let f := fromCache cache
  have hprefix := replay_of_mem_support _ _ _ _ hcut f (agreesWithFn_fromCache cache)
  have hget := queriedInputs_getElem_of_eval_hashQueryCutAt f computation ordinal input next hprefix.2.1
  obtain ⟨position, _, hinput⟩ := hhonest f input (List.mem_of_getElem? hget)
  have hnot : ¬ ∃ encoding : EncodingPosition, AtEncodingPosition key.parameter input encoding := by
    rintro ⟨encoding, he⟩
    exact he.not_atPosition position ⟨_, hinput⟩
  rw [collisionSigningStructuralCharge, collisionParentStoppedEncodingQueryCharge_eq_of_not_atEncoding key cache input hnot]
  exact structuralCharge_eq_zero_at_supported_honest_query key computation hsettling hhonest ordinal initialCache cache input next hcut

theorem expectedQueryCharge_collision_treeRoot_eq_zero
    (key : SecretKey) (lay : Layer) (tree : TreeIndex) (cache : QueryCache HashSpec) :
    expectedQueryCharge (collisionSigningStructuralCharge key)
      (liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache = 0 := by
  apply expectedQueryCharge_lift_eq_zero_of_supported_cuts
  intro ordinal middleCache input next hcut
  exact collisionStructuralCharge_eq_zero_at_supported_honest_query key _
    (fun f => settlingRun_treeRoot key.parameter key.otsSecret key.ftsSecret f lay tree)
    (fun f => honestStructuralQueries_treeRoot key.parameter key.otsSecret key.ftsSecret f lay tree)
    ordinal cache middleCache input next hcut

theorem expectedPreExceptionCharge_collision_treeRoot_eq_zero
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (lay : Layer) (tree : TreeIndex) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (collisionSigningStructuralCharge key)
      (liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache hit = 0 := by
  apply le_antisymm _ bot_le
  exact (expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit).trans_eq
    (expectedQueryCharge_collision_treeRoot_eq_zero key lay tree cache)

theorem collisionStructuralRecordPotential_root_irrel
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (left right : Digest)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    collisionStructuralRecordPotential ⟨parameter, left, otsSecret, ftsSecret⟩ cache saved =
      collisionStructuralRecordPotential ⟨parameter, right, otsSecret, ftsSecret⟩ cache saved := rfl

theorem collisionStructuralRecordPotential_empty (key : SecretKey) : collisionStructuralRecordPotential key ∅ none = 0 := by
  simp [collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential, collisionAnswerEncodingAdaptivePotential_eq finite_empty,
    ftsParentSelectionPotential, firstExceptionSelectionPotential, parentReserve_empty]

theorem collisionStructuralRecordPotential_treeRoot_eq_zero
    (key : SecretKey) (lay : Layer) (tree : TreeIndex) (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl
      (liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)).run ∅)) :
    collisionStructuralRecordPotential key result.2 none = 0 := by
  let computation : OracleComp OracleWorld Digest := liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest)
  let exception := CleanParentSettlement key.parameter key.otsSecret key.ftsSecret
  have h := expected_collisionStructuralRecordPotential_le_preCharge key computation ∅ finite_empty none
  have hz := expectedPreExceptionCharge_collision_treeRoot_eq_zero key exception lay tree ∅ false
  change expectedPreExceptionCharge exception (collisionSigningStructuralCharge key) computation ∅ false = 0 at hz
  rw [collisionStructuralRecordPotential_empty, Option.isSome_none, hz, zero_mul, zero_add] at h
  have hzero := le_antisymm h zero_le
  rw [← runFirstException_project exception computation ∅ none, support_map] at hresult
  obtain ⟨recorded, hr, hproject⟩ := hresult
  have hnone := runFirstException_treeRoot_no_record key exception (fun _ _ _ h => h.2) lay tree hr
  have hterm := (ENNReal.tsum_eq_zero.mp hzero) recorded
  have hp := (mul_eq_zero.mp hterm).resolve_left (probOutput_ne_zero_of_mem_support hr)
  rw [← hproject, ← hnone]
  exact hp

end SphincsSecurity.Concrete
