import SphincsSecurity.Proof.MessageAdmissibleDeficit

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

def MessageInputFor (parameter : PublicParameter) (root : Digest) (input : HashInput) (message : Message) : Prop :=
  ∃ randomness, input = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)

theorem MessageInputFor.unique {parameter : PublicParameter} {root : Digest} {input : HashInput}
    {left right : Message} (hleft : MessageInputFor parameter root input left)
    (hright : MessageInputFor parameter root input right) : left = right := by
  obtain ⟨leftRandomness, hleft⟩ := hleft
  obtain ⟨rightRandomness, hright⟩ := hright
  exact (Concrete.messageDigestPayload_injective root
    (tweakableHashInput_injective parameter (by trivial) (by trivial) (hleft.symm.trans hright)).2).1

theorem cachedMessageEntryCount_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cachedMessageEntryCount cache parameter root message ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCount_le_enncard cache parameter root message)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

theorem cachedMessageEntryCountWhere_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCountWhere_le_enncard cache parameter root message P)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

noncomputable def messageDeficitScore (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) : ℝ :=
  (cachedMessageEntryCount cache parameter root message).toReal -
    1024 * (cachedMessageEntryCountWhere cache parameter root message (fun _ => True)).toReal

theorem messageDeficitScore_cacheQuery (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input = none) :
    messageDeficitScore parameter root message (cache.cacheQuery input answer) =
      messageDeficitScore parameter root message cache +
        if MessageInputFor parameter root input message then
          (if Concrete.signAttemptResultOfOutput answer ≠ none then -1023 else 1) else 0 := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite parameter root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite parameter root message cache hfinite (fun _ => True)
  unfold messageDeficitScore
  rw [cachedMessageEntryCount_cacheQuery_eq parameter root message cache input answer hfresh,
    cachedMessageEntryCountWhere_cacheQuery_eq parameter root message cache input answer hfresh]
  simp only [MessageInputFor]
  split_ifs <;> simp_all only [and_true, and_false, true_and, false_and, not_true_eq_false,
    not_false_eq_true, add_zero, ENNReal.toReal_add hcount (by finiteness),
    ENNReal.toReal_add hadmissible (by finiteness), ENNReal.toReal_one] <;> ring

theorem messageDeficitScore_of_no_inputs (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hcount : cachedMessageEntryCount cache parameter root message = 0) :
    messageDeficitScore parameter root message cache ≤ 0 := by
  simp only [messageDeficitScore, hcount, ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

theorem messageDeficitScore_ofReal_eq (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ENNReal.ofReal (messageDeficitScore key.parameter key.root message cache) =
      1024 * Concrete.messageAdmissibleDeficit key message cache := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite key.parameter key.root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite key.parameter key.root message cache hfinite (fun _ => True)
  rw [messageDeficitScore, ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hcount, ENNReal.ofReal_toReal hadmissible]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold Concrete.messageAdmissibleDeficit
  rw [ENNReal.mul_sub (by intros; finiteness)]
  norm_num [ftsTreeHeight]
  congr 1
  calc
    _ = cachedMessageEntryCount cache key.parameter key.root message * ((1024 : ENNReal)⁻¹ * 1024) := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by finiteness), mul_one]
    _ = _ := by ring

end SphincsSecurity
