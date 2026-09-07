import SphincsSecurity.Proof.EncodingProbability

namespace SphincsSecurity.TargetSum

open scoped BigOperators
attribute [local irreducible] validDigests

theorem valid_encoding_eq_of_prefix_eq {left right : Encoding}
    (hl : Valid left) (hr : Valid right)
    (hprefix : ∀ i : Fin 41, left i.castSucc = right i.castSucc) : left = right := by
  have hsum : (∑ i : Fin 42, (left i).val) = ∑ i : Fin 42, (right i).val := hl.trans hr.symm
  rw [Fin.sum_univ_castSucc (fun i : Fin 42 => (left i).val),
    Fin.sum_univ_castSucc (fun i : Fin 42 => (right i).val)] at hsum
  have hprefixSum : (∑ i : Fin 41, (left i.castSucc).val) = ∑ i : Fin 41, (right i.castSucc).val :=
    Finset.sum_congr rfl (fun i _ => congrArg Fin.val (hprefix i))
  have hlast : left (Fin.last 41) = right (Fin.last 41) := Fin.ext (by omega)
  funext i
  exact Fin.lastCases hlast (fun j => hprefix j) i

theorem ValidDigest.decode_eq {digest : Digest} (hvalid : ValidDigest digest) :
    decodeDigest digest = some (digestEncoding digest) := by
  obtain ⟨encoding, hencoding⟩ := hvalid
  unfold decodeDigest at hencoding ⊢
  split at hencoding
  · rename_i h
    rw [if_pos h]
  · contradiction

theorem validDigests_card_le_two_pow_123 : validDigests.card ≤ 2 ^ 123 := by
  let firstDigits : {digest // digest ∈ validDigests} → (Fin 41 → Digit) :=
    fun digest i => digestEncoding digest.val i.castSucc
  have hinj : Function.Injective firstDigits := by
    intro left right heq
    apply Subtype.ext
    have hl := (mem_validDigests.mp left.property).decode_eq
    have hr := (mem_validDigests.mp right.property).decode_eq
    have hencoding := valid_encoding_eq_of_prefix_eq (valid_of_decodeDigest_eq_some hl)
      (valid_of_decodeDigest_eq_some hr) (fun i => congrFun heq i)
    rw [← hencoding] at hr
    exact decodeDigest_some_injective hl hr
  have hcard := Fintype.card_le_of_injective firstDigits hinj
  have hcard' : validDigests.card ≤ 8 ^ 41 := by
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
      show chainLength = 8 from rfl] using hcard
  exact hcard'.trans_eq (by norm_num)

end SphincsSecurity.TargetSum

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal

theorem probEvent_uniform_encoding_valid_le_one_div_32 :
    Pr[fun output : HashOutput => TargetSum.ValidDigest (truncateHash output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 32 := by
  rw [probEvent_uniform_encoding_valid, div_eq_mul_inv]
  apply (mul_le_mul' (Nat.cast_le (α := ENNReal).mpr TargetSum.validDigests_card_le_two_pow_123) le_rfl).trans_eq
  rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

end SphincsSecurity
