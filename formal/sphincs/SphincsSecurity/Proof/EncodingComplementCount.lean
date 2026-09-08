import SphincsSecurity.Proof.EncodingCount

namespace SphincsSecurity.TargetSum

open scoped BigOperators
attribute [local irreducible] validDigests packHalves digitSumCount
set_option backward.isDefEq.respectTransparency false

def complementDigits {n : Nat} (digits : Fin n → Digit) : Fin n → Digit :=
  fun index => Fin.rev (digits index)

theorem complementDigits_injective {n : Nat} : Function.Injective (@complementDigits n) := by
  intro left right heq
  funext index
  exact Fin.rev_injective (congrFun heq index)

theorem sum_complementDigits_add {n : Nat} (digits : Fin n → Digit) :
    (∑ index, (complementDigits digits index).val) + (∑ index, (digits index).val) = n * 7 := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _index : Fin n, 7 := by
      apply Finset.sum_congr rfl
      intro index _
      have h := (digits index).isLt
      change (digits index).val < 8 at h
      simp only [complementDigits, Fin.val_rev]
      change 8 - ((digits index).val + 1) + (digits index).val = 7
      omega
    _ = _ := by simp

theorem packHalves_valid_of_sum (low high : Fin 21 → Digit)
    (hsum : (∑ index, (low index).val) + (∑ index, (high index).val) = 191) :
    ValidDigest (packHalves low high) := by
  have hvalid : Valid (digestEncoding (packHalves low high)) := by
    unfold Valid sum
    change (∑ index : Fin (21 + 21), (digestEncoding (packHalves low high) index).val) = 191
    rw [Fin.sum_univ_add]
    simpa only [digestEncoding_packHalves_low, digestEncoding_packHalves_high] using hsum
  exact ⟨digestEncoding (packHalves low high), by
    rw [decodeDigest, if_pos ⟨(packHalves_padding low high).1, (packHalves_padding low high).2, hvalid⟩]⟩

theorem digitSumCount_ten_complement_halves_le_validDigests :
    (∑ index : Fin 10, digitSumCount 21 (47 + index.val) * digitSumCount 21 (56 - index.val)) ≤ validDigests.card := by
  let Source := Σ index : Fin 10, DigitSumFiber 21 (47 + index.val) × DigitSumFiber 21 (56 - index.val)
  let packing : Source → {digest // digest ∈ validDigests} := fun source =>
    ⟨packHalves (complementDigits source.2.1.val) (complementDigits source.2.2.val), by
      apply mem_validDigests.mpr
      apply packHalves_valid_of_sum
      have hl := sum_complementDigits_add source.2.1.val
      have hr := sum_complementDigits_add source.2.2.val
      rw [source.2.1.property] at hl
      rw [source.2.2.property] at hr
      have hi := source.1.isLt
      omega⟩
  have hinj : Function.Injective packing := by
    rintro ⟨i, low, high⟩ ⟨j, low', high'⟩ heq
    have hvalues : (complementDigits low.val, complementDigits high.val) =
        (complementDigits low'.val, complementDigits high'.val) := packHalves_injective (congrArg Subtype.val heq)
    have hl := complementDigits_injective (congrArg Prod.fst hvalues)
    have hr := complementDigits_injective (congrArg Prod.snd hvalues)
    have hij : i = j := by
      apply Fin.ext
      have hs := congrArg (fun digits : Fin 21 → Digit => ∑ index, (digits index).val) hl
      rw [low.property, low'.property] at hs
      omega
    subst j
    have hlow : low = low' := Subtype.ext hl
    have hhigh : high = high' := Subtype.ext hr
    subst low'
    subst high'
    rfl
  have hcard := Fintype.card_le_of_injective packing hinj
  simpa only [Source, Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe, digitSumCount] using hcard

end SphincsSecurity.TargetSum
