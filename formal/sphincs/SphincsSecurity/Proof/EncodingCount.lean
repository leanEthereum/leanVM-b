import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.Code

namespace SphincsSecurity.TargetSum

open scoped BigOperators

set_option maxRecDepth 1000
set_option backward.isDefEq.respectTransparency false

def packDigits {n : Nat} (digits : Fin n → Digit) : BitVec (3 * n) :=
  (BitVec.ofBoolListLE (List.ofFn fun bit : Fin (3 * n) =>
    (BitVec.ofFin (digits ⟨bit.val / 3, by omega⟩)).getLsbD (bit.val % 3))).cast (by simp)

theorem getLsbD_packDigits {n : Nat} (digits : Fin n → Digit) (bit : Nat) (hbit : bit < 3 * n) :
    (packDigits digits).getLsbD bit =
      (BitVec.ofFin (digits ⟨bit / 3, by omega⟩)).getLsbD (bit % 3) := by
  rw [packDigits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, hbit]

theorem extract_packDigits {n : Nat} (digits : Fin n → Digit) (index : Fin n) :
    (packDigits digits).extractLsb' (3 * index.val) 3 = BitVec.ofFin (digits index) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  rw [BitVec.getLsbD_extractLsb']
  have hwithin : 3 * index.val + bit < 3 * n := by omega
  rw [getLsbD_packDigits digits _ hwithin]
  have hdiv : (3 * index.val + bit) / 3 = index.val := by omega
  have hmod : (3 * index.val + bit) % 3 = bit := by omega
  simp only [hbit, decide_true, Bool.true_and, hdiv, hmod]

def packHalves (low high : Fin 21 → Digit) : Digest :=
  ((0#1 ++ packDigits high) ++ (0#1 ++ packDigits low))

theorem packHalves_padding (low high : Fin 21 → Digit) :
    (packHalves low high).getLsbD 63 = false ∧ (packHalves low high).getLsbD 127 = false := by
  have hpad : ∀ digits : Fin 21 → Digit, (0#1 ++ packDigits digits).getLsbD 63 = false := by
    intro digits
    rw [BitVec.getLsbD_append, if_neg (by decide)]
    rfl
  unfold packHalves
  constructor
  · rw [BitVec.getLsbD_append, if_pos (by decide)]
    exact hpad low
  · rw [BitVec.getLsbD_append, if_neg (by decide)]
    exact hpad high

theorem packHalves_extract_low (low high : Fin 21 → Digit) (index : Fin 21) :
    (packHalves low high).extractLsb' (3 * index.val) 3 = BitVec.ofFin (low index) := by
  rw [← extract_packDigits low index]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  simp only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and]
  have h63 : 3 * index.val + bit < 63 := by omega
  have h64 : 3 * index.val + bit < 64 := by omega
  simp only [packHalves, BitVec.getLsbD_append, h63, h64, if_pos]

theorem packHalves_extract_high (low high : Fin 21 → Digit) (index : Fin 21) :
    (packHalves low high).extractLsb' (64 + 3 * index.val) 3 = BitVec.ofFin (high index) := by
  rw [← extract_packDigits high index]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  simp only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and]
  have h64 : ¬64 + 3 * index.val + bit < 64 := by omega
  have h63 : 3 * index.val + bit < 63 := by omega
  have hsub : 64 + 3 * index.val + bit - 64 = 3 * index.val + bit := by omega
  simp only [packHalves, BitVec.getLsbD_append, h64, ite_false, hsub, h63, if_pos]

theorem digestEncoding_packHalves_low (low high : Fin 21 → Digit) (index : Fin 21) :
    digestEncoding (packHalves low high) (index.castAdd 21) = low index := by
  have hoffset : digitOffset (index.castAdd 21) = 3 * index.val := by
    simp [digitOffset, winternitzBits, digitsPerHalf, numChains]
  unfold digestEncoding
  rw [hoffset]
  change ((packHalves low high).extractLsb' (3 * index.val) 3).toFin = low index
  exact congrArg BitVec.toFin (packHalves_extract_low low high index)

theorem digestEncoding_packHalves_high (low high : Fin 21 → Digit) (index : Fin 21) :
    digestEncoding (packHalves low high) (index.natAdd 21) = high index := by
  have hoffset : digitOffset (index.natAdd 21) = 64 + 3 * index.val := by
    simp only [digitOffset, Fin.val_natAdd]
    norm_num [winternitzBits, digitsPerHalf, numChains]
    omega
  unfold digestEncoding
  rw [hoffset]
  change ((packHalves low high).extractLsb' (64 + 3 * index.val) 3).toFin = high index
  exact congrArg BitVec.toFin (packHalves_extract_high low high index)

theorem packHalves_injective : Function.Injective (fun halves : (Fin 21 → Digit) × (Fin 21 → Digit) =>
    packHalves halves.1 halves.2) := by
  intro left right heq
  apply Prod.ext
  · funext index
    have h := congrArg (fun digest => digestEncoding digest (index.castAdd 21)) heq
    simpa only [digestEncoding_packHalves_low] using h
  · funext index
    have h := congrArg (fun digest => digestEncoding digest (index.natAdd 21)) heq
    simpa only [digestEncoding_packHalves_high] using h

theorem packHalves_valid (low high : Fin 21 → Digit)
    (hlow : (∑ index, (low index).val) = 95) (hhigh : (∑ index, (high index).val) = 96) :
    ValidDigest (packHalves low high) := by
  have hsum : Valid (digestEncoding (packHalves low high)) := by
    unfold Valid sum
    change (∑ index : Fin (21 + 21), (digestEncoding (packHalves low high) index).val) = 191
    rw [Fin.sum_univ_add]
    simp only [digestEncoding_packHalves_low, digestEncoding_packHalves_high, hlow, hhigh]
  refine ⟨digestEncoding (packHalves low high), ?_⟩
  rw [decodeDigest, if_pos ⟨(packHalves_padding low high).1, (packHalves_padding low high).2, hsum⟩]

abbrev DigitSumFiber (n total : Nat) := {digits : Fin n → Digit // (∑ index, (digits index).val) = total}

noncomputable def digitSumCount (n total : Nat) : Nat := Fintype.card (DigitSumFiber n total)

theorem digitSumCount_zero (total : Nat) : digitSumCount 0 total = if total = 0 then 1 else 0 := by
  by_cases hzero : total = 0
  · subst total
    simp [digitSumCount, DigitSumFiber]
  · have hempty : IsEmpty (DigitSumFiber 0 total) := ⟨fun digits => by
      have heq : 0 = total := by simpa using digits.property
      exact hzero heq.symm⟩
    simp [digitSumCount, hzero]

def digitSumSplit (n total : Nat) : DigitSumFiber (n + 1) total ≃
    Σ head : Digit, {tail : Fin n → Digit // head.val + (∑ index, (tail index).val) = total} where
  toFun digits := ⟨digits.val 0, ⟨fun index => digits.val index.succ, by
    simpa only [Fin.sum_univ_succ] using digits.property⟩⟩
  invFun pair := ⟨Fin.cons pair.1 pair.2.val, by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using pair.2.property⟩
  left_inv digits := by
    apply Subtype.ext
    funext index
    cases index using Fin.cases <;> rfl
  right_inv pair := by
    cases pair
    rfl

theorem digitSumCount_succ (n total : Nat) :
    digitSumCount (n + 1) total = ∑ head : Digit, if head.val ≤ total then digitSumCount n (total - head.val) else 0 := by
  rw [digitSumCount, Fintype.card_congr (digitSumSplit n total), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro head _
  by_cases hle : head.val ≤ total
  · rw [if_pos hle]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun tail => by omega)
  · rw [if_neg hle]
    have hempty : IsEmpty {tail : Fin n → Digit // head.val + (∑ index, (tail index).val) = total} :=
      ⟨fun tail => by have := tail.property; omega⟩
    exact Fintype.card_eq_zero

theorem product_card_le_finset_of_injective
    {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq γ]
    (targets : Finset γ) (packing : α × β → γ) (hinjective : Function.Injective packing)
    (hmem : ∀ pair, packing pair ∈ targets) : Fintype.card α * Fintype.card β ≤ targets.card := by
  calc
    Fintype.card α * Fintype.card β = Fintype.card (α × β) := (Fintype.card_prod α β).symm
    _ = (Finset.univ.image packing).card := (Finset.card_image_of_injective Finset.univ hinjective).symm
    _ ≤ targets.card := Finset.card_le_card (by
      intro value hvalue
      obtain ⟨pair, _hpair, rfl⟩ := Finset.mem_image.mp hvalue
      exact hmem pair)

theorem digitSumCount_product_le_finset {γ : Type} [DecidableEq γ]
    (n total m otherTotal : Nat) (targets : Finset γ)
    (packing : DigitSumFiber n total × DigitSumFiber m otherTotal → γ)
    (hinjective : Function.Injective packing) (hmem : ∀ pair, packing pair ∈ targets) :
    digitSumCount n total * digitSumCount m otherTotal ≤ targets.card :=
  product_card_le_finset_of_injective targets packing hinjective hmem

theorem digitSumCount_halves_le_validDigests :
    digitSumCount 21 95 * digitSumCount 21 96 ≤ validDigests.card := by
  apply digitSumCount_product_le_finset 21 95 21 96 validDigests
    (fun halves : DigitSumFiber 21 95 × DigitSumFiber 21 96 => packHalves halves.1.val halves.2.val)
  · intro left right heq
    have hvalues := @packHalves_injective (left.1.val, left.2.val) (right.1.val, right.2.val) heq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hvalues)) (Subtype.ext (congrArg Prod.snd hvalues))
  · intro halves
    exact mem_validDigests.mpr (packHalves_valid halves.1.val halves.2.val halves.1.property halves.2.property)

def digitSumStep (row : List Nat) : List Nat :=
  List.ofFn fun total : Fin 97 =>
    ∑ head : Digit, if head.val ≤ total.val then row.getD (total.val - head.val) 0 else 0

theorem digitSumStep_correct (row : List Nat) (n : Nat)
    (hrow : ∀ total, total < 97 → row.getD total 0 = digitSumCount n total) :
    ∀ total, total < 97 → (digitSumStep row).getD total 0 = digitSumCount (n + 1) total := by
  intro total htotal
  simp only [digitSumStep, List.getD_eq_getElem?_getD, List.getElem?_ofFn, htotal, dite_true, Option.getD_some]
  rw [digitSumCount_succ]
  apply Finset.sum_congr rfl
  intro head _
  by_cases hle : head.val ≤ total
  · simp only [hle, if_pos]
    exact hrow (total - head.val) (by omega)
  · simp [hle]

end SphincsSecurity.TargetSum
