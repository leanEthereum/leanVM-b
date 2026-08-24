import SphincsSecurity.Proof.Bytes

/-!
# The target-sum code

Two codewords of equal digit sum cannot be ordered componentwise unless they are equal. That is what
removes the Winternitz checksum, and what makes a one-time key unforgeable on a new message: an
adversary holding the chain values at `x` can walk each chain forward, so it can produce any
codeword above `x`, and this says the only one is `x` itself.
-/

namespace SphincsSecurity.TargetSum

theorem eq_of_le_of_sum_eq {x y : Encoding} (hle : ∀ i, (x i).val ≤ (y i).val)
    (hsum : sum x = sum y) : x = y := by
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : sum x < sum y := by
    refine Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

/-- A concatenation of fixed-length blocks determines the blocks. -/
theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

/-- The same, for lists: a concatenation of fixed-length blocks determines the blocks. -/
theorem flatMap_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {xs ys : List α}, xs.length = ys.length → xs.flatMap g = ys.flatMap g → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlength _
      exact (List.eq_nil_of_length_eq_zero hlength.symm).symm
  | cons x xs ih =>
      intro ys hlength h
      cases ys with
      | nil => simp at hlength
      | cons y ys =>
          simp only [List.flatMap_cons] at h
          obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
          exact congrArg₂ _ (hinj _ _ hhead) (ih (by simpa using hlength) htail)

/-- A one-time signature's payload is its `v` endpoints, and the concatenation determines them. -/
theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : Concrete.leafPayload endpoints = Concrete.leafPayload endpoints') :
    endpoints = endpoints' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

/-- A few-time public key's payload is its `k - 1` roots. -/
theorem ftsRootsPayload_injective {roots roots' : FtsTree → Digest}
    (h : Concrete.ftsRootsPayload roots = Concrete.ftsRootsPayload roots') : roots = roots' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

end SphincsSecurity.TargetSum
