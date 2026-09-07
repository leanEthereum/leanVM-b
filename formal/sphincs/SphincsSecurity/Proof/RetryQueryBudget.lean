import SphincsSecurity.Proof.HashPrefixBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] ConsumesHashQueries

noncomputable def retryOption {α : Type} (attempt : OracleComp OracleWorld (Option α)) :
    Nat → OracleComp OracleWorld (Option α)
  | 0 => pure none
  | n + 1 => attempt >>= fun result =>
      match result with
      | none => retryOption attempt n
      | some value => pure (some value)

theorem retryOption_one {α : Type} (attempt : OracleComp OracleWorld (Option α)) :
    retryOption attempt 1 = attempt := by
  simp only [retryOption]
  have h : (fun result : Option α => match result with
      | none => (pure none : OracleComp OracleWorld (Option α))
      | some value => pure (some value)) = pure := by
    funext result
    cases result <;> rfl
  rw [h, bind_pure]

theorem mem_support_retryOption_succ {α : Type}
    (attempt : OracleComp OracleWorld (Option α)) (n : Nat) (result : Option α) :
    result ∈ support (retryOption attempt (n + 1)) ↔ result ∈ support attempt := by
  induction n with
  | zero => rw [retryOption_one]
  | succ n ih =>
      simp only [retryOption, mem_support_bind_iff]
      constructor
      · rintro ⟨out, hout, hresult⟩
        cases out with
        | none => exact ih.mp hresult
        | some value =>
            simp only [mem_support_pure_iff] at hresult
            subst result
            exact hout
      · intro hresult
        cases result with
        | none => exact ⟨none, hresult, ih.mpr hresult⟩
        | some value => exact ⟨some value, hresult, by simp⟩

/-- A syntactic query bound charges retries that can precede the same returned value. -/
theorem consumesHashQueries_retryOption {α : Type}
    (attempt : OracleComp OracleWorld (Option α)) (cost : Nat)
    (hcost : ConsumesHashQueries attempt cost) (hreject : none ∈ support attempt)
    (n : Nat) : ConsumesHashQueries (retryOption attempt n) (n * cost) := by
  induction n with
  | zero => simpa using consumesHashQueries_zero (retryOption attempt 0)
  | succ n ih =>
      cases n with
      | zero =>
          simpa only [Nat.zero_add, retryOption_one, Nat.one_mul] using hcost
      | succ n =>
          unfold ConsumesHashQueries at hcost ih ⊢
          intro β next q hbound result hresult
          rw [retryOption, bind_assoc] at hbound
          obtain ⟨hfirst, htail⟩ := hcost _ q hbound none hreject
          have hsupport : result ∈ support (retryOption attempt (n + 1)) :=
            (mem_support_retryOption_succ attempt n result).mpr
              ((mem_support_retryOption_succ attempt (n + 1) result).mp hresult)
          obtain ⟨hrest, hnext⟩ := ih next (q - cost) htail result hsupport
          constructor
          · rw [Nat.add_mul, Nat.one_mul]
            omega
          · simpa [Nat.add_mul, Nat.sub_sub, Nat.add_comm] using hnext

end SphincsSecurity.Concrete
