import XmssSecurity.Encoding

namespace XmssSecurity.Wots

/-- Walk `steps` edges of a domain-separated hash chain starting at `position`. -/
def walk {α : Type} (step : Nat → α → α) : Nat → Nat → α → α
  | _, 0, value => value
  | position, steps + 1, value => step (position + steps) (walk step position steps value)

@[simp]
theorem walk_zero {α : Type} (step : Nat → α → α) (position : Nat) (value : α) :
    walk step position 0 value = value := rfl

theorem walk_add {α : Type} (step : Nat → α → α) (position first second : Nat)
    (value : α) :
    walk step position (first + second) value =
      walk step (position + first) second (walk step position first value) := by
  induction second with
  | zero => simp
  | succ second ih =>
      simp only [walk]
      exact congrArg₂ step (Nat.add_assoc position first second).symm ih

theorem walk_split {α : Type} (step : Nat → α → α) (start split finish : Nat)
    (value : α) (hstart : start ≤ split) (hfinish : split ≤ finish) :
    walk step start (finish - start) value =
      walk step split (finish - split) (walk step start (split - start) value) := by
  rw [show finish - start = (split - start) + (finish - split) by omega, walk_add]
  congr 2
  omega

def HasStepCollision {α : Type} (step : Nat → α → α) (position steps : Nat)
    (left right : α) : Prop :=
  ∃ offset, offset < steps ∧
    walk step position offset left ≠ walk step position offset right ∧
    step (position + offset) (walk step position offset left) =
      step (position + offset) (walk step position offset right)

/-- Equal chain endpoints come from equal starts or from a collision at one chain step. -/
theorem eq_or_hasStepCollision {α : Type} (step : Nat → α → α) (position steps : Nat)
    (left right : α) (hend : walk step position steps left = walk step position steps right) :
    left = right ∨ HasStepCollision step position steps left right := by
  induction steps with
  | zero =>
      left
      simpa using hend
  | succ steps ih =>
      by_cases hmid : walk step position steps left = walk step position steps right
      · rcases ih hmid with hstart | hcollision
        · exact Or.inl hstart
        · exact Or.inr <| by
            obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
            exact ⟨offset, Nat.lt_succ_of_lt hoffset, hne, heq⟩
      · right
        exact ⟨steps, Nat.lt_succ_self steps, hmid, by simpa only [walk] using hend⟩

/-- A value forged earlier in a chain either recovers the signed value or creates a chain collision. -/
theorem backward_value_or_hasStepCollision {α : Type} (step : Nat → α → α)
    (forgedPosition signedPosition finish : Nat) (forgedValue signedValue : α)
    (hforged : forgedPosition ≤ signedPosition) (hsigned : signedPosition ≤ finish)
    (hend : walk step forgedPosition (finish - forgedPosition) forgedValue =
      walk step signedPosition (finish - signedPosition) signedValue) :
    walk step forgedPosition (signedPosition - forgedPosition) forgedValue = signedValue ∨
      HasStepCollision step signedPosition (finish - signedPosition)
        (walk step forgedPosition (signedPosition - forgedPosition) forgedValue) signedValue := by
  apply eq_or_hasStepCollision
  rw [← walk_split step forgedPosition signedPosition finish forgedValue hforged hsigned]
  exact hend

def signChain {α : Type} (step : Nat → α → α) (digit : Digit) (secret : α) : α :=
  walk step 0 digit.val secret

def recoverChain {α : Type} (step : Nat → α → α) (digit : Digit) (value : α) : α :=
  walk step digit.val (chainLength - 1 - digit.val) value

def publicChain {α : Type} (step : Nat → α → α) (secret : α) : α :=
  walk step 0 (chainLength - 1) secret

/-- Continuing an honestly generated chain value reaches its public endpoint. -/
theorem recover_signChain_eq_publicChain {α : Type} (step : Nat → α → α)
    (digit : Digit) (secret : α) :
    recoverChain step digit (signChain step digit secret) = publicChain step secret := by
  calc
    recoverChain step digit (signChain step digit secret) =
        walk step 0 (digit.val + (chainLength - 1 - digit.val)) secret := by
      simpa [recoverChain, signChain] using
        (walk_add step 0 digit.val (chainLength - 1 - digit.val) secret).symm
    _ = publicChain step secret := by
      unfold publicChain
      congr 2
      omega

/-- A distinct valid WOTS encoding with the same recovered endpoints yields a backward preimage or a chain collision. -/
theorem extract_of_distinct_valid_encodings {α : Type}
    (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α)
    (hsigned : TargetSum.Valid signedEncoding) (hforged : TargetSum.Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding)
    (hendpoints : ∀ i,
      recoverChain (step i) (forgedEncoding i) (forgedValue i) =
        recoverChain (step i) (signedEncoding i) (signedValue i)) :
    ∃ i, forgedEncoding i < signedEncoding i ∧
      (walk (step i) (forgedEncoding i).val
          ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i) = signedValue i ∨
        HasStepCollision (step i) (signedEncoding i).val
          (chainLength - 1 - (signedEncoding i).val)
          (walk (step i) (forgedEncoding i).val
            ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i))
          (signedValue i)) := by
  obtain ⟨i, hi⟩ := TargetSum.exists_forged_lt_signed hsigned hforged hne
  refine ⟨i, hi, ?_⟩
  apply backward_value_or_hasStepCollision
  · exact hi.le
  · exact Nat.le_pred_of_lt (signedEncoding i).isLt
  · simpa only [recoverChain] using hendpoints i

end XmssSecurity.Wots
