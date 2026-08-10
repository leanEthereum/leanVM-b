import XmssSecurity.RandomOracle

namespace XmssSecurity

open OracleComp OracleSpec ENNReal
open scoped BigOperators

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

def targetSecurityBits : Nat := 120

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | backwardChain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

def totalBadEventSlots : Nat :=
  1 + numChains + verificationChainHashes + 1 + treeHeight

theorem totalBadEventSlots_eq : totalBadEventSlots = 175 := by
  native_decide

theorem card_badEvent : Fintype.card BadEvent = totalBadEventSlots := by
  native_decide

def badEventSlotCapacity : Nat := 2 ^ (digestBits - targetSecurityBits)

theorem badEventSlotCapacity_eq : badEventSlotCapacity = 256 := by
  native_decide

theorem totalBadEventSlots_le_capacity : totalBadEventSlots ≤ badEventSlotCapacity := by
  native_decide

private theorem capacity_budget_eq (q : Nat) :
    (badEventSlotCapacity : ℝ≥0∞) *
      ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) =
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  have hbits : digestBits = (digestBits - targetSecurityBits) + targetSecurityBits := by
    native_decide
  have hzero : ((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞) ≠ 0 := by
    positivity
  have htop : ((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞) ≠ ∞ := by
    simp
  unfold badEventSlotCapacity
  rw [hbits, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞) *
        ((q : ℝ≥0∞) *
          (((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞)⁻¹)) =
        (((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞) *
          ((2 ^ (digestBits - targetSecurityBits) : Nat) : ℝ≥0∞)⁻¹) *
          ((q : ℝ≥0∞) * ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (q : ℝ≥0∞) * ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

theorem totalBadEventSlots_budget_le_120 (q : Nat) :
    (totalBadEventSlots : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  calc
    (totalBadEventSlots : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) ≤
      (badEventSlotCapacity : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      gcongr
      exact_mod_cast totalBadEventSlots_le_capacity
    _ = (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
      capacity_budget_eq q

/-- Hitting any fresh digest in a set of at most 175 targets costs at most `q / 2^120`. -/
theorem truncated_targets_le_120 {α : Type} (computation : OracleComp HashSpec α)
    (q : Nat) (hbound : computation.IsTotalQueryBound q) (targets : Finset Digest)
    (hcard : targets.card ≤ totalBadEventSlots) (cache : QueryCache HashSpec)
    (habsent : ∀ input output, cache input = some output → truncateHash output ∉ targets) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output ∈ targets |
      (simulateQ cachingOracle computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  refine (Rom.truncated_outputs_hit_targets_from_cache_le
    computation q hbound targets cache habsent).trans ?_
  calc
    (targets.card : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) ≤
      (totalBadEventSlots : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      gcongr
    _ ≤ (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
      totalBadEventSlots_budget_le_120 q

/-- A pointwise classification of a winning event gives the corresponding probability union bound. -/
theorem classified_event_le_sum {α : Type} (computation : OracleComp HashSpec α)
    (win : α → Prop) (occurs : BadEvent → α → Prop)
    (hclassify : ∀ outcome, win outcome → ∃ event, occurs event outcome) :
    Pr[win | computation] ≤ ∑ event, Pr[occurs event | computation] := by
  calc
    Pr[win | computation] ≤
        Pr[fun outcome => ∃ event ∈ (Finset.univ : Finset BadEvent), occurs event outcome |
          computation] := by
      apply probEvent_mono''
      intro outcome hwin
      obtain ⟨event, hevent⟩ := hclassify outcome hwin
      exact ⟨event, Finset.mem_univ event, hevent⟩
    _ ≤ ∑ event ∈ (Finset.univ : Finset BadEvent), Pr[occurs event | computation] :=
      probEvent_exists_finset_le_sum Finset.univ computation occurs
    _ = ∑ event, Pr[occurs event | computation] := by rfl

/-- A union of the 175 reduction events, each bounded by `q / 2^128`, fits within `q / 2^120`. -/
theorem badEvent_sum_le_120 (q : Nat) (cost : BadEvent → ℝ≥0∞)
    (hcost : ∀ event, cost event ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) :
    ∑ event, cost event ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  calc
    ∑ event, cost event ≤
        ∑ _event : BadEvent,
          (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro event _
      exact hcost event
    _ = (totalBadEventSlots : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_badEvent]
    _ ≤ (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
      totalBadEventSlots_budget_le_120 q

/-- Classified bad events bounded individually at 128 bits yield the 120-bit target. -/
theorem classified_event_le_120 {α : Type} (computation : OracleComp HashSpec α)
    (win : α → Prop) (occurs : BadEvent → α → Prop) (q : Nat)
    (hclassify : ∀ outcome, win outcome → ∃ event, occurs event outcome)
    (hcost : ∀ event, Pr[occurs event | computation] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) :
    Pr[win | computation] ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
  (classified_event_le_sum computation win occurs hclassify).trans
    (badEvent_sum_le_120 q (fun event => Pr[occurs event | computation]) hcost)

end XmssSecurity
