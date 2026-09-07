import SphincsSecurity.Proof.DirectQueryBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

def ConsumesHashQueries {α : Type} (computation : OracleComp OracleWorld α) (cost : Nat) : Prop :=
  ∀ {β : Type} (next : α → OracleComp OracleWorld β) (q : Nat),
    (computation >>= next).IsQueryBoundP (· matches Sum.inr _) q →
    ∀ value ∈ support computation, cost ≤ q ∧
      (next value).IsQueryBoundP (· matches Sum.inr _) (q - cost)

theorem consumesHashQueries_zero {α : Type} (computation : OracleComp OracleWorld α) :
    ConsumesHashQueries computation 0 := by
  intro β next q hbound value hvalue
  exact ⟨Nat.zero_le _, isQueryBoundP_of_bind hbound value hvalue⟩

theorem ConsumesHashQueries.mono {α : Type} {computation : OracleComp OracleWorld α}
    {a b : Nat} (h : ConsumesHashQueries computation a) (hba : b ≤ a) :
    ConsumesHashQueries computation b := by
  intro β next q hbound value hvalue
  obtain ⟨ha, htail⟩ := h next q hbound value hvalue
  exact ⟨hba.trans ha, htail.mono (Nat.sub_le_sub_left hba q)⟩

theorem consumesHashQueries_pure {α : Type} (value : α) :
    ConsumesHashQueries (pure value) 0 := by
  intro β next q hbound result hresult
  simp only [mem_support_pure_iff] at hresult
  subst result
  exact ⟨Nat.zero_le _, by simpa using hbound⟩

theorem consumesHashQueries_bind {α β : Type} (first : OracleComp OracleWorld α)
    (second : α → OracleComp OracleWorld β) (a b : Nat)
    (hfirst : ConsumesHashQueries first a) (hsecond : ∀ value, ConsumesHashQueries (second value) b) :
    ConsumesHashQueries (first >>= second) (a + b) := by
  intro γ next q hbound result hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨value, hvalue, hresult⟩ := hresult
  rw [bind_assoc] at hbound
  obtain ⟨ha, htail⟩ := hfirst _ q hbound value hvalue
  obtain ⟨hb, hrest⟩ := hsecond value next (q - a) htail result hresult
  exact ⟨by omega, by simpa only [Nat.sub_sub] using hrest⟩

theorem consumesHashQueries_hash (input : HashInput) :
    ConsumesHashQueries (oracleHash input) 1 := by
  intro β next q hbound value hvalue
  change (liftM (OracleWorld.query (.inr input)) >>= next).IsQueryBoundP _ q at hbound
  rw [isQueryBoundP_query_bind_iff] at hbound
  exact ⟨Nat.succ_le_iff.mpr (by simpa using hbound.1), hbound.2 value⟩

theorem consumesHashQueries_tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    ConsumesHashQueries (liftM (tweakableHash parameter domain payload : OracleComp HashSpec Digest)) 1 := by
  change ConsumesHashQueries (oracleHash (tweakableHashInput parameter domain payload) >>= fun output => pure (truncateHash output)) 1
  exact consumesHashQueries_bind (oracleHash (tweakableHashInput parameter domain payload)) (fun output => pure (truncateHash output)) 1 0 (consumesHashQueries_hash _) (fun _ => consumesHashQueries_pure _)

end SphincsSecurity.Concrete
