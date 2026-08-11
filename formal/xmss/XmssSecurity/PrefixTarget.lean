import XmssSecurity.AdaptiveFreshTarget
import XmssSecurity.QueryBoundSupport

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

/-- A randomized prefix may choose an indexed target map and initial cache before the bounded continuation runs. -/
theorem mixed_adaptiveFreshDigestCollision_after_prefix_le {α β : Type}
    (head : OracleComp OracleWorld β) (continuation : β → OracleComp OracleWorld α)
    (q : Nat)
    (hbound : (head >>= continuation).IsQueryBoundP (· matches .inr _) q)
    (initialCache : QueryCache HashSpec)
    (targetInput : β → QueryCache HashSpec → HashInput → HashInput)
    (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ prefixResult ∈ support ((simulateQ xmssRomImpl head).run initialCache),
      ∀ result ∈ support
        ((simulateQ xmssRomImpl (continuation prefixResult.1)).run prefixResult.2),
        win result → AdaptiveFreshDigestCollisionWith prefixResult.2 result.2
          (targetInput prefixResult.1 prefixResult.2)) :
    Pr[win | (simulateQ xmssRomImpl (head >>= continuation)).run initialCache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro prefixResult hprefixResult
  have hprefixSupport : prefixResult.1 ∈ support head := by
    apply support_simulateQ_run'_subset xmssRomImpl head initialCache
    rw [StateT.run'_eq, support_map]
    exact ⟨prefixResult, hprefixResult, rfl⟩
  have hcontinuationBound :
      (continuation prefixResult.1).IsQueryBoundP (· matches .inr _) q :=
    OracleComp.IsQueryBoundP.continuation_mono_of_mem_support
      (· matches .inr _) head continuation q hbound prefixResult.1 hprefixSupport
  exact mixed_adaptiveFreshDigestCollisionWith_le
    (continuation prefixResult.1) q hcontinuationBound prefixResult.2
    (targetInput prefixResult.1 prefixResult.2) win
    (hwin prefixResult hprefixResult)

end XmssSecurity.Rom
