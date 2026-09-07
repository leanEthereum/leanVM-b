import SphincsSecurity.Proof.CachedTargetIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cachedTargetFutureIncrement_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input sourceInput : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (source : FewTimeView) :
    cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log sourceInput source =
      cachedTargetFutureIncrement remaining key before log sourceInput source +
        (if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          targetCoverageInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0) := by
  have hweight : (fun targetInput target => targetCoverageInputIncrement remaining key
        (before.cacheQuery input output) log (payloadOf targetInput) target sourceInput source) =
      (fun targetInput target => targetCoverageInputIncrement remaining key before log (payloadOf targetInput) target sourceInput source) := by
    funext targetInput target
    exact targetCoverageInputIncrement_cache_stable remaining key before _ log _ target source sourceInput
      (QueryCache.le_cacheQuery before hfresh) hsigned
  rw [cachedTargetFutureIncrement, hweight, cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  rfl

theorem cachedReuseColumn_cacheQuery_of_ne (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input sourceInput : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hne : sourceInput ≠ input) :
    cachedSignerInputWeight key message (before.cacheQuery input output)
        (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) sourceInput =
      cachedSignerInputWeight key message before (cachedTargetFutureIncrement remaining key before log) sourceInput +
        cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput := by
  unfold cachedTargetSourceIncrement cacheMessageEntryWeight
  simp only [QueryCache.cacheQuery_self, cachedSignerInputWeight, QueryCache.cacheQuery_of_ne before output hne]
  cases before sourceInput with
  | none => simp only [ite_self, add_zero]
  | some sourceOutput =>
      simp only [cachedTargetFutureIncrement_cacheQuery remaining key before log input sourceInput output hfresh hsigned,
        targetCoverageInputIncrement_cache_stable remaining key before _ log _ _ _ sourceInput
          (QueryCache.le_cacheQuery before hfresh) hsigned]
      split_ifs <;> simp only [add_zero]

theorem cachedFutureCoverageReuseCharge_cacheQuery (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) :
    cachedFutureCoverageReuseCharge remaining key message (before.cacheQuery input output) log q =
      cachedFutureCoverageReuseCharge remaining key message before log q +
        ((∑' sourceInput, cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput) +
          cachedSignerInputWeight key message (before.cacheQuery input output)
            (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input) * digestReuseWeight q := by
  have hpoint (sourceInput : HashInput) :
      (if sourceInput = input then 0 else cachedSignerInputWeight key message (before.cacheQuery input output)
        (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) sourceInput) =
      cachedSignerInputWeight key message before (cachedTargetFutureIncrement remaining key before log) sourceInput +
        cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput := by
    by_cases heq : sourceInput = input
    · subst sourceInput
      simp only [if_true, cachedSignerInputWeight, hfresh, cachedTargetSourceIncrement_self, add_zero]
    · rw [if_neg heq]
      exact cachedReuseColumn_cacheQuery_of_ne remaining key message before log input sourceInput output hfresh hsigned heq
  simp only [cachedFutureCoverageReuseCharge_eq_sources]
  rw [ENNReal.tsum_eq_add_tsum_ite
    (f := cachedSignerInputWeight key message (before.cacheQuery input output)
      (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log)) input]
  calc
    _ = (cachedSignerInputWeight key message (before.cacheQuery input output)
          (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input +
        ∑' sourceInput, (cachedSignerInputWeight key message before (cachedTargetFutureIncrement remaining key before log) sourceInput +
          cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput)) * digestReuseWeight q := by
      apply congrArg (fun value => (cachedSignerInputWeight key message (before.cacheQuery input output)
        (cachedTargetFutureIncrement remaining key (before.cacheQuery input output) log) input + value) * digestReuseWeight q)
      apply tsum_congr
      intro sourceInput
      have h := hpoint sourceInput
      by_cases heq : sourceInput = input <;> simp only [heq, if_true, if_false] at h ⊢ <;> exact h
    _ = _ := by
      rw [ENNReal.tsum_add]
      ring

end SphincsSecurity.Concrete
