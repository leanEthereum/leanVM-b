import SphincsSecurity.Proof.CachedFutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetSourceIncrement (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (targetInput sourceInput : HashInput) : ENNReal :=
  cacheMessageEntryWeight key.parameter (fun input target =>
    cachedSignerInputWeight key message before
      (targetCoverageInputIncrement remaining key before log (payloadOf input) target) sourceInput) before targetInput

theorem cachedFutureCoverageReuseCharge_eq_pairs (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) :
    cachedFutureCoverageReuseCharge remaining key message before log q =
      (∑' targetInput, ∑' sourceInput, cachedTargetSourceIncrement remaining key message before log targetInput sourceInput) *
        digestReuseWeight q := by
  unfold cachedFutureCoverageReuseCharge cacheMessageWeight
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro targetInput
  unfold cachedTargetSourceIncrement cacheMessageEntryWeight
  cases before targetInput with
  | none => simp only [tsum_zero, zero_mul]
  | some output =>
      simp only
      split_ifs
      · rfl
      · simp only [tsum_zero, zero_mul]

theorem cachedTargetSourceIncrement_self (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) :
    cachedTargetSourceIncrement remaining key message before log input input = 0 := by
  unfold cachedTargetSourceIncrement cacheMessageEntryWeight
  cases before input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood
      · obtain ⟨payload, rfl⟩ := hgood.1
        rw [payloadOf_tweakableHashInput]
        exact cachedSignerInputWeight_target_self remaining key message before log payload _
      · rfl

theorem cachedTargetSourceIncrement_of_ne (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (targetInput sourceInput : HashInput)
    (hne : sourceInput ≠ targetInput) :
    cachedTargetSourceIncrement remaining key message before log targetInput sourceInput =
      cacheMessageEntryWeight key.parameter (fun input target =>
        cachedSignerInputWeight key message before (fun _ source => futureFewTimeCoverageIncrement remaining
          (uncoveredFewTimeTrees (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter before)
            key.root (payloadOf input) log) target) target source) sourceInput) before targetInput := by
  unfold cachedTargetSourceIncrement cacheMessageEntryWeight
  cases before targetInput with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood
      · obtain ⟨payload, rfl⟩ := hgood.1
        rw [payloadOf_tweakableHashInput]
        unfold cachedSignerInputWeight
        cases before sourceInput with
        | none => rfl
        | some sourceOutput =>
            simp only
            split_ifs
            · exact targetCoverageInputIncrement_of_ne remaining key before log payload _ _ sourceInput hne
            · rfl
      · rfl

end SphincsSecurity.Concrete
