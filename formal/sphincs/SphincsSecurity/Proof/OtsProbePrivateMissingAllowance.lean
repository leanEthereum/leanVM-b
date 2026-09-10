import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateAllowanceCounting
import SphincsSecurity.Proof.OtsProbePrivateInactive

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateMissingProbeInputAllowance (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (input : LazyRevealProbe.Query Coordinate) : ENNReal :=
  if context.state.values (.position target) = none then privateProbeInputAllowance target table context input else 0

theorem privateMissingProbeInputAllowance_le (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (input : LazyRevealProbe.Query Coordinate) :
    privateMissingProbeInputAllowance target table context input ≤ privateProbeInputAllowance target table context input := by
  unfold privateMissingProbeInputAllowance
  split_ifs <;> simp

theorem privateMissingProbeInputAllowance_eq_zero_of_inactive
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : LazyRevealProbe.Query Coordinate) (hinactive : PrivateTargetInactive target context) :
    privateMissingProbeInputAllowance target table context input = 0 := by
  rcases hinactive with hknown | hpublic
  · simp [privateMissingProbeInputAllowance, hknown]
  · cases input <;> simp only [privateMissingProbeInputAllowance, privateProbeInputAllowance]
    all_goals try simp
    case probe coordinate digest =>
      by_cases heq : coordinate = .position target
      · subst coordinate
        simp [candidateFailureAllowance, hpublic]
      · simp [heq]

noncomputable def privateLiveMissingProbeAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        privateMissingProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

theorem privateLiveMissingProbeAllowance_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveMissingProbeAllowance target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        privateMissingProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => privateLiveMissingProbeAllowance target (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem privateLiveMissingProbeAllowance_eq_zero_of_inactive
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hinactive : PrivateTargetInactive target context) :
    privateLiveMissingProbeAllowance target computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [privateLiveMissingProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, privateMissingProbeInputAllowance_eq_zero_of_inactive target table context input hinactive, zero_add]
        apply ENNReal.tsum_eq_zero.mpr
        intro option
        by_cases hoption : option ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases option with
          | none => simp
          | some result =>
              dsimp only
              rw [ih result.value result.context result.remaining result.table (hinactive.of_mem_runResolved _ fuel table result hoption), mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hoption]
      · rw [if_neg hcomplete]

theorem privateLiveMissingProbeAllowance_le_stoppedAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveMissingProbeAllowance target computation context fuel table ≤ privateLiveProbeAllowance target computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [privateLiveMissingProbeAllowance_query_bind, privateLiveProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, if_pos hcomplete]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · rw [if_pos hdisclose]
          have hnotProbe : ¬IsPrivatePositionProbe target input := by
            cases input <;> simp_all [IsPrivatePositionDisclosure, IsPrivatePositionProbe]
          rw [show privateMissingProbeInputAllowance target table context input = 0 by
            simp [privateMissingProbeInputAllowance, privateProbeInputAllowance_of_not_probe target table context input hnotProbe], zero_add]
          apply le_of_eq
          apply ENNReal.tsum_eq_zero.mpr
          intro option
          by_cases hoption : option ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
          · cases option with
            | none => simp
            | some result =>
                have hinactive := privateTargetInactive_of_disclosure target input pure context fuel table result hdisclose
                  (by simpa only [bind_pure] using hoption)
                dsimp only
                rw [privateLiveMissingProbeAllowance_eq_zero_of_inactive target _ result.context result.remaining result.table hinactive, mul_zero]
          · simp [probOutput_eq_zero_of_not_mem_support hoption]
        · rw [if_neg hdisclose]
          apply add_le_add (privateMissingProbeInputAllowance_le target table context input)
          apply ENNReal.tsum_le_tsum
          intro option
          apply mul_le_mul' le_rfl
          cases option with
          | none => exact le_rfl
          | some result => exact ih result.value result.context result.remaining result.table
      · rw [if_neg hcomplete, if_neg hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
