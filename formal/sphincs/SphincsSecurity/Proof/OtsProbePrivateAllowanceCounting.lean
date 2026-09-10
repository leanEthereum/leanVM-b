import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeFreshGuessRisk
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateProbeInputAllowance (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe coordinate digest => if coordinate = .position target then
      candidateFailureAllowance table context (some ⟨coordinate, digest⟩) else 0
  | _ => 0

theorem privateProbeInputAllowance_of_not_probe
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : LazyRevealProbe.Query Coordinate) (hprobe : ¬IsPrivatePositionProbe target input) :
    privateProbeInputAllowance target table context input = 0 := by
  cases input <;> simp_all [privateProbeInputAllowance, IsPrivatePositionProbe]

noncomputable def privateLiveProbeAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else privateProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

noncomputable def privateLiveProbeOrdinalAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next ordinal context fuel table =>
      if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then privateProbeInputAllowance target table context input
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal)
              result.context result.remaining result.table
      else 0) computation

theorem privateLiveProbeAllowance_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveProbeAllowance target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else privateProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => privateLiveProbeAllowance target (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem privateLiveProbeOrdinalAllowance_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveProbeOrdinalAllowance target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal context fuel table =
      (if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then privateProbeInputAllowance target table context input
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => privateLiveProbeOrdinalAllowance target (next result.value)
              (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal) result.context result.remaining result.table
      else 0) := rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
