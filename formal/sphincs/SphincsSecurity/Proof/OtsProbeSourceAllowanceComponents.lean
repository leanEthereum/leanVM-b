import SphincsSecurity.Proof.OtsProbeSourceRiskAccumulation
import SphincsSecurity.Proof.OtsProbeNativeCandidateComponents

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveSourceCharge
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        charge table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

theorem liveSourceCharge_query_bind
    (charge : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveSourceCharge charge ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input) :
      OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        charge table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table
            (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input))] *
            match result with
            | none => 0
            | some result => liveSourceCharge charge (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem liveSourceCharge_add
    (left right : (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveSourceCharge (fun table context input => left table context input + right table context input)
      computation context fuel table =
      liveSourceCharge left computation context fuel table + liveSourceCharge right computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [liveSourceCharge]
  | query_bind input next ih =>
      simp only [liveSourceCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [hcomplete, if_true]
        conv_rhs => rw [add_add_add_comm]
        congr 1
        rw [← ENNReal.tsum_add]
        apply tsum_congr
        intro result
        cases result with
        | none => simp
        | some result =>
            dsimp only
            rw [ih, mul_add]
      · simp [hcomplete]

theorem liveSourceCharge_zero (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveSourceCharge (fun _ _ _ => 0) computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [liveSourceCharge_query_bind]
      split_ifs
      · rw [zero_add]
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        cases result with
        | none => simp
        | some result => simp only [ih, mul_zero]
      · rfl

theorem liveSourceCharge_sum {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (charge : ι → (OtsSecretIndex → HashOutput) → DeferredContext → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveSourceCharge (fun table context input => ∑ index ∈ indices, charge index table context input)
      computation context fuel table =
      ∑ index ∈ indices, liveSourceCharge (charge index) computation context fuel table := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [liveSourceCharge_zero]
  | @insert index indices hnot ih =>
      simp only [Finset.sum_insert hnot]
      rw [liveSourceCharge_add, ih]

noncomputable def materializedProbeInputAllowance (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe coordinate digest => materializedCandidateAllowance table context (some ⟨coordinate, digest⟩)
  | _ => 0

noncomputable def liveMaterializedProbeAllowance
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  liveSourceCharge materializedProbeInputAllowance computation

theorem probeFailureInputAllowance_eq_components (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (input : LazyRevealProbe.Query Coordinate) :
    probeFailureInputAllowance table context input = startProbeInputAllowance table context input +
      (∑ target : Position, privateMissingProbeInputAllowance target table context input) +
      materializedProbeInputAllowance table context input := by
  cases input with
  | probe coordinate digest =>
      exact candidateFailureAllowance_eq_native_components Finset.univ table context (some ⟨coordinate, digest⟩)
        (by simp)
  | _ => simp [probeFailureInputAllowance, startProbeInputAllowance, materializedProbeInputAllowance,
      privateMissingProbeInputAllowance, privateProbeInputAllowance]

theorem liveProbeFailureAllowance_eq_components
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveProbeFailureAllowance computation context fuel table =
      liveStartProbeAllowance computation context fuel table +
        (∑ target : Position, privateLiveMissingProbeAllowance target computation context fuel table) +
        liveMaterializedProbeAllowance computation context fuel table := by
  change liveSourceCharge probeFailureInputAllowance computation context fuel table = _
  rw [show probeFailureInputAllowance = fun table context input => startProbeInputAllowance table context input +
      (∑ target : Position, privateMissingProbeInputAllowance target table context input) +
      materializedProbeInputAllowance table context input from funext fun table => funext fun context =>
        funext fun input => probeFailureInputAllowance_eq_components table context input]
  rw [liveSourceCharge_add, liveSourceCharge_add, liveSourceCharge_sum]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
