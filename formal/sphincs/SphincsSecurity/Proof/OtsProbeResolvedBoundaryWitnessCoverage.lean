import SphincsSecurity.Proof.OtsProbeCanonicalPrivateEndpoint

/-!
# Boundary witness coverage

The materialized-stability coupling is consumed with one combined postcondition. A detailed
failure is covered either by a private witness on the deferred side or by the ordinary projection
of the detailed outcome.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def WitnessOrOrdinaryCovers
    (source : PrivateWitnessPlanOutput) (outcome : DirectBoundaryOutcome) : Prop :=
  outcome.failed = true → source.1.isSome = true ∨ outcome.ordinary = true

theorem witnessOrOrdinaryCovers_of_witness
    (witness : PrivateHitWitness) (candidates : List Probe)
    (outcome : DirectBoundaryOutcome) :
    WitnessOrOrdinaryCovers (some witness, candidates) outcome := by
  intro _
  exact Or.inl rfl

theorem witnessOrOrdinaryCovers_ordinaryFailure
    (source : PrivateWitnessPlanOutput) :
    WitnessOrOrdinaryCovers source .ordinaryFailure := by
  intro _
  exact Or.inr rfl

theorem relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers
    (left : ProbComp PrivateWitnessPlanOutput) :
    RelTriple (spec₁ := unifSpec) (spec₂ := unifSpec) left
      (pure (.ordinaryFailure : DirectBoundaryOutcome))
      WitnessOrOrdinaryCovers := by
  have hbase : RelTriple left
      (pure .ordinaryFailure : ProbComp DirectBoundaryOutcome) (fun _ _ ↦ True) :=
    relTriple_true (spec₁ := unifSpec) (spec₂ := unifSpec) left
      (pure .ordinaryFailure : ProbComp DirectBoundaryOutcome)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro source outcome hrelation
  have houtcome : outcome = .ordinaryFailure := by
    simpa using hrelation.2
  subst outcome
  exact witnessOrOrdinaryCovers_ordinaryFailure source

set_option maxRecDepth 100000 in
theorem relTriple_finishDirectWitnessPlan_detailed_of_materializedStable
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (rightObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (candidates : List Probe)
    (hstep : RelTriple leftRun rightRun
      (DirectWitnessMaterializedStableRunEq table))
    (hclean : ∀ left right,
      DirectWitnessResult.done left ∈ support leftRun →
      DirectDetailedResult.done right ∈ support rightRun →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (leftObserve left.context left.remaining left.value candidates)
        (rightObserve right.context right.remaining right.value)
        WitnessOrOrdinaryCovers)
    (hdoomed : ∀ (left : ProbComp PrivateWitnessPlanOutput) right,
      DirectDetailedResult.done right ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table right →
      RelTriple left (rightObserve right.context right.remaining right.value)
        WitnessOrOrdinaryCovers) :
    RelTriple
      (leftRun >>= finishDirectWitnessPlanObserve leftObserve candidates)
      (rightRun >>= finishDirectDetailedObserve rightObserve)
      WitnessOrOrdinaryCovers := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result ↦ result ∈ support leftRun) (fun _ hresult ↦ hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro left right hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases left with
  | stoppedFuel =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
          | fuelExhausted =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
      | done right =>
          exact hdoomed (pure (none, candidates)) right hrightMem hrelation
  | stoppedOrdinary =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
          | fuelExhausted =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
      | done right =>
          exact hdoomed (pure (none, candidates)) right hrightMem hrelation
  | stoppedPrivate witness =>
      have hbase := relTriple_true
        (pure (some witness, candidates) : ProbComp PrivateWitnessPlanOutput)
        (finishDirectDetailedObserve rightObserve right)
      have hleft :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun source ↦ source = (some witness, candidates)) (by simp)
      apply relTriple_post_mono hleft
      intro source outcome hsource
      rw [hsource.2]
      exact witnessOrOrdinaryCovers_of_witness witness candidates outcome
  | done left =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
          | fuelExhausted =>
              exact relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers _
      | done right =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean left right hleftMem hrightMem hcleanRelation
          · exact hdoomed
              (leftObserve left.context left.remaining left.value candidates)
              right hrightMem hdoomedRelation

theorem probEvent_failed_le_witness_add_ordinary_of_relTriple
    (source : ProbComp PrivateWitnessPlanOutput)
    (detailed : ProbComp DirectBoundaryOutcome)
    (hrelation : RelTriple source detailed WitnessOrOrdinaryCovers) :
    Pr[fun outcome ↦ outcome.failed = true | detailed] ≤
      Pr[fun output ↦ output.1.isSome = true | source] +
        Pr[fun outcome ↦ outcome.ordinary = true | detailed] := by
  apply probEvent_le_failure_add_residual_of_relTriple detailed source
    (fun outcome output ↦ WitnessOrOrdinaryCovers output outcome)
    (fun outcome ↦ outcome.failed = true)
    (fun outcome ↦ outcome.ordinary = true)
    (fun output ↦ output.1.isSome = true)
    (relTriple_symm hrelation)
  intro outcome output hcovers hfailed hnotOrdinary
  rcases hcovers hfailed with hwitness | hordinary
  · exact hwitness
  · exact False.elim (hnotOrdinary hordinary)

end SphincsSecurity.Concrete.OtsProbeSimulation
