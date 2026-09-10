import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Structural boundary first fire

Canonical signer boundaries hide materialized values that were not published while retaining their
private structural copy. A later probe can make such a context impossible only by naming the
truncated private value. This file isolates that exact discrepancy from ordinary clean execution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

def PrivateStructuralHit (context : DeferredContext) : Prop :=
  ∃ position output,
    context.state.values (.position position) = none ∧
      context.values position = some output ∧
      context.state.hitAt (.position position) output

theorem DeferredCompletion.not_privateStructuralHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    ¬PrivateStructuralHit context := by
  rintro ⟨position, output, _hhidden, hprivate, hhit⟩
  have hcompletionOutput : completion (.position position) = output :=
    hcompletion.2.1 position output hprivate
  have hpending :
      (Coordinate.position position, truncateHash output) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  have havoids := hcompletion.2.2.1 (.position position) (truncateHash output) hpending
  rw [hcompletionOutput] at havoids
  exact havoids rfl

theorem not_privateStructuralHit_of_deferredCompletable
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) :
    ¬PrivateStructuralHit context := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  exact hcompletion.not_privateStructuralHit

inductive DirectBoundaryOutcome where
  | success
  | ordinaryFailure
  | privateStructuralFailure
deriving DecidableEq

def DirectBoundaryOutcome.failed : DirectBoundaryOutcome → Bool
  | .success => false
  | .ordinaryFailure => true
  | .privateStructuralFailure => true

def DirectBoundaryOutcome.privateStructural : DirectBoundaryOutcome → Bool
  | .privateStructuralFailure => true
  | _ => false

def DirectBoundaryOutcome.ordinary : DirectBoundaryOutcome → Bool
  | .ordinaryFailure => true
  | _ => false

def DirectBoundaryOutcome.ofFailed : Bool → DirectBoundaryOutcome
  | false => .success
  | true => .ordinaryFailure

@[simp] theorem DirectBoundaryOutcome.failed_ofFailed (failed : Bool) :
    (DirectBoundaryOutcome.ofFailed failed).failed = failed := by
  cases failed <;> rfl

@[simp] theorem DirectBoundaryOutcome.ordinary_ofFailed (failed : Bool) :
    (DirectBoundaryOutcome.ofFailed failed).ordinary = failed := by
  cases failed <;> rfl

@[simp] theorem DirectBoundaryOutcome.ordinary_eq_true_iff
    (outcome : DirectBoundaryOutcome) :
    outcome.ordinary = true ↔ outcome = .ordinaryFailure := by
  cases outcome <;> simp [DirectBoundaryOutcome.ordinary]

@[simp] theorem DirectBoundaryOutcome.privateStructural_eq_true_iff
    (outcome : DirectBoundaryOutcome) :
    outcome.privateStructural = true ↔ outcome = .privateStructuralFailure := by
  cases outcome <;> simp [DirectBoundaryOutcome.privateStructural]

end SphincsSecurity.Concrete.OtsProbeSimulation
