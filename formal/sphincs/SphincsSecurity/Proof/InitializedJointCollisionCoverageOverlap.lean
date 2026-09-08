import SphincsSecurity.Proof.JointCollisionCoverageOverlap
import SphincsSecurity.Proof.BeforeFailureChargeTrace
import SphincsSecurity.Proof.InitializedJointCollisionCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedJointCollisionCoverageOverlap (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  min 1 ((q : ENNReal) * initialRawIndexRate q) *
      Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] +
    ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedJointCollisionCoverageOverlap parameter initial.2.1 otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone

theorem initializedJointCollisionCoverageCharge_add_overlap_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedJointCollisionCoverageCharge adversary parameter otsTable ftsTable q fuel +
      initializedJointCollisionCoverageOverlap adversary parameter otsTable ftsTable q fuel ≤
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  rw [initializedJointCollisionCoverageCharge, initializedJointCollisionCoverageOverlap, add_add_add_comm,
    ← add_mul, tsub_add_cancel_of_le (min_le_left _ _), one_mul, ← ENNReal.tsum_add]
  have hbound : (∑' initial, (Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedJointCollisionCoverageCharge parameter initial.2.1 otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone +
      Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedJointCollisionCoverageOverlap parameter initial.2.1 otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone)) ≤
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        (if initial.1.isNone then 0 else Pr[fun result => result.2 = true | runWithFailure (parentException parameter otsTable ftsTable)
          parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone]) := by
    rw [initializedBeforeFailureCollisionCharge, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro initial
    rw [← mul_add, mul_assoc, ← mul_add]
    have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
      (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
    rw [expectedBeforeFailureCharge_retainedComputation _ _ adversary parameter initial.2.1 otsTable ftsTable q htrace,
      probEvent_retainedComputation_failed_eq_unlogged _ adversary parameter initial.2.1 otsTable ftsTable q htrace]
    exact mul_le_mul' le_rfl (expectedJointCollisionCoverageCharge_add_overlap_le_failure_add_collision parameter initial.2.1 otsTable ftsTable q q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone)
  apply (add_le_add le_rfl hbound).trans_eq
  rw [add_left_comm]
  congr 1
  rw [runRetainedWithFailure, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro initial
  cases hf : initial.1 with
  | none => simp only [Option.isNone_none, if_true, mul_zero, add_zero, probEvent_runWithFailure_failed_eq_one, mul_one]
  | some frame => simp only [Option.isNone_some, reduceCtorEq, if_false, zero_add]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
