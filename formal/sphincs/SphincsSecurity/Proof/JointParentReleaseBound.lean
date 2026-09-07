import SphincsSecurity.Proof.StoppedParentReleaseBound
import SphincsSecurity.Proof.FiniteQueryChargeMonotonicity
import SphincsSecurity.Proof.JointParentReserveConservation

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

noncomputable def localizedFtsParentReleaseCharge (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache input +
    (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal) *
      directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹

theorem releasedFtsParentQueryCharge_le_localized
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedFtsParentQueryCharge key cache input ≤ localizedFtsParentReleaseCharge key cache input :=
  releasedParentQueryCharge_le_direct_add_scaled key.parameter key.otsSecret key.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) hfinite input

theorem releasedFtsParentQueryCharge_add_discard_le_localized
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedFtsParentQueryCharge key cache input + discardedFtsParentQueryCharge exception key cache input ≤
      localizedFtsParentReleaseCharge key cache input :=
  releasedParentQueryCharge_add_discard_le_direct_add_scaled key.parameter key.otsSecret key.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) exception hsub cache hfinite input

namespace FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureFtsParentRelease_le_localized
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (releasedFtsParentQueryCharge key) parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (localizedFtsParentReleaseCharge key) parameter root otsTable ftsTable computation frame cache hit failed :=
  expectedBeforeFailureCharge_mono_of_finite exception _ _ (releasedFtsParentQueryCharge_le_localized key)
    parameter root otsTable ftsTable computation frame cache hfinite hit failed

theorem expectedBeforeFailureFtsParentRelease_add_discard_le_localized
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (releasedFtsParentQueryCharge key) parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureCharge exception (discardedFtsParentQueryCharge exception key) parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (localizedFtsParentReleaseCharge key) parameter root otsTable ftsTable computation frame cache hit failed := by
  rw [← expectedBeforeFailureCharge_add]
  exact expectedBeforeFailureCharge_mono_of_finite exception _ _ (releasedFtsParentQueryCharge_add_discard_le_localized exception key hsub)
    parameter root otsTable ftsTable computation frame cache hfinite hit failed

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
