import SphincsSecurity.Proof.DirectParentCacheBudget
import SphincsSecurity.Proof.DirectParentReleaseBudget
import SphincsSecurity.Proof.BeforeFailureSigningCacheCap
import SphincsSecurity.Proof.PreExceptionCacheCap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

noncomputable def crossFtsParentReleaseCharge (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  ((parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache -
      directParentRelease key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache input : Nat) : ENNReal) *
    min 1 (directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹)

theorem localizedFtsParentReleaseCharge_eq_direct_add_cross (key : SecretKey) :
    localizedFtsParentReleaseCharge key = fun cache input => directFtsParentReleaseCharge key cache input + crossFtsParentReleaseCharge key cache input := rfl

theorem crossFtsParentReleaseCharge_le_all_direct_scaled (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (cap : Nat) (hcap : QueryCache.enncard cache ≤ cap) (input : HashInput) :
    crossFtsParentReleaseCharge key cache input ≤
      directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input *
        ((cap : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hparent := (Nat.cast_le.mpr (Nat.sub_le
    (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache)
    (directParentRelease key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache input))).trans
      ((parentReserve_le_enncard key.parameter key.otsSecret key.ftsSecret _ cache hfinite).trans hcap)
  have h := mul_le_mul' hparent (min_le_right (1 : ENNReal)
    (directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹))
  unfold crossFtsParentReleaseCharge
  convert h using 1 <;> first | rfl | ring

namespace FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureDirectParentCharge_le_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (eligible : Position → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) (cap : Nat)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureCharge exception (directParentQueryCharge key.parameter key.otsSecret key.ftsSecret eligible)
      parameter root otsTable ftsTable computation frame cache hit failed ≤ cap :=
  ((expectedBeforeFailureCharge_le_preExceptionCharge exception _ parameter root otsTable ftsTable computation frame cache hit failed).trans
    (expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit)).trans
      (expected_directParentQueryCharge_le_cache_cap key.parameter key.otsSecret key.ftsSecret eligible
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hfinite cap
        (runWithFailure_original_cache_cap exception parameter root otsTable ftsTable computation frame cache hit failed cap hcap))

theorem expectedBeforeFailureCrossParentCharge_le_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) (cap : Nat)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureCharge exception (crossFtsParentReleaseCharge key)
      parameter root otsTable ftsTable computation frame cache hit failed ≤
      (cap : ENNReal) * ((cap : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let raw := simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation
  have hc := runWithFailure_original_cache_cap exception parameter root otsTable ftsTable computation frame cache hit failed cap hcap
  apply (expectedBeforeFailureCharge_le_preExceptionCharge exception _ parameter root otsTable ftsTable computation frame cache hit failed).trans
  have h := expectedPreExceptionCharge_mono_of_cache_cap exception (crossFtsParentReleaseCharge key)
    (fun current input => directParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun _ => True) current input *
      ((cap : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹)) cap
    (fun current hf hc input => crossFtsParentReleaseCharge_le_all_direct_scaled key current hf cap hc input) raw cache hfinite hit hc
  rw [expectedPreExceptionCharge_mul] at h
  exact h.trans (mul_le_mul' ((expectedPreExceptionCharge_le_queryCharge exception _ raw cache hit).trans
    (expected_directParentQueryCharge_le_cache_cap key.parameter key.otsSecret key.ftsSecret (fun _ => True) raw cache hfinite cap hc)) le_rfl)

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
