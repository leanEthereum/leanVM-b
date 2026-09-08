import SphincsSecurity.Proof.NearUniformOrderArithmetic
import SphincsSecurity.Proof.NearUniformCoverageProbability

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem finiteNearUniformInitialMixedEnvelope_le (q : Nat) (hq : q ≤ 2 ^ 127) :
    finiteNearUniformInitialMixedEnvelope q ≤ (3 : ENNReal) * 2 ^ 44 :=
  (finiteNearUniformInitialMixedEnvelope_le_signingFactorial q hq).trans nearUniformSigningFactorialEnvelope_le

theorem initialNearUniformRawIndexRate_le (q : Nat) (hq : q ≤ 2 ^ 127) :
    initialNearUniformRawIndexRate q ≤ (3 / 16 : ENNReal) * ((2 ^ 128 : Nat) : ENNReal)⁻¹ := by
  unfold initialNearUniformRawIndexRate
  rw [initialNearUniformTargetIndexEnvelope_eq_finite]
  apply (mul_le_mul' (finiteNearUniformInitialMixedEnvelope_le q hq) le_rfl).trans_eq
  have hl : (3 : ENNReal) * 2 ^ 44 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≠ ⊤ := by finiteness
  have hr : (3 / 16 : ENNReal) * ((2 ^ 128 : Nat) : ENNReal)⁻¹ ≠ ⊤ := by finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem probEvent_runWithFailure_liveCover_add_nearUniformUnused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hdetect : ∀ cache input answer,
      MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) (cache.cacheQuery input answer) →
        exception cache input answer)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedReuseUnusedCoverageCharge exception parameter root otsTable ftsTable nearUniformDigestReuseWeight ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * (3 / 16 : ENNReal) * ((2 ^ 128 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_runWithFailure_liveCover_add_nearUniformUnused_le_initial
    exception parameter root otsTable ftsTable hdetect q hq computation hbound frame cache hit failed hnone hcache).trans
  simpa only [mul_assoc] using mul_le_mul' (le_refl (q : ENNReal)) (initialNearUniformRawIndexRate_le q hq)

theorem probEvent_runWithFailure_deficitStopped_liveCover_add_unused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception) parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedReuseUnusedCoverageCharge (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        parameter root otsTable ftsTable nearUniformDigestReuseWeight ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * (3 / 16 : ENNReal) * ((2 ^ 128 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_runWithFailure_deficitStopped_liveCover_add_unused_le_initial
    exception parameter root otsTable ftsTable q hq computation hbound frame cache hit failed hnone hcache).trans
  simpa only [mul_assoc] using mul_le_mul' (le_refl (q : ENNReal)) (initialNearUniformRawIndexRate_le q hq)

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
