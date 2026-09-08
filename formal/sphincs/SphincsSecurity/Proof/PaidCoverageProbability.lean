import SphincsSecurity.Proof.AdaptivePaidCoverage
import SphincsSecurity.Proof.RemainingCoverageProbability

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_runWithFailure_liveCover_pairs_refund_le_reserved_add_residual
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
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedPaidCoverageRefund exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have h := expected_runWithFailure_coverage_pairs_refund_le_reserved_add_residual exception parameter root otsTable ftsTable
    q q hq computation frame (cache, []) hit failed hbound hsigned hcache
  have hsurvive : survivingLogPotential (fun current => remainingCoveragePotential key q q current ∅ Finset.univ *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹) (cache, []) hit failed ≤ (q : ENNReal) * initialRawIndexRate q := by
    rw [← remainingCoveragePotential_initial_scaled key q cache hnone]
    unfold survivingLogPotential
    split_ifs
    · exact zero_le
    · exact le_rfl
  apply le_trans ?_ (h.trans (add_le_add (add_le_add hsurvive le_rfl) le_rfl))
  apply add_le_add (add_le_add ?_ le_rfl) le_rfl
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [survivingLogPotential, hcover.1, hcover.2.1]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    exact le_mul_of_one_le_right' (one_le_cappedRemainingCachedTargetEnvelope_scaled_of_covered key q 0
      (result.1.2.1.2, result.1.2.1.1.2) hcover.2.2.1 hcover.2.2.2)
  · exact bot_le

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
