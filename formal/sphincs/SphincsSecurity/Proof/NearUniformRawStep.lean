import SphincsSecurity.Proof.CappedReuseRawEnvelope
import SphincsSecurity.Proof.MessageDeficitReuse
import SphincsSecurity.Proof.StoppedTargetPotentials

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def nearUniformDigestReuseWeight : ENNReal :=
  (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹

theorem nearUniformDigestReuseWeight_ne_top : nearUniformDigestReuseWeight ≠ ⊤ := by
  unfold nearUniformDigestReuseWeight
  finiteness

theorem exactDigestReuseWeight_le_near_uniform_of_clean_cache (key : SecretKey) (cache : QueryCache HashSpec)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ cap)
    (hclean : ¬ MessageDeficitExceptional key cache) (message : Message) :
    exactDigestReuseWeight key message cache ≤ nearUniformDigestReuseWeight :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message cache cap hcap hcache
    (le_of_not_gt (fun h => hclean ⟨message, h⟩))

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem stepWithFailure_deficit_clean
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hdetect : ∀ cache input answer,
      MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) (cache.cacheQuery input answer) →
        exception cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hclean : hit = false → ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache)
    (result : FailureStepResult input)
    (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed))
    (hnoHit : result.1.2.2 = false) :
    ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) result.1.2.1.2 :=
  runExceptionMonitor_clean_of_detects _ exception hdetect _ cache hit hclean result.1.2
    (stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr) hnoHit

theorem stepWithFailure_nearUniformRawEnvelope_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget)
    (hclean : hit = false → ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) state.1)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight (budget - signingExecutionHashCost input) current groups remaining)
        (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      survivingLogPotential (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight budget current groups remaining) state hit failed := by
  by_cases hstop : (hit || failed) = true
  · rw [survivingLogPotential, if_pos hstop]
    have h := stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed
      (fun current => cappedReuseRawEnvelope (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight (budget - signingExecutionHashCost input) current groups remaining) ⊤ le_top
    simpa only [hstop, if_true] using h
  · have hhit : hit = false := by cases hit <;> simp_all
    exact stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed _ _
      (expected_logTraced_cappedReuseRawEnvelope_le (secretKey parameter root otsTable ftsTable)
        nearUniformDigestReuseWeight budget state hsigned
        (exactDigestReuseWeight_le_near_uniform_of_clean_cache _ state.1 cap hcap hcache (hclean hhit))
        input hcost groups remaining hvalid)

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
