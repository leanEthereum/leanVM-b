import SphincsSecurity.Proof.AdaptiveNearUniformRaw
import SphincsSecurity.Proof.InitialRawIndexEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem reuseRawEnvelope_initial (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    reuseRawEnvelope key reuse queries signatures (cache, []) groups remaining =
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
        initialTargetIndexVector groups.card remaining.card := by
  unfold reuseRawEnvelope observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid, targetIndexMoments_initial key cache hnone]

theorem validRawIndexShape_le_cappedReuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (if SigningTranscript.Valid state.2 then observedRawIndexShapeVector key state groups remaining else 0) ≤
      cappedReuseRawEnvelope key reuse budget state groups remaining := by
  unfold cappedReuseRawEnvelope
  split_ifs
  · exact le_targetShapeEnvelope _ _ _ _ _ _ groups remaining
  · exact le_rfl

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem expected_runWithFailure_deficitStopped_raw_le_initial
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) q)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception) parameter root otsTable ftsTable
        (withSigningLog computation []) frame cache false failed] *
      survivingLogPotential (fun current => if SigningTranscript.Valid current.2 then
        observedRawIndexShapeVector (secretKey parameter root otsTable ftsTable) current groups remaining else 0)
          (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) ≤
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
        initialTargetIndexVector groups.card remaining.card := by
  let key := secretKey parameter root otsTable ftsTable
  have h := expected_runWithFailure_deficitStopped_raw_le exception parameter root otsTable ftsTable q hq computation
    frame cache failed hbound hcache (fun payload => hnone _ ⟨payload, rfl⟩) groups remaining hvalid
  simp only [cappedReuseRawEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _),
    List.length_nil, Nat.sub_zero] at h
  rw [reuseRawEnvelope_initial key nearUniformDigestReuseWeight q signatureLimit cache hnone groups remaining hvalid] at h
  apply le_trans _ h
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  unfold survivingLogPotential
  split_ifs
  · exact le_rfl
  · exact validRawIndexShape_le_cappedReuseRawEnvelope key nearUniformDigestReuseWeight 0 _ groups remaining

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
