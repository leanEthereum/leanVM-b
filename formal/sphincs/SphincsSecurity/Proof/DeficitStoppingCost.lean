import SphincsSecurity.Proof.ExceptionUnionMonitor
import SphincsSecurity.Proof.AdaptiveNearUniformRaw

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)

theorem probEvent_runExceptionMonitor_deficitStoppingException_le
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    Pr[fun result => result.2 = true | runExceptionMonitor (deficitStoppingException key exception) computation cache hit] ≤
      Pr[fun result => result.2 = true | runExceptionMonitor exception computation cache hit] + (q : ENNReal) / 2 ^ 223 := by
  have h := probEvent_runExceptionMonitor_union_le exception (cacheEntryException (MessageDeficitExceptional key))
    computation cache hit false
  simp only [Bool.or_false] at h
  exact h.trans (add_le_add le_rfl (probEvent_messageDeficitExceptional_le key computation q hbound hq cache hfinite hnone))

theorem runWithFailure_monitor_projection
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (fun result => result.1.2) <$> runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed =
      evalDist (runExceptionMonitor exception
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit) := by
  calc
    _ = Prod.snd <$> (Prod.fst <$> runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed) := by
      simp only [Functor.map_map]
    _ = _ := by rw [runWithFailure_project, run_original]

theorem probEvent_runWithFailure_hit_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    Pr[fun result => result.1.2.2 = true | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] =
      Pr[fun result => result.2 = true | runExceptionMonitor exception
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit] := by
  have h := congrArg (fun distribution => Pr[fun result => result.2 = true | distribution])
    (runWithFailure_monitor_projection exception parameter root otsTable ftsTable computation frame cache hit failed)
  rw [probEvent_map] at h
  exact h

theorem probEvent_runWithFailure_deficitStoppingException_hit_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none) :
    Pr[fun result => result.1.2.2 = true |
      runWithFailure (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        parameter root otsTable ftsTable computation frame cache hit failed] ≤
      Pr[fun result => result.1.2.2 = true | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] +
        (q : ENNReal) / 2 ^ 223 := by
  rw [probEvent_runWithFailure_hit_eq, probEvent_runWithFailure_hit_eq]
  exact probEvent_runExceptionMonitor_deficitStoppingException_le _ exception _ q hbound hq cache hfinite hit hnone

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
