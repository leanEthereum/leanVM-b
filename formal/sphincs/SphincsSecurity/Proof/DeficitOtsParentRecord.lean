import SphincsSecurity.Proof.DeficitExceptionRecord
import SphincsSecurity.Proof.JointProbeOriginalOtsParentRecord

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex OtsExceptionRecord FirstOtsParentRecord)

theorem firstDeficitOtsRecord_earlyTransition
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache)
    (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (actual, some record) ∈ support
      (runFirstException (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none))
    (hots : OtsExceptionRecord parameter record) :
    EarlyOtsParentTransition parameter otsTable ftsTable cache actual.2 := by
  have hmessage : ¬ MessageHashInput parameter record.input := by
    obtain ⟨position, hat, _⟩ := hots
    exact atPosition_not_message hat
  have hbase := firstDeficitExceptionRecord_support_nonmessage (secretKey parameter root otsTable ftsTable)
    exception _ cache hclean actual record hresult hmessage
  exact firstOtsRecord_earlyTransition exception parameter root otsTable ftsTable hparent input cache actual record hbase hots

theorem probEvent_firstDeficitOtsRecord_le_originalTransition
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache) :
    Pr[FirstOtsParentRecord parameter |
      runFirstException (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] ≤
    Pr[fun result => EarlyOtsParentTransition parameter otsTable ftsTable cache result.2 |
      (simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache] := by
  rw [← runFirstException_project (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
    _ cache none, probEvent_map]
  apply probEvent_mono
  intro result hresult hevent
  obtain ⟨record, hrecord, hots⟩ := hevent
  have hs : result.2 = some record := Option.mem_def.mp hrecord
  exact firstDeficitOtsRecord_earlyTransition exception parameter root otsTable ftsTable hparent input cache hclean
    result.1 record (by simpa only [← hs] using hresult) hots

theorem probEvent_firstDeficitOtsRecord_le_stepSharedFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache)
    (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    Pr[FirstOtsParentRecord parameter |
      runFirstException (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] ≤
    Pr[fun result => result.2 = true |
      stepWithFailure (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        parameter root otsTable ftsTable input (some frame) cache false false] := by
  apply (probEvent_firstDeficitOtsRecord_le_originalTransition exception parameter root otsTable ftsTable hparent
    input cache hclean).trans
  let stopped := deficitStoppingException (secretKey parameter root otsTable ftsTable) exception
  let event := fun result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec =>
    EarlyOtsParentTransition parameter otsTable ftsTable cache result.2
  have hm : (fun result => result.1.2.1) <$>
      stepWithFailure stopped parameter root otsTable ftsTable input (some frame) cache false false =
      evalDist ((simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache) := by
    calc
      _ = Prod.fst <$> (Prod.snd <$> (Prod.fst <$>
          stepWithFailure stopped parameter root otsTable ftsTable input (some frame) cache false false)) := by
            simp only [Functor.map_map]
      _ = _ := by rw [stepWithFailure_project, step_original, ← evalDist_map, runExceptionMonitor_project]
  have hp := congrArg (fun computation => Pr[event | computation]) hm
  rw [probEvent_map] at hp
  change Pr[fun result => event result.1.2.1 |
    stepWithFailure stopped parameter root otsTable ftsTable input (some frame) cache false false] =
    Pr[event | (simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache] at hp
  rw [← hp]
  apply probEvent_mono
  intro result hresult hearly
  exact stepWithFailure_earlyOtsParent_imp_failed stopped parameter root otsTable ftsTable input frame cache
    henabled hcomputed result hresult hearly

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
