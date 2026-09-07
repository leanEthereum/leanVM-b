import SphincsSecurity.Proof.JointProbeOriginalOtsParent
import SphincsSecurity.Proof.FirstOtsParentQuery

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex OtsExceptionRecord FirstOtsParentRecord)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem firstOtsRecord_earlyTransition
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (actual, some record) ∈ support
      (runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none))
    (hots : OtsExceptionRecord parameter record) :
    EarlyOtsParentTransition parameter otsTable ftsTable cache actual.2 := by
  let key := secretKey parameter root otsTable ftsTable
  have hw : ∃ child parent, AtPosition parameter record.input child ∧ child.parentOf = some parent ∧
      ¬ Settled parameter key.otsSecret key.ftsSecret cache child ∧
      Settled parameter key.otsSecret key.ftsSecret actual.2 parent ∧
      cache (cachedInput parameter key.otsSecret key.ftsSecret actual.2 parent) ≠ none := by
    cases input with
    | inl query =>
        have hcache := firstExceptionRecord_query_cache exception query cache actual record hresult
        have hv := runFirstException_none_valid exception (expandedAdversaryImpl key (.inl query)) cache hresult record (by simp)
        obtain ⟨child, parent, hat, hpar, hb, _, _, ha, hcached, _⟩ :=
          (hparent _ _ _ hv.2.2.1).exists_full_parent_input parameter key.otsSecret key.ftsSecret hv.2.2.2
        exact ⟨child, parent, hat, hpar, hcache ▸ hb, ha, hcache ▸ hcached⟩
    | inr message =>
        exact firstExceptionRecord_sign_parent_input_initial key exception hparent message cache actual record hresult le_rfl
  obtain ⟨child, parent, hat, hpar, hb, ha, hcached⟩ := hw
  obtain ⟨position, hposition, hots⟩ := hots
  have heq := atPosition_unique parameter hposition hat
  exact ⟨child, parent, (heq ▸ hots).parent hpar, Position.mem_children_iff.mpr hpar, hb, ha, hcached⟩

theorem probEvent_firstOtsRecord_le_originalTransition
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    Pr[FirstOtsParentRecord parameter |
      runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] ≤
    Pr[fun result => EarlyOtsParentTransition parameter otsTable ftsTable cache result.2 |
      (simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache] := by
  rw [← runFirstException_project exception _ cache none, probEvent_map]
  apply probEvent_mono
  intro result hresult hevent
  obtain ⟨record, hrecord, hots⟩ := hevent
  have hs : result.2 = some record := Option.mem_def.mp hrecord
  have hr : (result.1, some record) ∈ support
      (runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none) := by
    simpa only [← hs] using hresult
  exact firstOtsRecord_earlyTransition exception parameter root otsTable ftsTable hparent input cache result.1 record hr hots

private theorem probEvent_evalDist_eq (computation : ProbComp α) (event : α → Prop) :
    Pr[event | evalDist computation] = Pr[event | computation] := rfl

theorem probEvent_firstOtsRecord_le_stepSharedFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    Pr[FirstOtsParentRecord parameter |
      runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] ≤
    Pr[fun result => result.2 = true |
      stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] := by
  apply (probEvent_firstOtsRecord_le_originalTransition exception parameter root otsTable ftsTable hparent input cache).trans
  let event := fun result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec =>
    EarlyOtsParentTransition parameter otsTable ftsTable cache result.2
  have hm : (fun result => result.1.2.1) <$>
      stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false =
      evalDist ((simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache) := by
    calc
      _ = Prod.fst <$> (Prod.snd <$> (Prod.fst <$>
          stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)) := by
            simp only [Functor.map_map]
      _ = _ := by
        rw [stepWithFailure_project, step_original, ← evalDist_map, runExceptionMonitor_project]
  have hp := congrArg (fun computation => Pr[event | computation]) hm
  rw [probEvent_map, probEvent_evalDist_eq] at hp
  rw [← hp]
  apply probEvent_mono
  intro result hresult hearly
  exact stepWithFailure_earlyOtsParent_imp_failed exception parameter root otsTable ftsTable input frame cache henabled hcomputed
    result hresult hearly

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
