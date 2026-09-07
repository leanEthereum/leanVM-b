import SphincsSecurity.Proof.JointProbeOriginalOtsParentRecord
import SphincsSecurity.Proof.JointProbeOriginalComputed
import SphincsSecurity.Proof.JointProbeOriginalFailurePersistence

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex OtsExceptionRecord FirstOtsParentRecord)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def FirstOtsOrClean (parameter : PublicParameter) (bad : α × QueryCache HashSpec → Prop)
    (result : (α × QueryCache HashSpec) × Option ExceptionRecord) : Prop :=
  FirstOtsParentRecord parameter result ∨ (result.2 = none ∧ bad result.1)

def SharedFailureOrClean (bad : α × QueryCache HashSpec → Prop)
    (result : (Option Frame × ((α × QueryCache HashSpec) × Bool)) × Bool) : Prop :=
  result.2 = true ∨ (result.1.2.2 = false ∧ bad result.1.2.1)

noncomputable def firstOtsContinuationCost
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (bad : α × QueryCache HashSpec → Prop) (result : (β × QueryCache HashSpec) × Bool) : ENNReal :=
  if result.2 then
    if EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2 then 1 else 0
  else Pr[FirstOtsOrClean parameter bad | runFirstException exception
    (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next result.1.1)) result.1.2 none]

theorem firstOtsContinuationCost_le_one
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (bad : α × QueryCache HashSpec → Prop) (result : (β × QueryCache HashSpec) × Bool) :
    firstOtsContinuationCost exception parameter root otsTable ftsTable next cache bad result ≤ 1 := by
  unfold firstOtsContinuationCost
  split
  · split <;> simp
  · exact probEvent_le_one

theorem probEvent_firstOtsOrClean_query_bind_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool) (bad : α × QueryCache HashSpec → Prop) :
    Pr[FirstOtsOrClean parameter bad | runFirstException exception
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (OracleSpec.query input >>= next)) cache none] ≤
    ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache false failed] *
      firstOtsContinuationCost exception parameter root otsTable ftsTable next cache bad result.1.2 := by
  have hm := tsum_probOutput_map_mul
    (stepWithFailure exception parameter root otsTable ftsTable input frame cache false failed) Prod.fst
    (fun result => firstOtsContinuationCost exception parameter root otsTable ftsTable next cache bad result.2)
  rw [stepWithFailure_project] at hm
  have hflag := runFirstException_flag_projection exception
    (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none
  simp only [Option.isSome_none] at hflag
  rw [← hm, step_expect_original, ← hflag, tsum_probOutput_map_mul]
  rw [simulateQ_bind, simulateQ_spec_query, runFirstException_bind, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro head
  by_cases hh : head ∈ support (runFirstException exception
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none)
  · apply mul_le_mul' le_rfl
    cases hs : head.2 with
    | none => simp only [firstOtsContinuationCost, Option.isSome_none, Bool.false_eq_true, if_false, le_refl]
    | some record =>
        by_cases ho : OtsExceptionRecord parameter record
        · have he := firstOtsRecord_earlyTransition exception parameter root otsTable ftsTable hparent input cache head.1 record
            (by simpa only [← hs] using hh) ho
          simp only [firstOtsContinuationCost, Option.isSome_some, if_true, he]
          exact probEvent_le_one
        · rw [runFirstException_some, probEvent_map]
          have hz : Pr[fun result => FirstOtsOrClean parameter bad (result, some record) |
              (simulateQ romImpl (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
                (next head.1.1))).run head.1.2] = 0 := by
            apply probEvent_eq_zero_iff.mpr
            intro result _ hevent
            rcases hevent with ⟨other, hother, hots⟩ | ⟨hnone, _⟩
            · have heq : record = other := Option.some.inj (Option.mem_def.mp hother)
              exact ho (heq ▸ hots)
            · contradiction
          change Pr[fun result => FirstOtsOrClean parameter bad (result, some record) | _] ≤ _
          rw [hz]
          exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hh, zero_mul, zero_mul]

theorem probEvent_firstOtsOrClean_le_runWithFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (bad : α × QueryCache HashSpec → Prop) :
    Pr[FirstOtsOrClean parameter bad | runFirstException exception
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache none] ≤
    Pr[SharedFailureOrClean bad | runWithFailure exception parameter root otsTable ftsTable computation (some frame) cache false false] := by
  induction computation using OracleComp.inductionOn generalizing frame cache with
  | pure value =>
      simp [simulateQ_pure, runFirstException, runWithFailure_pure, FirstOtsOrClean, FirstOtsParentRecord, SharedFailureOrClean]
  | query_bind input next ih =>
      have hh : OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel := by
        rw [isQueryBoundP_query_bind_iff] at hbound
        exact fun hi => hbound.1.elim (fun hn => False.elim (hn hi)) id
      have he : frame.Enabled parameter otsTable ftsTable input cache false := ⟨rfl, hvalid, hh⟩
      apply (probEvent_firstOtsOrClean_query_bind_le exception parameter root otsTable ftsTable hparent input next
        (some frame) cache false bad).trans
      rw [runWithFailure_query_bind, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro head
      by_cases hs : head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)
      · apply mul_le_mul' le_rfl
        cases hf : head.2 with
        | true =>
            have hone : Pr[SharedFailureOrClean bad | runWithFailure exception parameter root otsTable ftsTable
                (next head.1.2.1.1) head.1.1 head.1.2.1.2 head.1.2.2 true] = 1 := by
              apply probEvent_eq_one_iff.mpr
              exact ⟨runWithFailure_probFailure_eq_zero exception parameter root otsTable ftsTable _ _ _ _ _,
                fun result hr => Or.inl (runWithFailure_failed exception parameter root otsTable ftsTable _ _ _ _ result hr)⟩
            rw [hone]
            exact firstOtsContinuationCost_le_one exception parameter root otsTable ftsTable next cache bad head.1.2
        | false =>
            cases ho : head.1.2.2 with
            | true =>
                have hn : ¬ EarlyOtsParentTransition parameter otsTable ftsTable cache head.1.2.1.2 := by
                  intro ht
                  have hfailed := stepWithFailure_earlyOtsParent_imp_failed exception parameter root otsTable ftsTable
                    input frame cache he hcomputed head hs ht
                  simp [hf] at hfailed
                simp only [firstOtsContinuationCost, ho, if_true, hn, if_false]
                exact zero_le
            | false =>
                have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input (some frame) cache false false head hs
                have hv := stepWithFailure_invariant exception parameter root otsTable ftsTable input (some frame) cache false false
                  (fun live hlive => Option.some.inj hlive ▸ hvalid)
                  (fun live hlive => Option.some.inj hlive ▸ hh) rfl head hs
                cases hm : head.1.1 with
                | none => simp [hm, ho, hf] at hv
                | some middle =>
                    have hmiddle := (step_valid exception parameter root otsTable ftsTable input (some frame) cache false head.1 hp middle hm).1
                    have hnext := step_queryBound exception parameter root otsTable ftsTable input next frame cache false hbound head.1 hp middle hm
                    have hc := step_computed exception parameter root otsTable ftsTable input frame cache false hcomputed head.1 hp middle hm
                    simp only [firstOtsContinuationCost, ho, Bool.false_eq_true, if_false]
                    exact ih head.1.2.1.1 middle head.1.2.1.2 hmiddle hnext hc
      · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
