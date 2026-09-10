import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveJointCharge
import SphincsSecurity.Proof.OtsProbeLiveStartCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def nativeCutQueryCharge (charge : LazyRevealProbe.Query Coordinate → ENNReal) : PrivateValueCut α → ENNReal
  | .done _ => 0
  | .query input _ => charge input

noncomputable def liveNativeCutCharge (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (result : Option (ResolvedRunResult (PrivateValueCut α))) : ENNReal :=
  match retainCompletableResult result with
  | none => 0
  | some result => nativeCutQueryCharge charge result.value

noncomputable def expectedLiveNativeCutCharge (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable context fuel table computation] * liveNativeCutCharge charge result

theorem expectedLiveNativeCutCharge_pure (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (value : PrivateValueCut α) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveNativeCutCharge charge (pure value) context fuel table =
      if DeferredCompletable table context then nativeCutQueryCharge charge value else 0 := by
  by_cases hcomplete : DeferredCompletable table context <;>
    simp [expectedLiveNativeCutCharge, runResolvedFromTable, liveNativeCutCharge, retainCompletableResult, hcomplete]

theorem expectedLiveNativeCutCharge_bind (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) β)
    (next : β → OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveNativeCutCharge charge (computation >>= next) context fuel table =
      ∑' result, Pr[= result | runResolvedFromTable context fuel table computation] *
        match result with
        | none => 0
        | some result => expectedLiveNativeCutCharge charge (next result.value) result.context result.remaining result.table := by
  unfold expectedLiveNativeCutCharge
  rw [runResolvedFromTable_bind, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  cases result with
  | none => simp [liveNativeCutCharge, retainCompletableResult]
  | some result => rfl

theorem expectedLiveNativeCutCharge_eq_zero_of_not_completable
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    expectedLiveNativeCutCharge charge computation context fuel table = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable context fuel table computation)
  · cases result with
    | none => simp [liveNativeCutCharge, retainCompletableResult]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
        have hstill := not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult hdoomed
        simp [liveNativeCutCharge, retainCompletableResult, hcore.1, hstill]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem sum_expectedLiveNativeProbeCutCharge_le_expectedCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    (∑ ordinal ∈ Finset.range q, expectedLiveNativeCutCharge charge (nativeProbeCutAt computation ordinal) context fuel table) ≤
      expectedLiveResolvedQueryCharge charge computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => simp [nativeProbeCutAt, expectedLiveNativeCutCharge_pure, nativeCutQueryCharge, expectedLiveResolvedQueryCharge]
  | query_bind input next ih =>
      rw [expectedLiveResolvedQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        have htail (n : Nat) :
            (∑ ordinal ∈ Finset.range n, expectedLiveNativeCutCharge charge
              ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
                fun output => nativeProbeCutAt (next output) ordinal) context fuel table) ≤
            ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
              match result with
              | none => 0
              | some result => expectedLiveResolvedQueryCharge charge (next result.value) result.context result.remaining result.table := by
          simp only [expectedLiveNativeCutCharge_bind]
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
          · cases result with
            | none => simp
            | some result =>
                have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                simp only [← Finset.mul_sum]
                exact mul_le_mul' le_rfl (ih result.value n result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2))
          · simp [probOutput_eq_zero_of_not_mem_support hresult]
        by_cases hprobe : LazyRevealProbe.IsProbe input
        · cases q with
          | zero => simp
          | succ q =>
              rw [Finset.sum_range_succ']
              simp only [nativeProbeCutAt_query_bind, if_pos hprobe, expectedLiveNativeCutCharge_pure,
                if_pos hcomplete, nativeCutQueryCharge]
              exact (add_le_add (htail q) le_rfl).trans_eq (add_comm _ _)
        · simp only [nativeProbeCutAt_query_bind, if_neg hprobe]
          exact (htail q).trans le_add_self
      · rw [if_neg hcomplete]
        simp only [expectedLiveNativeCutCharge_eq_zero_of_not_completable charge _ context fuel table hconsistent hstarts hcomplete,
          Finset.sum_const_zero, le_refl]

theorem unresolvedStartCandidateCharge_nativeCut_le
    (context : DeferredContext) (cut : PrivateValueCut α) :
    unresolvedStartCandidateCharge context (nativeCutCandidate context cut) ≤ nativeCutQueryCharge chainStartProbeQueryCharge cut := by
  cases cut with
  | done value => simp [nativeCutCandidate, unresolvedStartCandidateCharge, nativeCutQueryCharge]
  | query input next =>
      cases input with
      | probe coordinate digest =>
          cases coordinate with
          | position position => simp [nativeCutCandidate, unresolvedStartCandidateCharge, nativeCutQueryCharge, chainStartProbeQueryCharge]
          | chainStart lay tree leafIdx chainIdx =>
              simp only [nativeCutCandidate, unresolvedStartCandidateCharge, nativeCutQueryCharge, chainStartProbeQueryCharge]
              split_ifs
              · have h := candidateCharge_sum_le_one (materializedDeferredState context) (some ⟨.chainStart lay tree leafIdx chainIdx, digest⟩)
                exact_mod_cast (Nat.le_add_right _ _).trans h
              · exact zero_le
      | _ => simp [nativeCutCandidate, unresolvedStartCandidateCharge, nativeCutQueryCharge, chainStartProbeQueryCharge]

theorem historyUnresolvedStartCharge_le_liveNativeCutCharge
    (result : Option (ResolvedRunResult (PrivateValueCut α))) :
    historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result) ≤
      liveNativeCutCharge chainStartProbeQueryCharge result := by
  unfold liveNativeCutCharge
  cases hresult : retainCompletableResult result with
  | none => simp [historyUnresolvedStartCharge]
  | some result => exact unresolvedStartCandidateCharge_nativeCut_le result.context result.value

end SphincsSecurity.Concrete.OtsProbeSimulation
