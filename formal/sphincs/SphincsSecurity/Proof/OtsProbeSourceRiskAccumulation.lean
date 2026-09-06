import SphincsSecurity.Proof.OtsProbePrimitiveRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveProbeFailureAllowance (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        probeFailureInputAllowance table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

theorem liveProbeFailureAllowance_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    liveProbeFailureAllowance ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input) :
      OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        probeFailureInputAllowance table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table
            (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input))] *
            match result with
            | none => 0
            | some result => liveProbeFailureAllowance (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem probEvent_source_finish_le_initial_add_probeAllowance
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbudget : q < fuel) (hspace : context.state.pending.card + fuel < Fintype.card Digest) :
    Pr[fun verdict => verdict = true | runResolvedFromTable context fuel table computation >>= finishResolvedRunIsNone] ≤
      resolvedContextFailureRisk table context + liveProbeFailureAllowance computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value =>
      simp only [runResolvedFromTable, construct_pure, pure_bind, liveProbeFailureAllowance, add_zero]
      rw [finishResolvedRunIsNone_metadata_eq context table fuel 0 value ()]
      exact le_rfl
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [isQueryBoundP_query_bind_iff] at hbound
        let queryRun := runResolvedFromTable context fuel table
          (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input))
        let tailCharge := fun option : Option (ResolvedRunResult ((LazyRevealProbe.World Coordinate).Range input)) =>
          match option with
          | none => (0 : ENNReal)
          | some result => liveProbeFailureAllowance (next result.value) result.context result.remaining result.table
        have hstep := probEvent_resolved_query_finish_le_allowance input context fuel table hconsistent hstarts (by omega) (by omega)
        rw [probEvent_finished_eq_expected_outcomeRisk] at hstep
        rw [runResolvedFromTable_bind, bind_assoc, probEvent_bind_eq_tsum]
        calc
          _ ≤ ∑' option, Pr[= option | queryRun] * (resolvedOutcomeFailureRisk option + tailCharge option) := by
            apply ENNReal.tsum_le_tsum
            intro option
            by_cases hoption : option ∈ support queryRun
            · cases option with
              | none => simp [queryRun, resolvedOutcomeFailureRisk, tailCharge, finishResolvedRunIsNone, finishResolvedRun]
              | some result =>
                  have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
                  have hstepBound : (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _).IsQueryBoundP
                      LazyRevealProbe.IsProbe (if LazyRevealProbe.IsProbe input then 1 else 0) := by
                    by_cases hprobe : LazyRevealProbe.IsProbe input <;> simp [hprobe]
                  have hfuel := (fuel_bounds_of_mem_runResolvedFromTable _ context fuel _ table result hstepBound hoption).2
                  have hremaining := pending_add_remaining_le_of_mem_resolved_query input context fuel table result hoption
                  apply mul_le_mul' le_rfl
                  exact ih result.value _ result.context result.remaining result.table (hbound.2 result.value)
                    hcore.2.1 (by rw [hcore.1]; exact hcore.2.2)
                    (by
                      by_cases hprobe : LazyRevealProbe.IsProbe input
                      · have hpositive := hbound.1.resolve_left (not_not.mpr hprobe)
                        simp only [hprobe, if_true] at hfuel ⊢
                        omega
                      · simp only [hprobe, if_false] at hfuel ⊢
                        omega)
                    (hremaining.trans_lt hspace)
            · change Pr[= option | queryRun] * _ ≤ _
              simp only [show Pr[= option | queryRun] = 0 from probOutput_eq_zero_of_not_mem_support hoption, zero_mul, le_refl]
          _ = (∑' option, Pr[= option | queryRun] * resolvedOutcomeFailureRisk option) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
          _ ≤ (resolvedContextFailureRisk table context + probeFailureInputAllowance table context input) +
              ∑' option, Pr[= option | queryRun] * tailCharge option := add_le_add hstep le_rfl
          _ = _ := by
            rw [liveProbeFailureAllowance_query_bind, if_pos hcomplete]
            exact add_assoc _ _ _
      · rw [liveProbeFailureAllowance_query_bind, if_neg hcomplete,
          resolvedContextFailureRisk_of_not_completable table context hcomplete, add_zero]
        exact probEvent_le_one

end SphincsSecurity.Concrete.OtsProbeSimulation
