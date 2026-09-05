import SphincsSecurity.Proof.OtsProbePrivateAllowanceCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateProbeCutAllowance (target : Position) : Option (ResolvedRunResult (PrivateValueCut α)) → ENNReal
  | none => 0
  | some result => if DeferredCompletable result.table result.context then
      candidateFailureAllowance result.table result.context
        ((privateRawCutCandidate target result.remaining result.value).map (fun digest => ⟨.position target, digest⟩)) else 0

theorem expected_privateProbeCutAllowance_eq_zero_of_not_completable
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    (∑' result, Pr[= result | runResolvedFromTable context fuel table computation] * privateProbeCutAllowance target result) = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro option
  by_cases hoption : option ∈ support (runResolvedFromTable context fuel table computation)
  · cases option with
    | none => simp [privateProbeCutAllowance]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hoption
        have hstop := not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hoption hdoomed
        simp [privateProbeCutAllowance, hcore.1, hstop]
  · simp [probOutput_eq_zero_of_not_mem_support hoption]

theorem expected_privateProbeCutAllowance_eq_ordinalAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    (∑' result, Pr[= result | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] * privateProbeCutAllowance target result) =
      privateLiveProbeOrdinalAllowance target computation ordinal context fuel table := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [privatePositionProbeCutAt, runResolvedFromTable, privateLiveProbeOrdinalAllowance,
          privateProbeCutAllowance, hcomplete, privateRawCutCandidate, privatePositionAccessCandidate, candidateFailureAllowance, privateProbeInputAllowance]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [privatePositionProbeCutAt_query_bind, privateLiveProbeOrdinalAllowance_query_bind, if_pos hcomplete]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · rw [if_pos hdisclose, if_pos hdisclose]
          cases input <;> simp [IsPrivatePositionDisclosure] at hdisclose <;>
            simp [runResolvedFromTable, privateProbeCutAllowance, hcomplete,
              privateRawCutCandidate, privatePositionAccessCandidate, candidateFailureAllowance]
        · rw [if_neg hdisclose, if_neg hdisclose]
          have htail (n : Nat) :
              (∑' result, Pr[= result | runResolvedFromTable context fuel table
                ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
                  fun reply => privatePositionProbeCutAt target (next reply) n)] * privateProbeCutAllowance target result) =
              ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => privateLiveProbeOrdinalAllowance target (next result.value) n result.context result.remaining result.table := by
            rw [runResolvedFromTable_bind, tsum_probOutput_bind_mul]
            apply tsum_congr
            intro result
            by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
            · cases result with
              | none => simp [privateProbeCutAllowance, privateRawCutCandidate, privatePositionAccessCandidate, candidateFailureAllowance]
              | some result =>
                  have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                  dsimp only
                  rw [ih result.value n result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2)]
            · simp [probOutput_eq_zero_of_not_mem_support hresult]
          by_cases hprobe : IsPrivatePositionProbe target input
          · rw [if_pos hprobe]
            cases ordinal with
            | zero =>
                simp only [hprobe, and_self, if_true]
                cases input <;> simp [IsPrivatePositionProbe] at hprobe
                subst_vars
                simp [runResolvedFromTable, privateProbeCutAllowance, hcomplete,
                  privateRawCutCandidate, privatePositionAccessCandidate, candidateFailureAllowance, privateProbeInputAllowance]
            | succ ordinal =>
                simp only [hprobe, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, if_true, Nat.add_sub_cancel]
                rw [htail ordinal]
                apply tsum_congr
                intro result
                cases result <;> rfl
          · simp only [hprobe, false_and, if_false]
            rw [htail ordinal]
            apply tsum_congr
            intro result
            cases result <;> rfl
      · rw [expected_privateProbeCutAllowance_eq_zero_of_not_completable target (privatePositionProbeCutAt target _ ordinal) context fuel table hconsistent hstarts hcomplete,
          privateLiveProbeOrdinalAllowance_query_bind, if_neg hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
