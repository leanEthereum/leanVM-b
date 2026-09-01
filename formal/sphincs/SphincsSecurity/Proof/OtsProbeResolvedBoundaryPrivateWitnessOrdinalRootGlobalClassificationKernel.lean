import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassification

/-!
# Fixed-table diagnostic root kernel

The operational root-or-doomed coupling is composed with the diagnostic finalizer in this separate
module so the resulting relational proof term is compiled once before table sampling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonical_diagnosticRootRel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
        finishObservedMaterializedDiagnostic table)
      SnapshotObservedDiagnosticRootRel := by
  exact relTriple_finishObservedDiagnostic_of_rootOrDoomed table _ _
    (relTriple_granularAllCanonical_observedMaterialized_rootOrDoomed adversary parameter
      ftsSecret q table hbound)

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem hasExistingHiddenHit_of_mem_diagnosticFromTable_successfulDoomed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hq : q ≤ 2 ^ securityBits)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
        finishObservedMaterializedDiagnostic table))
    (hsuccess : outcome.SuccessfulDoomed) :
    outcome.HasExistingHiddenHit := by
  classical
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨before?, hbefore, hfinish⟩ := houtcome
  cases before? with
  | none =>
      have houtcomeEq : outcome = ⟨none, none, false⟩ := by
        simpa [finishObservedMaterializedDiagnostic] using hfinish
      have hfinalNone : outcome.final = none := congrArg
        ObservedMaterializedDiagnostic.final houtcomeEq
      simp [ObservedMaterializedDiagnostic.SuccessfulDoomed, hfinalNone] at hsuccess
  | some before =>
      unfold finishObservedMaterializedDiagnostic at hfinish
      rw [mem_support_bind_iff] at hfinish
      obtain ⟨final?, hfinal, hreturn⟩ := hfinish
      cases final? with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          have hfinalNone : outcome.final = none := by
            simpa using congrArg ObservedMaterializedDiagnostic.final hreturn
          simp [ObservedMaterializedDiagnostic.SuccessfulDoomed, hfinalNone] at hsuccess
      | some finalResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          have hbeforeEq : outcome.before = some before := by
            simpa using congrArg ObservedMaterializedDiagnostic.before hreturn
          have hdoomedEq : decide
              (¬DeferredCompletable table (directDeferredContext before.state)) = true := by
            have hfield := congrArg ObservedMaterializedDiagnostic.wasDoomed hreturn
            exact hfield.symm.trans hsuccess.2
          have hnotCompletable :
              ¬DeferredCompletable table (directDeferredContext before.state) := by
            simpa using of_decide_eq_true hdoomedEq
          have htracked :
              CleanProbeObservationsTrackedBy before.observations before.state := by
            simpa only [ObservedMaterializedOutputTracked] using
              observedMaterializedOutputTracked_of_mem_retainedRunFromTable adversary parameter
                ftsSecret (2 * q) table (some before) hbefore
          have hcovered :
              CleanProbeObservationsCoverPending before.observations before.state := by
            simpa only [ObservedMaterializedOutputCovered] using
              observedMaterializedOutputCovered_of_mem_retainedRunFromTable adversary parameter
                ftsSecret (2 * q) table (some before) hbefore
          have hpending : before.state.pending.card ≤ 2 * q :=
            pending_card_le_fuel_of_mem_observedMaterializedRetainedRunFromTable adversary parameter
              ftsSecret (2 * q) table before hbefore
          have htableAndStarts :
              before.table = table ∧ StartTableAgrees before.state table :=
            table_eq_and_startTableAgrees_of_mem_observedMaterializedRetainedRunFromTable
              adversary parameter ftsSecret (2 * q) table before hbefore
          have hcard : before.state.pending.card < Fintype.card Digest := by
            have hq' : 2 * q ≤ 2 ^ (securityBits + 1) := by
              have : 2 * q ≤ 2 * 2 ^ securityBits := Nat.mul_le_mul_left 2 hq
              simpa [pow_succ, Nat.mul_comm] using this
            have hspace : 2 ^ (securityBits + 1) < Fintype.card Digest := by
              norm_num [securityBits, digestBits]
            exact hpending.trans_lt (hq'.trans_lt hspace)
          have hconsistent :
              (directDeferredContext before.state).ValuesConsistent := by
            intro position output hvalue
            simpa [directDeferredContext, directDeferredValues] using hvalue
          have hdoomed :
              DoomedResolvedContext table (directDeferredContext before.state) :=
            ⟨hconsistent, htableAndStarts.2, hnotCompletable⟩
          exact ⟨before, hbeforeEq, hasExistingHiddenHit_of_doomed_finished table before finalResult
            htableAndStarts.1 hdoomed htracked hcovered hcard hfinal⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
