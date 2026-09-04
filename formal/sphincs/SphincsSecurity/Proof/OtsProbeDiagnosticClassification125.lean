import SphincsSecurity.Proof.OtsProbeStopped125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option linter.constructorNameAsVariable false

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem hasExistingHiddenHit_of_mem_diagnosticFromTable_successfulDoomed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hq : q ≤ 2 ^ 125)
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
            have hq' : 2 * q ≤ 2 ^ (125 + 1) := by
              have : 2 * q ≤ 2 * 2 ^ 125 := Nat.mul_le_mul_left 2 hq
              simpa [pow_succ, Nat.mul_comm] using this
            have hspace : 2 ^ (125 + 1) < Fintype.card Digest := by
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

attribute [local irreducible] observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ 125)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)))
    (hsuccess : outcome.SuccessfulDoomed) :
    outcome.HasExistingHiddenHit := by
  change outcome ∈ support (sampleOtsHashTable >>= fun table =>
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
      finishObservedMaterializedDiagnostic table) at houtcome
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨table, _htable, hfixed⟩ := houtcome
  exact hasExistingHiddenHit_of_mem_diagnosticFromTable_successfulDoomed adversary parameter
    ftsSecret q table hq outcome hfixed hsuccess

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_sum_successfulFirstOrdinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ∑ ordinal : Fin (2 * q),
        (Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenRootHitAt ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
          Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenNonRootHitAt ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)]) := by
  classical
  let run := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => ∃ ordinal ∈ (Finset.univ : Finset (Fin (2 * q))),
          (outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
            (outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenNonRootHitAt ordinal.val) | run] := by
      apply probEvent_mono
      intro outcome houtcome hsuccess
      have hhit := hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed adversary
        parameter ftsSecret q hq outcome houtcome hsuccess
      rcases outcome.firstExistingHidden_root_or_nonRoot hhit with hroot | hnonRoot
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩ := hroot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hrootAt : outcome.FirstExistingHiddenRootHitAt ordinal :=
          outcome.firstExistingHiddenRootHitAt_of_ordinal
            ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inl ⟨hsuccess, hrootAt⟩⟩
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩ :=
          hnonRoot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hnonRootAt : outcome.FirstExistingHiddenNonRootHitAt ordinal :=
          outcome.firstExistingHiddenNonRootHitAt_of_ordinal
            ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inr ⟨hsuccess, hnonRootAt⟩⟩
    _ ≤ ∑ ordinal : Fin (2 * q),
          Pr[fun outcome =>
            (outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
              (outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenNonRootHitAt ordinal.val) | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun (ordinal : Fin (2 * q)) outcome =>
        (outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
          (outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenNonRootHitAt ordinal.val)
    _ ≤ ∑ ordinal : Fin (2 * q),
          (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenRootHitAt ordinal.val | run] +
            Pr[fun outcome => outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenNonRootHitAt ordinal.val | run]) := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      exact probEvent_or_le _ _ _
    _ = _ := by simp only [run]

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
