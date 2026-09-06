import SphincsSecurity.Proof.OtsProbeSourceAllowanceComponents
import SphincsSecurity.Proof.OtsProbeSourceCandidateRisk
import SphincsSecurity.Proof.OtsProbeNativeLiveAllowanceReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initializedSourceDirectRisk_eq_allowances
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel q : Nat) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    initializedSourceDirectRisk targets computation fuel q =
      ∑' table, Pr[= table | sampleOtsHashTable] *
        (liveStartProbeAllowance computation (ensuredInitialContext targets) fuel table +
          ∑ target ∈ targets, privateLiveProbeAllowance target computation (ensuredInitialContext targets) fuel table) := by
  have hlive := fun table => liveResolvedQueryBound_of_syntactic LazyRevealProbe.IsProbe computation q hbound
    (ensuredInitialContext targets) fuel table
  unfold initializedSourceDirectRisk
  rw [sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance_of_liveBound targets computation fuel q hlive]
  simp_rw [sum_privateHits_ensuredInitial_eq_liveAllowance_of_liveBound targets computation fuel q _ (hlive _)]
  simp only [mul_add, ENNReal.tsum_add]

theorem sourceMissingAllowances_le_directRisk
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel q : Nat) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      (liveStartProbeAllowance computation (ensuredInitialContext targets) fuel table +
        ∑ target ∈ targets, privateLiveMissingProbeAllowance target computation (ensuredInitialContext targets) fuel table)) ≤
      initializedSourceDirectRisk targets computation fuel q := by
  rw [initializedSourceDirectRisk_eq_allowances targets computation fuel q hbound]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  apply add_le_add le_rfl
  exact Finset.sum_le_sum fun target _ => privateLiveMissingProbeAllowance_le_stoppedAllowance target computation
    (ensuredInitialContext targets) fuel table

theorem probEvent_source_ensured_finish_le_probeAllowance
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q)
    (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    Pr[fun verdict => verdict = true |
      runResolvedFromTable (ensuredInitialContext targets) fuel table computation >>= finishResolvedRunIsNone] ≤
      liveProbeFailureAllowance computation (ensuredInitialContext targets) fuel table := by
  have hvalid := ensuredInitialContext_valid targets
  have hstarts := startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)
  have h := probEvent_source_finish_le_initial_add_probeAllowance computation q (ensuredInitialContext targets) fuel table
    hbound hvalid.valuesConsistent hstarts hbudget (by simpa [ensuredInitialContext, LazyRevealProbe.State.empty] using hspace)
  rw [resolvedContextFailureRisk_of_no_pending table (ensuredInitialContext targets) hvalid hstarts
    (show PendingCoveredBy [] (ensuredInitialContext targets) from pendingCoveredBy_empty), zero_add] at h
  exact h

noncomputable def initializedSourceMaterializedRisk
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel : Nat) : ENNReal :=
  ∑' table, Pr[= table | sampleOtsHashTable] *
    liveMaterializedProbeAllowance computation (ensuredInitialContext Finset.univ) fuel table

theorem probEvent_sampled_source_finish_le_direct_add_materialized
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q)
    (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[fun result => result = none |
        runResolvedFromTable (ensuredInitialContext ∅) fuel table computation >>= finishResolvedRun]) ≤
      initializedSourceDirectRisk Finset.univ computation fuel q + initializedSourceMaterializedRisk computation fuel := by
  have htable (table : OtsSecretIndex → HashOutput) :
      Pr[fun result => result = none |
        runResolvedFromTable (ensuredInitialContext ∅) fuel table computation >>= finishResolvedRun] ≤
        liveProbeFailureAllowance computation (ensuredInitialContext Finset.univ) fuel table := by
    have hdist := evalDist_runResolved_finish_enlargeEnsured computation (ensuredInitialContext ∅) fuel table
      (Finset.univ.image Coordinate.position) (ensuredInitialContext_valid ∅).valuesConsistent
      (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))
    rw [← ensuredInitialContext_eq_enlarge_empty] at hdist
    have heq := probEvent_congr' (fun _ _ => Iff.rfl) hdist (p := fun verdict => verdict = true)
    have h := probEvent_source_ensured_finish_le_probeAllowance Finset.univ computation q fuel table hbound hbudget hspace
    rw [heq] at h
    simpa only [finishResolvedRunIsNone, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
      Option.isNone_iff_eq_none] using h
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        liveProbeFailureAllowance computation (ensuredInitialContext Finset.univ) fuel table :=
      ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl (htable table)
    _ = (∑' table, Pr[= table | sampleOtsHashTable] *
        (liveStartProbeAllowance computation (ensuredInitialContext Finset.univ) fuel table +
          ∑ target : Position, privateLiveMissingProbeAllowance target computation (ensuredInitialContext Finset.univ) fuel table)) +
        initializedSourceMaterializedRisk computation fuel := by
      simp only [liveProbeFailureAllowance_eq_components, mul_add, ENNReal.tsum_add, initializedSourceMaterializedRisk]
    _ ≤ _ := add_le_add (sourceMissingAllowances_le_directRisk Finset.univ computation fuel q hbound) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
