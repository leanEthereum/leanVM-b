import SphincsSecurity.Proof.OtsProbeNativeRiskAccumulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def probeFailureInputAllowance (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    LazyRevealProbe.Query Coordinate → ENNReal
  | .probe coordinate digest => candidateFailureAllowance table context (some ⟨coordinate, digest⟩)
  | _ => 0

theorem runResolvedFromTable_probe_positive
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (digest : Digest) :
    runResolvedFromTable context (fuel + 1) table
      (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe coordinate digest))) =
      pure (some ⟨afterCandidateContext context (some ⟨coordinate, digest⟩), fuel, (), table⟩) := by
  simp only [runResolvedFromTable, construct_query, afterCandidateContext]
  split_ifs <;> rfl

theorem probEvent_resolved_query_finish_le_allowance
    (input : LazyRevealProbe.Query Coordinate) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hfuel : 0 < fuel) (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    Pr[fun verdict => verdict = true | runResolvedFromTable context fuel table (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input)) >>=
      finishResolvedRunIsNone] ≤ resolvedContextFailureRisk table context + probeFailureInputAllowance table context input := by
  by_cases hprobe : LazyRevealProbe.IsProbe input
  · cases input <;> simp only [LazyRevealProbe.IsProbe] at hprobe
    case probe coordinate digest =>
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hfuel)
      rw [runResolvedFromTable_probe_positive, pure_bind,
        finishResolvedRunIsNone_metadata_eq _ table remaining 0 () ()]
      exact resolvedContextFailureRisk_afterCandidate_le table context (some ⟨coordinate, digest⟩) hconsistent hstarts hcard
  · have hfree : (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input) : OracleComp (LazyRevealProbe.World Coordinate) _).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
      simpa using hprobe
    have hd := evalDist_runResolvedFinishIsNone_probeFree_of_core (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input)) context fuel table () hfree hconsistent hstarts (by omega)
    have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd (p := fun verdict => verdict = true)
    have hzero : probeFailureInputAllowance table context input = 0 := by
      cases input <;> simp_all [probeFailureInputAllowance, LazyRevealProbe.IsProbe]
    rw [hzero, add_zero]
    rw [finishResolvedRunIsNone_metadata_eq context table fuel 0 () ()] at hp
    exact le_of_eq hp

theorem pending_add_remaining_le_of_mem_resolved_query
    (input : LazyRevealProbe.Query Coordinate) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult ((LazyRevealProbe.World Coordinate).Range input))
    (hentry : some entry ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) input)))) :
    entry.context.state.pending.card + entry.remaining ≤ context.state.pending.card + fuel := by
  cases input with
  | uniform n =>
      simp only [runResolvedFromTable, construct_query, mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq] at hentry
      obtain ⟨output, _, rfl⟩ := hentry
      exact le_rfl
  | hashOutput =>
      simp only [runResolvedFromTable, construct_query, mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq] at hentry
      obtain ⟨output, _, rfl⟩ := hentry
      exact le_rfl
  | ensure coordinate =>
      simp only [runResolvedFromTable, construct_query, mem_support_pure_iff, Option.some.injEq] at hentry
      cases hentry
      exact le_rfl
  | publish coordinate =>
      simp only [runResolvedFromTable, construct_query, mem_support_pure_iff, Option.some.injEq] at hentry
      cases hentry
      exact le_rfl
  | peek coordinate =>
      simp only [runResolvedFromTable, construct_query, mem_support_pure_iff, Option.some.injEq] at hentry
      cases hentry
      exact le_rfl
  | probe coordinate digest =>
      cases fuel with
      | zero => simp [runResolvedFromTable] at hentry
      | succ remaining =>
          rw [runResolvedFromTable_probe_positive] at hentry
          simp only [mem_support_pure_iff, Option.some.injEq] at hentry
          cases hentry
          unfold afterCandidateContext
          dsimp only
          split_ifs
          · omega
          · have hcard := context.state.pending_card_addPending_le coordinate digest
            dsimp only
            omega
  | reveal coordinate =>
      cases coordinate <;>
        simp only [runResolvedFromTable, construct_query, mem_support_bind_iff] at hentry
      all_goals
        obtain ⟨result, _, hentry⟩ := hentry
        cases result with
        | none => simp at hentry
        | some result =>
            simp only [mem_support_pure_iff, Option.some.injEq] at hentry
            cases hentry
            apply Nat.add_le_add_right
            exact Finset.card_le_card (Finset.filter_subset _ _)

end SphincsSecurity.Concrete.OtsProbeSimulation
