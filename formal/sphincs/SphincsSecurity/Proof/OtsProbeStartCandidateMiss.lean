import SphincsSecurity.Proof.OtsProbeStartHistoryRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem afterCandidateContext_valuesConsistent (context : DeferredContext) (candidate : Option Probe)
    (hconsistent : context.ValuesConsistent) : (afterCandidateContext context candidate).ValuesConsistent := by
  cases candidate with
  | none => exact hconsistent
  | some candidate =>
      unfold afterCandidateContext
      dsimp only
      split_ifs
      · exact hconsistent
      · exact hconsistent.addPending candidate.coordinate candidate.candidate

theorem afterCandidateContext_startTableAgrees (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (candidate : Option Probe) (hstarts : StartTableAgrees context.state table) :
    StartTableAgrees (afterCandidateContext context candidate).state table := by
  cases candidate with
  | none => exact hstarts
  | some candidate =>
      unfold afterCandidateContext
      dsimp only
      split_ifs
      · exact hstarts
      · exact hstarts.addPending candidate.coordinate candidate.candidate

theorem deferredCompletable_afterCandidate_of_mem_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context (fuel + 1) table
      ((probingHashQuery parameter input).run cache)))
    (hcomplete : DeferredCompletable table result.context) :
    DeferredCompletable table
      (afterCandidateContext context (purePlanProbingHashQuery parameter input context.state).candidate?) := by
  rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
  unfold probingHashQueryAfterPlan executePlannedHashQuery at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_executeCandidate_positive, pure_bind] at hresult
  exact deferredCompletable_of_mem_runResolvedFromTable _ _ _ table result
    (afterCandidateContext_valuesConsistent context _ hconsistent)
    (afterCandidateContext_startTableAgrees table context _ hstarts) hresult hcomplete

theorem deferredCompletable_afterCandidate_of_mem_canonicalHashQuery
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
      (.inl (.inr input)) context (fuel + 1) table cache))
    (hcomplete : DeferredCompletable result.table result.context) :
    DeferredCompletable table
      (afterCandidateContext context (purePlanProbingHashQuery parameter input context.state).candidate?) := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some raw =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff, Option.some.injEq] at hcanonical
      subst result
      change some raw ∈ support (runResolvedFromTable context (fuel + 1) table
        ((probingHashQuery parameter input).run cache)) at hraw
      have hcore := resolvedCore_of_mem_runResolvedFromTable ((probingHashQuery parameter input).run cache)
        context (fuel + 1) table raw hconsistent hstarts hraw
      change DeferredCompletable raw.table (canonicalizeMaterializedValues table raw.context) at hcomplete
      rw [hcore.1] at hcomplete
      obtain ⟨completion, hcompletion⟩ := hcomplete
      exact deferredCompletable_afterCandidate_of_mem_probingHashQuery parameter input context fuel table cache raw
        hconsistent hstarts hraw ⟨completion, hcompletion.of_canonicalizeMaterializedValues hcore.2.1 hcore.2.2⟩

theorem canonicalHashQuery_complete_candidate_misses_chainStart
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
      (.inl (.inr input)) context (fuel + 1) table cache))
    (hcomplete : DeferredCompletable result.table result.context)
    (index : OtsSecretIndex) (digest : Digest)
    (hcandidate : (purePlanProbingHashQuery parameter input context.state).candidate? = some ⟨index.coordinate, digest⟩)
    (hhidden : index.coordinate ∉ context.state.revealed) : truncateHash (table index) ≠ digest := by
  have hafter := deferredCompletable_afterCandidate_of_mem_canonicalHashQuery parameter root table ftsSecret input
    context fuel cache result hconsistent hstarts hresult hcomplete
  rw [hcandidate, afterCandidateContext, if_neg hhidden] at hafter
  intro hhit
  apply hafter.not_pendingResolvedHit
  refine ⟨index.coordinate, table index, ?_, ?_⟩
  · cases index
    rfl
  · unfold LazyRevealProbe.State.hitAt
    rw [LazyRevealProbe.State.mem_pendingAt_iff]
    simp [LazyRevealProbe.State.addPending, hhit]

end SphincsSecurity.Concrete.OtsProbeSimulation
