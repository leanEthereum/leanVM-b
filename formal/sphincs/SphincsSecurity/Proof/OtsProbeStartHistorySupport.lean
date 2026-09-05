import SphincsSecurity.Proof.OtsProbeStartCandidateMiss

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem revealed_subset_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact Finset.Subset.rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate digest =>
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runResolvedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa only [hrevealed, ↓reduceIte] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate digest } remaining
                  (by simpa only [hrevealed, ↓reduceIte] using hresult)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact (Finset.subset_insert coordinate context.state.revealed).trans
            (ih () { context with state := context.state.publish coordinate } fuel hresult)
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨option, _hresolve, htail⟩ := hresult
            cases option with
            | none => simp at htail
            | some resolved =>
                have hmono := ih resolved.output _ fuel htail
                exact hmono

theorem revealed_subset_of_mem_canonicalChronologicalQuery
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hresult : some result ∈ support (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
      input context fuel table cache)) : context.state.revealed ⊆ result.context.state.revealed := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some raw =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff, Option.some.injEq] at hcanonical
      subst result
      exact revealed_subset_of_mem_runResolvedFromTable _ context fuel table raw hraw

def UnrevealedChainStartHistoryMisses (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (history : List Probe) : Prop :=
  ∀ candidate ∈ history, candidate.coordinate ∉ state.revealed →
    ¬ChainStartEntryHit table (candidate.coordinate, candidate.candidate)

theorem UnrevealedChainStartHistoryMisses.mono_revealed
    {table : OtsSecretIndex → HashOutput} {before after : LazyRevealProbe.State Coordinate} {history : List Probe}
    (hmiss : UnrevealedChainStartHistoryMisses table before history) (hrevealed : before.revealed ⊆ after.revealed) :
    UnrevealedChainStartHistoryMisses table after history := by
  intro candidate hcandidate hhidden
  exact hmiss candidate hcandidate (fun hmem => hhidden (hrevealed hmem))

theorem unrevealedChainStartHistoryMisses_append_canonicalQuery
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (prior : List Probe)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hprior : UnrevealedChainStartHistoryMisses table context.state prior)
    (hresult : some result ∈ support (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
      input context (fuel + 1) table cache))
    (hcomplete : DeferredCompletable result.table result.context) :
    UnrevealedChainStartHistoryMisses table result.context.state
      (prior ++ canonicalQueryCandidates parameter input context) := by
  have hsubset := revealed_subset_of_mem_canonicalChronologicalQuery parameter root table ftsSecret input
    context (fuel + 1) cache result hresult
  intro candidate hcandidate hhidden
  rcases List.mem_append.mp hcandidate with hpriorCandidate | hcurrent
  · exact hprior.mono_revealed hsubset candidate hpriorCandidate hhidden
  · have hhiddenBefore : candidate.coordinate ∉ context.state.revealed := fun hmem => hhidden (hsubset hmem)
    cases input with
    | inl query =>
        cases query with
        | inl n => simp [canonicalQueryCandidates] at hcurrent
        | inr input =>
            have hplan : (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate := by
              simpa only [canonicalQueryCandidates, Option.mem_toList] using hcurrent
            rcases candidate with ⟨coordinate, digest⟩
            cases coordinate with
            | position position => simp [ChainStartEntryHit]
            | chainStart lay tree leafIdx chainIdx =>
                exact canonicalHashQuery_complete_candidate_misses_chainStart parameter root table ftsSecret input
                  context fuel cache result hconsistent hstarts hresult hcomplete
                  ⟨lay, tree, leafIdx, chainIdx⟩ digest hplan hhiddenBefore
    | inr message => simp [canonicalQueryCandidates] at hcurrent

end SphincsSecurity.Concrete.OtsProbeSimulation
