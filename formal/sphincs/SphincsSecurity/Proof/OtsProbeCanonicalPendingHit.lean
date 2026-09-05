import SphincsSecurity.Proof.OtsProbeCanonicalPending

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

def PendingResolvedHit (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : Prop :=
  ∃ coordinate output, resolvedCompletionValue table context coordinate = some output ∧
    context.state.hitAt coordinate output

theorem DeferredCompletable.not_pendingResolvedHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) : ¬PendingResolvedHit table context := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  rintro ⟨coordinate, output, hvalue, hhit⟩
  have heq := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hpending : (coordinate, truncateHash output) ∈ context.state.pending := by
    rwa [← LazyRevealProbe.State.mem_pendingAt_iff]
  exact hcompletion.2.2.1 coordinate (truncateHash output) hpending (by rw [heq])

theorem deferredCompletable_iff_no_pendingResolvedHit
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    DeferredCompletable table context ↔ ¬PendingResolvedHit table context := by
  constructor
  · exact DeferredCompletable.not_pendingResolvedHit
  · intro hclean
    have hvalid : context.Valid := by
      refine ⟨hconsistent, ?_⟩
      intro coordinate output hvalue hhit
      apply hclean
      refine ⟨coordinate, output, ?_, hhit⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
          simp [resolvedCompletionValue, heq]
      | position position => simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
    apply deferredCompletable_of_valid_of_no_boundary_hit table context hvalid hstarts
      (hcard := hcard)
    · rintro ⟨position, output, hhidden, hvalue, hhit⟩
      exact hclean ⟨.position position, output,
        by simp [resolvedCompletionValue, DeferredContext.positionValue, hhidden, hvalue], hhit⟩
    · rintro ⟨index, _hhidden, hhit⟩
      exact hclean ⟨index.coordinate, table index, rfl, hhit⟩

theorem PendingCoveredBy.resolved_hit_candidate
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext} {candidates : List Probe}
    (hcovered : PendingCoveredBy candidates context) (hhit : PendingResolvedHit table context) :
    ∃ candidate ∈ candidates, ∃ output,
      resolvedCompletionValue table context candidate.coordinate = some output ∧
      truncateHash output = candidate.candidate := by
  obtain ⟨coordinate, output, hvalue, hhit⟩ := hhit
  have hpending : (coordinate, truncateHash output) ∈ context.state.pending := by
    rwa [← LazyRevealProbe.State.mem_pendingAt_iff]
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered _ hpending
  exact ⟨candidate, hcandidate, output, hcoordinate ▸ hvalue, hdigest.symm⟩

theorem canonicalQuery_completable_iff_no_pendingResolvedHit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) (prior : List Probe)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCoveredBy prior context)
    (hcard : prior.length + outerHashQueryCount input < Fintype.card Digest)
    (hrun : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)) :
    DeferredCompletable result.table result.context ↔ ¬PendingResolvedHit table result.context := by
  have hnextCovered := pendingCoveredBy_of_mem_canonicalChronologicalQuery
    parameter root ftsSecret input context fuel table cache prior result hcovered hrun
  have hnextCard : result.context.state.pending.card < Fintype.card Digest := by
    have hcandidates := canonicalQueryCandidates_length_le_hashCount parameter input context
    have hbound := hnextCovered.card_le
    simp only [List.length_append] at hbound
    omega
  have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl
    parameter root table ftsSecret input context fuel cache result hconsistent hstarts hrun
  rw [hcore.1]
  exact deferredCompletable_iff_no_pendingResolvedHit table result.context hcore.2.1 hcore.2.2 hnextCard

theorem resolved_hit_candidate_of_canonicalQuery_not_completable
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) (prior : List Probe)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCoveredBy prior context)
    (hcard : prior.length + outerHashQueryCount input < Fintype.card Digest)
    (hrun : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache))
    (hstop : ¬DeferredCompletable table result.context) :
    ∃ candidate ∈ prior ++ canonicalQueryCandidates parameter input context, ∃ output,
      resolvedCompletionValue table result.context candidate.coordinate = some output ∧
      truncateHash output = candidate.candidate := by
  have hnextCovered := pendingCoveredBy_of_mem_canonicalChronologicalQuery
    parameter root ftsSecret input context fuel table cache prior result hcovered hrun
  have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl
    parameter root table ftsSecret input context fuel cache result hconsistent hstarts hrun
  apply hnextCovered.resolved_hit_candidate
  have hiff := canonicalQuery_completable_iff_no_pendingResolvedHit parameter root table ftsSecret
    input context fuel cache prior result hconsistent hstarts hcovered hcard hrun
  rw [hcore.1] at hiff
  exact Classical.not_not.mp fun hclean => hstop (hiff.mpr hclean)

def ReturnedPendingResolvedHit (table : OtsSecretIndex → HashOutput)
    (result : Option (ResolvedRunResult α)) : Prop :=
  match result with
  | none => False
  | some result => PendingResolvedHit table result.context

theorem probEvent_canonicalQuery_rejected_eq_none_add_pendingHit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) (prior : List Probe)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCoveredBy prior context)
    (hcard : prior.length + outerHashQueryCount input < Fintype.card Digest) :
    let queryRun := canonicalChronologicalAdversaryImpl parameter root table ftsSecret
      input context fuel table cache
    Pr[ResolvedQueryRejected | queryRun] = Pr[fun result => result = none | queryRun] +
      Pr[ReturnedPendingResolvedHit table | queryRun] := by
  classical
  dsimp only
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro option
  by_cases hsupported : option ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)
  · cases option with
    | none => simp [ResolvedQueryRejected, ReturnedPendingResolvedHit]
    | some result =>
        have hiff := canonicalQuery_completable_iff_no_pendingResolvedHit parameter root table ftsSecret
          input context fuel cache prior result hconsistent hstarts hcovered hcard hsupported
        simp [ResolvedQueryRejected, ReturnedPendingResolvedHit, hiff]
  · have hzero := probOutput_eq_zero_of_not_mem_support hsupported
    simp [hzero]

set_option maxHeartbeats 800000 in
theorem canonicalQuery_not_completable_has_query_source
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hleft : left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (ordinal : Nat) (entry : CanonicalQuerySelection) (hentry : left.2[ordinal]? = some entry)
    (root : Digest)
    (result : ResolvedRunResult ((OracleWorld + SigningSpec).Range entry.input × SplitHashCache))
    (hrun : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        entry.input entry.context entry.fuel table entry.cache))
    (hstop : ¬DeferredCompletable table result.context) :
    ∃ earlier ≤ ordinal, ∃ source candidate output,
      left.2[earlier]? = some source ∧
      candidate ∈ canonicalQueryCandidates parameter source.input source.context ∧
      resolvedCompletionValue table result.context candidate.coordinate = some output ∧
      truncateHash output = candidate.candidate := by
  obtain ⟨hindex, hvalue⟩ := List.getElem?_eq_some_iff.mp hentry
  have hselected := hrelation.selection_at ⟨ordinal, hindex⟩
  simp only [List.get_eq_getElem, hvalue] at hselected
  have hinvariant := hselected.2.2.1
  have hcovered := pendingCoveredBy_of_mem_canonicalRetainedQueryTrace
    adversary parameter table ftsSecret fuel left hleft ordinal entry hentry
  have hbudget := (canonicalTraceCandidates_length_le_hashCount parameter (left.2.take ordinal)).trans
    ((canonicalTraceHashCount_take_le _ _).trans (hrelation.hashCount_le.trans
      (prehitRetainedTraceHashCount_le adversary q hq parameter hparameter table ftsSecret hfts right hright)))
  have hcount : outerHashQueryCount entry.input ≤ 1 := by
    cases entry.input with
    | inl query => cases query <;> simp [outerHashQueryCount]
    | inr message => exact Nat.zero_le 1
  have hcard : (canonicalTraceCandidates parameter (left.2.take ordinal)).length +
      outerHashQueryCount entry.input < Fintype.card Digest := by
    have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  obtain ⟨candidate, hcandidate, output, houtput, hdigest⟩ :=
    resolved_hit_candidate_of_canonicalQuery_not_completable parameter root table ftsSecret
      entry.input entry.context entry.fuel entry.cache _ result
      hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hcovered hcard hrun hstop
  rcases List.mem_append.mp hcandidate with hprior | hcurrent
  · obtain ⟨earlier, hlt, source, hsource, hcandidate⟩ :=
      candidate_source_of_mem_canonicalTraceCandidates_take parameter left.2 ordinal candidate hprior
    exact ⟨earlier, hlt.le, source, candidate, output, hsource, hcandidate, houtput, hdigest⟩
  · exact ⟨ordinal, le_rfl, entry, candidate, output, hentry, hcurrent, houtput, hdigest⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
