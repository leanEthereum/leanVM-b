import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateCandidateResolve

/-!
# Pending-candidate trace invariant

Probe-free resolved computations can only preserve or remove pending candidates. This is the support invariant needed to show that every private structural stop is witnessed by a candidate already present in the proof-only plan trace.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem pending_subset_of_done_runDirectResolvedDetailedFromTable_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.context.state.pending ⊆ context.state.pending := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact Finset.Subset.rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hprobeFree
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel (hprobeFree.2 output) htail
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel (hprobeFree.2 output) htail
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (hprobeFree.2 ()) hresult
      | probe coordinate candidate =>
          simp [LazyRevealProbe.IsProbe] at hprobeFree
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel
            (hprobeFree.2 _) hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            (hprobeFree.2 ()) hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some output =>
              simp only [hstate] at hresult
              exact ih output context fuel (hprobeFree.2 output) hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact (ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel (hprobeFree.2 output) hresult).trans
                        (Finset.filter_subset _ _)
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact (ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel (hprobeFree.2 output) hresult).trans
                            (Finset.filter_subset _ _)
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, htail⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at htail
                      · simp only [hhit, ↓reduceIte] at htail
                        exact (ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel (hprobeFree.2 output) htail).trans
                            (Finset.filter_subset _ _)

theorem pending_subset_of_done_runDirectResolvedDetailedFromTable_of_ProbeFree
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hprobeFree : ProbeFree computation)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table (computation.run cache))) :
    result.context.state.pending ⊆ context.state.pending :=
  pending_subset_of_done_runDirectResolvedDetailedFromTable_of_probeFree
    (computation.run cache) context fuel table result (hprobeFree cache) hresult

def PendingCoveredBy (candidates : List Probe) (context : DeferredContext) : Prop :=
  ∀ entry ∈ context.state.pending,
    ∃ candidate ∈ candidates,
      candidate.coordinate = entry.1 ∧ candidate.candidate = entry.2

theorem pendingCoveredBy_empty :
    PendingCoveredBy []
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues } := by
  intro entry hentry
  simp [LazyRevealProbe.State.empty] at hentry

theorem PendingCoveredBy.of_subset
    {candidates : List Probe} {left right : DeferredContext}
    (hcovered : PendingCoveredBy candidates right)
    (hsubset : left.state.pending ⊆ right.state.pending) :
    PendingCoveredBy candidates left := by
  intro entry hentry
  exact hcovered entry (hsubset hentry)

theorem PendingCoveredBy.mono_candidates
    {prior later : List Probe} {context : DeferredContext}
    (hcovered : PendingCoveredBy prior context) (hsublist : prior.Sublist later) :
    PendingCoveredBy later context := by
  intro entry hentry
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered entry hentry
  exact ⟨candidate, hsublist.subset hcandidate, hcoordinate, hdigest⟩

theorem PendingCoveredBy.addPending_append
    (candidates : List Probe) (context : DeferredContext) (candidate : Probe)
    (hcovered : PendingCoveredBy candidates context) :
    PendingCoveredBy (candidates ++ [candidate])
      { context with
        state := context.state.addPending candidate.coordinate candidate.candidate } := by
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with hnew | hold
  · subst entry
    exact ⟨candidate, by simp, rfl, rfl⟩
  · obtain ⟨oldCandidate, holdCandidate, hcoordinate, hdigest⟩ := hcovered entry hold
    exact ⟨oldCandidate, by simp [holdCandidate], hcoordinate, hdigest⟩

theorem candidateListHits_of_mem
    (target : Position) (output : HashOutput) (candidate : Probe)
    (candidates : List Probe) (hmem : candidate ∈ candidates)
    (hcoordinate : candidate.coordinate = .position target)
    (hdigest : candidate.candidate = truncateHash output) :
    candidateListHits target candidates output := by
  induction candidates with
  | nil => simp at hmem
  | cons head remaining ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl ⟨hcoordinate, hdigest.symm⟩
      · exact Or.inr (ih hmem)

def RecordedCandidateHit (context : DeferredContext) (candidates : List Probe) : Prop :=
  ∃ position output,
    context.values position = some output ∧
      candidateListHits position candidates output

theorem recordedCandidateHit_of_privateStructuralHit
    (context : DeferredContext) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (hhit : PrivateStructuralHit context) :
    RecordedCandidateHit context candidates := by
  obtain ⟨position, output, _hhidden, hprivate, hhit⟩ := hhit
  have hpending :
      (Coordinate.position position, truncateHash output) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ :=
    hcovered (Coordinate.position position, truncateHash output) hpending
  exact ⟨position, output, hprivate,
    candidateListHits_of_mem position output candidate candidates hcandidate hcoordinate
      hdigest⟩

def PrivateValuesLE (left right : DeferredContext) : Prop :=
  ∀ position output, left.values position = some output →
    right.values position = some output

theorem PrivateValuesLE.refl (context : DeferredContext) :
    PrivateValuesLE context context := by
  intro position output hvalue
  exact hvalue

theorem PrivateValuesLE.trans {first second third : DeferredContext}
    (hfirst : PrivateValuesLE first second) (hsecond : PrivateValuesLE second third) :
    PrivateValuesLE first third := by
  intro position output hvalue
  exact hsecond position output (hfirst position output hvalue)

set_option maxRecDepth 100000 in
theorem privateValuesLE_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    PrivateValuesLE context result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact PrivateValuesLE.refl context
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, htail⟩ := hresult
          exact ih value context fuel htail
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨value, _hvalue, htail⟩ := hresult
          exact ih value context fuel htail
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining hresult
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some value =>
              simp only [hstate] at hresult
              exact ih value context fuel hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let value := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) value
                  · simp [value, hhit] at hresult
                  · simp only [value, hhit, ↓reduceIte] at hresult
                    exact ih value
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) value
                        values := context.values }
                      fuel hresult
              | position revealed =>
                  cases hprivate : context.values revealed with
                  | some value =>
                      by_cases hhit : context.state.hitAt (.position revealed) value
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih value
                          { state := context.state.materialize (.position revealed) value
                            values := context.values }
                          fuel hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨value, _hvalue, htail⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position revealed) value
                      · simp [hhit] at htail
                      · simp only [hhit, ↓reduceIte] at htail
                        have hnext := ih value
                          { state := context.state.materialize (.position revealed) value
                            values := context.values.install revealed value }
                          fuel htail
                        intro position output hvalue
                        apply hnext position output
                        have hne : position ≠ revealed := by
                          intro heq
                          subst position
                          rw [hprivate] at hvalue
                          contradiction
                        simpa [DeferredStructuralValues.install, Function.update_of_ne hne] using
                          hvalue

end SphincsSecurity.Concrete.OtsProbeSimulation
