import SphincsSecurity.Proof.OtsProbePrehitQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def PrehitQuerySnapshot.EncodingReserveTo (accountingKey : SecretKey)
    (before after : PrehitQuerySnapshot) : Prop :=
  ∀ (input : HashInput) (candidate : Probe) (target : Position),
    before.input = .inl (.inr input) →
    EncodingLayerRootCandidateAt accountingKey.parameter input candidate →
    candidate.coordinate = .position target → after.state.2 = false →
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret after.state.1.cache target →
    candidate.candidate = honestValue (fromCache after.state.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target →
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey before.state.1.cache input

set_option maxRecDepth 100000 in
theorem prehitQueryTrace_pairwise_encodingReserve
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state)) :
    result.2.Pairwise (PrehitQuerySnapshot.EncodingReserveTo accountingKey) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [runPrehitQueryTrace, OracleComp.construct_pure, mem_support_pure_iff] at hrun
      subst result
      exact List.Pairwise.nil
  | query_bind query next ih =>
      rw [runPrehitQueryTrace_query_bind, mem_support_bind_iff] at hrun
      obtain ⟨step, hstep, hrun⟩ := hrun
      rw [mem_support_bind_iff] at hrun
      obtain ⟨tail, htail, hresult⟩ := hrun
      simp only [mem_support_pure_iff] at hresult
      subst result
      apply List.Pairwise.cons ?_ (ih step.1 step.2 tail htail)
      intro entry hentry input candidate target hinput hcandidate hposition hfalse hsettled hmatch
      change query = .inl (.inr input) at hinput
      subst query
      obtain ⟨ordinal, cut, _hcutInput, hcut⟩ := queryCut_support_of_mem_prehitQueryTrace
        accountingKey secretKey (next step.1) step.2 tail htail entry hentry
      let segment : OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α) :=
        (OracleWorld + SigningSpec).query (.inl (.inr input)) >>= fun answer => outerQueryCutAt (next answer) ordinal
      have hprefix : (cut, entry.state) ∈ support
          ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) segment).run state) := by
        dsimp only [segment]
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨step, hstep, hcut⟩
      have hprefixFalse : (cut, (entry.state.1, false)) ∈ support
          ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) segment).run (state.1, state.2)) := by
        simpa only [← hfalse] using hprefix
      have hinitial := encodingPrehitViewedAdversaryImpl_initial_false_of_mem_support accountingKey secretKey
        segment state.1 entry.state.1 state.2 cut hprefixFalse
      rw [hinitial] at hprefixFalse
      exact hcandidate.refinedReserve_of_prehitFree_viewed_matching_query secretKey hposition hsettled hmatch
        (fun answer => outerQueryCutAt (next answer) ordinal) cut hprefixFalse

def UnpaidEncodingRootMatch (accountingKey : SecretKey) (history : List PrehitQuerySnapshot) : Prop :=
  ∃ (i j : Fin history.length), i.val < j.val ∧
    ∃ (input : HashInput) (candidate : Probe) (target : Position),
      (history.get i).input = .inl (.inr input) ∧
      EncodingLayerRootCandidateAt accountingKey.parameter input candidate ∧
      candidate.coordinate = .position target ∧
      Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (history.get j).state.1.cache target ∧
      candidate.candidate = honestValue (fromCache (history.get j).state.1.cache)
        accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target ∧
      otsOpeningRefinedQueryReserve accountingKey (history.get i).state.1.cache input < (4 / 3 : ℝ≥0∞)

theorem prehitQueryTrace_hit_of_unpaidEncodingRootMatch
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hmatch : UnpaidEncodingRootMatch accountingKey result.2) : result.1.2.2 = true := by
  by_cases hhit : result.1.2.2 = true
  · exact hhit
  have hfalse := Bool.eq_false_iff.mpr hhit
  obtain ⟨i, j, hij, input, candidate, target, hinput, hcandidate, hposition, hsettled, hmatch, hreserve⟩ := hmatch
  have hpairs := prehitQueryTrace_pairwise_encodingReserve accountingKey secretKey computation state result hrun
  have hpair := hpairs.rel_get_of_lt hij
  have hentryFalse := prehitQueryTrace_entry_false_of_final_false accountingKey secretKey computation state result
    hrun hfalse (result.2.get j) (List.get_mem _ _)
  exact False.elim ((not_le_of_gt hreserve)
    (hpair input candidate target hinput hcandidate hposition hentryFalse hsettled hmatch))

theorem probEvent_unpaidEncodingRootMatch_le_prehit
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Pr[fun result => UnpaidEncodingRootMatch accountingKey result.2 |
      runPrehitQueryTrace accountingKey secretKey computation state] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state] := by
  rw [← runPrehitQueryTrace_projection, probEvent_map]
  exact probEvent_mono fun result hresult hmatch =>
    prehitQueryTrace_hit_of_unpaidEncodingRootMatch accountingKey secretKey computation state result hresult hmatch

end SphincsSecurity.Concrete.OtsProbeSimulation
