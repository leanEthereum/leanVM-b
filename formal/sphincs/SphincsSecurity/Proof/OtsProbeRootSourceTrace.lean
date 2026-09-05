import SphincsSecurity.Proof.OtsProbeNativeRootSource
import SphincsSecurity.Proof.OtsProbeQueryTraceReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def PrehitQuerySnapshot.EncodingSourceSettledTo (accountingKey : SecretKey)
    (before after : PrehitQuerySnapshot) : Prop :=
  ∀ (input : HashInput) (candidate : Probe) (target : Position),
    before.input = .inl (.inr input) →
    EncodingLayerRootCandidateAt accountingKey.parameter input candidate →
    candidate.coordinate = .position target → after.state.2 = false →
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret after.state.1.cache target →
    candidate.candidate = honestValue (fromCache after.state.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target →
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret before.state.1.cache target

set_option maxRecDepth 100000 in
theorem prehitQueryTrace_pairwise_encodingSourceSettled
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state)) :
    result.2.Pairwise (PrehitQuerySnapshot.EncodingSourceSettledTo accountingKey) := by
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
      exact hcandidate.settled_of_prehitFree_viewed_matching_query secretKey hposition hsettled hmatch
        (fun answer => outerQueryCutAt (next answer) ordinal) cut hprefixFalse

def UnsettledSourceEncodingRootMatch (accountingKey : SecretKey) (history : List PrehitQuerySnapshot) : Prop :=
  ∃ (i j : Fin history.length), i.val < j.val ∧
    ∃ (input : HashInput) (candidate : Probe) (target : Position),
      (history.get i).input = .inl (.inr input) ∧
      EncodingLayerRootCandidateAt accountingKey.parameter input candidate ∧
      candidate.coordinate = .position target ∧
      Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (history.get j).state.1.cache target ∧
      candidate.candidate = honestValue (fromCache (history.get j).state.1.cache)
        accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target ∧
      ¬Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (history.get i).state.1.cache target

theorem prehitQueryTrace_hit_of_unsettledSourceEncodingRootMatch
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hmatch : UnsettledSourceEncodingRootMatch accountingKey result.2) : result.1.2.2 = true := by
  by_cases hhit : result.1.2.2 = true
  · exact hhit
  have hfalse := Bool.eq_false_iff.mpr hhit
  obtain ⟨i, j, hij, input, candidate, target, hinput, hcandidate, hposition, hsettled, hmatch, hreserve⟩ := hmatch
  have hpairs := prehitQueryTrace_pairwise_encodingSourceSettled accountingKey secretKey computation state result hrun
  have hpair := hpairs.rel_get_of_lt hij
  have hentryFalse := prehitQueryTrace_entry_false_of_final_false accountingKey secretKey computation state result
    hrun hfalse (result.2.get j) (List.get_mem _ _)
  exact False.elim (hreserve
    (hpair input candidate target hinput hcandidate hposition hentryFalse hsettled hmatch))

theorem probEvent_unsettledSourceEncodingRootMatch_le_prehit
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Pr[fun result => UnsettledSourceEncodingRootMatch accountingKey result.2 |
      runPrehitQueryTrace accountingKey secretKey computation state] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state] := by
  rw [← runPrehitQueryTrace_projection, probEvent_map]
  exact probEvent_mono fun result hresult hmatch =>
    prehitQueryTrace_hit_of_unsettledSourceEncodingRootMatch accountingKey secretKey computation state result hresult hmatch

set_option maxRecDepth 100000 in
theorem prehitQueryTrace_encodingSourceSettled_at_final
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (entry : PrehitQuerySnapshot) (hentry : entry ∈ result.2)
    (input : HashInput) (candidate : Probe) (target : Position)
    (hinput : entry.input = .inl (.inr input))
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target) (hfinal : result.1.2.2 = false)
    (hsettled : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret result.1.2.1.cache target)
    (hmatch : candidate.candidate = honestValue (fromCache result.1.2.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target) :
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret entry.state.1.cache target := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [runPrehitQueryTrace, OracleComp.construct_pure, mem_support_pure_iff] at hrun
      subst result
      simp at hentry
  | query_bind query next ih =>
      have hproject := mem_support_prehitRun_of_trace accountingKey secretKey _ state result hrun
      rw [runPrehitQueryTrace_query_bind, mem_support_bind_iff] at hrun
      obtain ⟨step, hstep, hrun⟩ := hrun
      rw [mem_support_bind_iff] at hrun
      obtain ⟨tail, htail, hresult⟩ := hrun
      simp only [mem_support_pure_iff] at hresult
      subst result
      rcases List.mem_cons.mp hentry with heq | htailEntry
      · subst entry
        change query = .inl (.inr input) at hinput
        subst query
        have hrunFalse : (tail.1.1, (tail.1.2.1, false)) ∈ support
            ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
              ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (state.1, state.2)) := by
          dsimp only at hfinal
          simpa only [← hfinal] using hproject
        have hinitial := encodingPrehitViewedAdversaryImpl_initial_false_of_mem_support accountingKey secretKey
          ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)
          state.1 tail.1.2.1 state.2 tail.1.1 hrunFalse
        rw [hinitial] at hrunFalse
        exact hcandidate.settled_of_prehitFree_viewed_matching_query secretKey hposition hsettled hmatch
          next tail.1.1 hrunFalse
      · exact ih step.1 step.2 tail htail htailEntry hfinal hsettled hmatch

def UnsettledSourceFinalEncodingRootMatch (accountingKey : SecretKey)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  ∃ entry ∈ result.2, ∃ (input : HashInput) (candidate : Probe) (target : Position),
    entry.input = .inl (.inr input) ∧
    EncodingLayerRootCandidateAt accountingKey.parameter input candidate ∧
    candidate.coordinate = .position target ∧
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret result.1.2.1.cache target ∧
    candidate.candidate = honestValue (fromCache result.1.2.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target ∧
    ¬Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret entry.state.1.cache target

theorem prehitQueryTrace_hit_of_unsettledSourceFinalEncodingRootMatch
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hmatch : UnsettledSourceFinalEncodingRootMatch accountingKey result) : result.1.2.2 = true := by
  by_cases hhit : result.1.2.2 = true
  · exact hhit
  obtain ⟨entry, hentry, input, candidate, target, hinput, hcandidate, hposition, hsettled, hmatch, hreserve⟩ := hmatch
  exact False.elim (hreserve (prehitQueryTrace_encodingSourceSettled_at_final accountingKey secretKey
    computation state result hrun entry hentry input candidate target hinput hcandidate hposition
    (Bool.eq_false_iff.mpr hhit) hsettled hmatch))

theorem probEvent_unsettledSourceTraceRootMatch_le_prehit
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Pr[fun result => UnsettledSourceEncodingRootMatch accountingKey result.2 ∨ UnsettledSourceFinalEncodingRootMatch accountingKey result |
      runPrehitQueryTrace accountingKey secretKey computation state] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state] := by
  rw [← runPrehitQueryTrace_projection, probEvent_map]
  apply probEvent_mono
  intro result hresult hmatch
  rcases hmatch with hpairs | hfinal
  · exact prehitQueryTrace_hit_of_unsettledSourceEncodingRootMatch accountingKey secretKey computation state result hresult hpairs
  · exact prehitQueryTrace_hit_of_unsettledSourceFinalEncodingRootMatch accountingKey secretKey computation state result hresult hfinal

end SphincsSecurity.Concrete.OtsProbeSimulation
