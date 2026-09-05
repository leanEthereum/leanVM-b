import SphincsSecurity.Proof.OtsProbePrehitTracePairs

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem prehitQueryTrace_encodingReserve_at_final
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
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey entry.state.1.cache input := by
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
        exact hcandidate.refinedReserve_of_prehitFree_viewed_matching_query secretKey hposition hsettled hmatch
          next tail.1.1 hrunFalse
      · exact ih step.1 step.2 tail htail htailEntry hfinal hsettled hmatch

def UnpaidFinalEncodingRootMatch (accountingKey : SecretKey)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  ∃ entry ∈ result.2, ∃ (input : HashInput) (candidate : Probe) (target : Position),
    entry.input = .inl (.inr input) ∧
    EncodingLayerRootCandidateAt accountingKey.parameter input candidate ∧
    candidate.coordinate = .position target ∧
    Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret result.1.2.1.cache target ∧
    candidate.candidate = honestValue (fromCache result.1.2.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret target ∧
    otsOpeningRefinedQueryReserve accountingKey entry.state.1.cache input < (4 / 3 : ℝ≥0∞)

theorem prehitQueryTrace_hit_of_unpaidFinalEncodingRootMatch
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hmatch : UnpaidFinalEncodingRootMatch accountingKey result) : result.1.2.2 = true := by
  by_cases hhit : result.1.2.2 = true
  · exact hhit
  obtain ⟨entry, hentry, input, candidate, target, hinput, hcandidate, hposition, hsettled, hmatch, hreserve⟩ := hmatch
  exact False.elim ((not_le_of_gt hreserve) (prehitQueryTrace_encodingReserve_at_final accountingKey secretKey
    computation state result hrun entry hentry input candidate target hinput hcandidate hposition
    (Bool.eq_false_iff.mpr hhit) hsettled hmatch))

theorem probEvent_unpaidTraceRootMatch_le_prehit
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Pr[fun result => UnpaidEncodingRootMatch accountingKey result.2 ∨ UnpaidFinalEncodingRootMatch accountingKey result |
      runPrehitQueryTrace accountingKey secretKey computation state] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state] := by
  rw [← runPrehitQueryTrace_projection, probEvent_map]
  apply probEvent_mono
  intro result hresult hmatch
  rcases hmatch with hpairs | hfinal
  · exact prehitQueryTrace_hit_of_unpaidEncodingRootMatch accountingKey secretKey computation state result hresult hpairs
  · exact prehitQueryTrace_hit_of_unpaidFinalEncodingRootMatch accountingKey secretKey computation state result hresult hfinal

end SphincsSecurity.Concrete.OtsProbeSimulation
