import SphincsSecurity.Proof.OriginalRecordBudgetPotential
import SphincsSecurity.Proof.CertificateCacheExceptionPotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_originalLength_cacheException_le {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (hit : μ → Bool)
    (hupdate : ∀ input state length record, hit (update input state length record) =
      (hit state.2 || decide (CertificateCacheExceptional key state.1) ||
        decide (CertificateCacheExceptional key record.cache)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : QueryCache HashSpec × μ) (hfinite : Finite state.1) :
    Pr[fun result => hit result.2.2 = true |
      (simulateQ (originalLengthImpl key spent enabled update) computation).run state] ≤
        if hit state.2 then 1 else certificateCacheExceptionPotential key q state.1 := by
  induction computation using OracleComp.inductionOn generalizing q state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
      cases hit state.2 <;> simp
  | query_bind input next ih =>
      by_cases hhit : hit state.2 = true
      · simp only [hhit, if_true]
        exact probEvent_le_one
      have hfalse : hit state.2 = false := Bool.eq_false_iff.mpr hhit
      by_cases hbad : CertificateCacheExceptional key state.1
      · simp only [hhit]
        exact probEvent_le_one.trans (certificateCacheExceptionPotential_bad key q state.1 hfinite hbad)
      have hquery : (expandedAdversaryImpl key input).IsQueryBoundP (· matches .inr _) q := by
        rw [simulateQ_bind, simulateQ_spec_query] at hbound
        exact IsQueryBoundP.of_bind_left hbound
      have hrecord (length : Nat) (record : ProposalExecutionRecord input)
          (hr : record ∈ (originalProposalRecord key input state.1).support) :
          Pr[fun result => hit result.2.2 = true |
            (simulateQ (originalLengthImpl key spent enabled update) (next record.output)).run
              (originalProposalAdvance update input state length record)] ≤
            certificateCacheExceptionPotential key (q - record.trace.hashCalls) record.cache := by
        have hnext := originalProposalRecord_query_bound key input next q hbound state.1 record hr
        have hcache := originalProposalRecord_cache_finite key input state.1 hfinite record hr
        have htail := ih record.output (q - record.trace.hashCalls) hnext.2
          (originalProposalAdvance update input state length record) hcache
        simp only [originalProposalAdvance] at htail
        apply htail.trans
        split_ifs with hafter
        · rw [hupdate input state length record] at hafter
          have hafterBad : CertificateCacheExceptional key record.cache := by
            simpa only [hfalse, hbad, decide_false, Bool.false_or, decide_eq_true_eq] using hafter
          exact certificateCacheExceptionPotential_bad key _ record.cache hcache hafterBad
        · exact le_rfl
      simp only [hhit]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum]
      apply le_trans _ (expected_originalProposalRecord_budgetPotential_le
        (certificateCacheExceptionPotential key)
        (fun remaining cache _ => certificateCacheExceptionPotential_mono key remaining cache)
        (expected_certificateCacheExceptionPotential_fresh_le key) key input q hquery state.1 hfinite)
      simp only [originalLengthImpl, lengthRecordImpl, StateT.run_mk]
      split
      · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        calc
          _ ≤ ∑' result, Pr[= result | recordLengthBridge (originalProposalRecord key input state.1)
                targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] *
              certificateCacheExceptionPotential key (q - result.2.trace.hashCalls) result.2.cache := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hr : result ∈ (recordLengthBridge (originalProposalRecord key input state.1)
                targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le).support
            · have hm := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨result, hr, rfl⟩
              rw [recordLengthBridge_record] at hm
              exact mul_le_mul' le_rfl (hrecord result.1 result.2 hm)
            · have hz : Pr[= result | recordLengthBridge (originalProposalRecord key input state.1)
                  targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] = 0 := by
                rw [PMF.probOutput_eq_apply]
                exact (PMF.apply_eq_zero_iff _ _).mpr hr
              rw [hz, zero_mul, zero_mul]
          _ = _ := by
            have hm := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
              ∑' record, Pr[= record | law] *
                certificateCacheExceptionPotential key (q - record.trace.hashCalls) record.cache)
              (recordLengthBridge_record (originalProposalRecord key input state.1)
                targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
            rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hm
            exact hm
      · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        apply ENNReal.tsum_le_tsum
        intro record
        by_cases hr : record ∈ (originalProposalRecord key input state.1).support
        · exact mul_le_mul' le_rfl (hrecord 0 record hr)
        · have hz : Pr[= record | originalProposalRecord key input state.1] = 0 := by
            rw [PMF.probOutput_eq_apply]
            exact (PMF.apply_eq_zero_iff _ _).mpr hr
          rw [hz, zero_mul, zero_mul]

end SphincsSecurity.Concrete
