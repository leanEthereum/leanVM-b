import SphincsSecurity.Proof.CertificateCleanExecution

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation withSigningLog
  signingTraceComputation signingTraceComputation_fst unloggedRetainedRestComputation
  retainedGameRestComputation_eq_signingTrace arrangeRetainedTrace)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initialCertificateMonitor_ready (key : SecretKey) (budget spent : Nat)
    (cache : QueryCache HashSpec) (stopped : Bool)
    (hbudget : budget ≤ 2 ^ 127) (hspent : spent ≤ budget)
    (hcache : QueryCache.enncard cache ≤ spent)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    CertificateMonitorReady key budget (cache, initialCertificateMonitor spent stopped) := by
  have hfinite := Finite.of_enncard_le hcache
  have hclean : ¬ CertificateCacheExceptional key cache := by
    intro hbad
    have hzero := certificateCacheExceptionPotential_initial_le key 0 (by omega) cache hnone
    have hone := certificateCacheExceptionPotential_bad key 0 cache hfinite hbad
    simp only [Nat.cast_zero, ENNReal.zero_div, add_zero] at hzero
    exact (not_le_of_gt (by norm_num : (0 : ENNReal) < 1)) (hone.trans hzero)
  refine ⟨?_, proposalCacheBound_of_no_cache_exception key cache hfinite spent
    (hspent.trans hbudget) hcache hclean, hspent⟩
  intro entry hentry
  simp only [initialCertificateMonitor, List.not_mem_nil] at hentry

theorem certificateCacheProposal_withSigningLog_clean {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : List Index × CertificateCacheMonitorState)
    (hready : CertificateMonitorReady key budget (certificateCacheMonitorProject state.2))
    (halive : state.2.2.1.stopped = false) (hroom : state.2.2.1.spent + q ≤ budget)
    (result : (α × QueryLog SigningSpec) × (List Index × CertificateCacheMonitorState))
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required proposalPrefixStop)
      (withSigningLog computation state.2.2.1.log)).run state).support)
    (hvalid : SigningTranscript.Valid result.1.2) (hhit : result.2.2.2.2 = false)
    (hprefix : ¬ ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject result.2.2) := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheProposalImpl_length] at hm
  exact certificateCacheLength_withSigningLog_clean key budget required hbudget computation q hbound
    state.2 hready halive hroom _ hm hvalid hhit hprefix

theorem certificateCacheProposal_rest_clean (adversary : Adversary) (publicKey : PublicKey)
    (key : SecretKey) (budget q : Nat) (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (hbound : (simulateQ (expandedAdversaryImpl key)
      (retainedGameRestComputation adversary publicKey)).IsQueryBoundP (· matches .inr _) q)
    (state : List Index × CertificateCacheMonitorState)
    (hready : CertificateMonitorReady key budget (certificateCacheMonitorProject state.2))
    (halive : state.2.2.1.stopped = false) (hlog : state.2.2.1.log = [])
    (hroom : state.2.2.1.spent + q ≤ budget) (result : CertificateCacheGameResult)
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required proposalPrefixStop)
      (retainedGameRestComputation adversary publicKey)).run state).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateGameExceptional result) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject result.2.2) := by
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, isQueryBoundP_map_iff] at hbound
  have hforget : Prod.fst <$> simulateQ (expandedAdversaryImpl key)
      (signingTraceComputation (unloggedRetainedRestComputation adversary publicKey)) =
        simulateQ (expandedAdversaryImpl key) (unloggedRetainedRestComputation adversary publicKey) := by
    rw [← simulateQ_map, signingTraceComputation_fst]
  have hunlogged := (isQueryBoundP_iff_of_map_eq (p := (· matches Sum.inr _)) hforget).mp hbound
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, rfl⟩ := hr
  have htrace : withSigningLog (unloggedRetainedRestComputation adversary publicKey) state.2.2.1.log =
      signingTraceComputation (unloggedRetainedRestComputation adversary publicKey) := by
    simp only [withSigningLog, hlog, List.nil_append, Prod.mk.eta]
    exact id_map _
  have hresult := certificateCacheProposal_withSigningLog_clean key budget required hbudget
    (unloggedRetainedRestComputation adversary publicKey) q hunlogged state hready halive hroom source
    (by rwa [htrace]) hvalid (Bool.eq_false_iff.mpr (fun h => hclean (Or.inl h)))
    (fun h => hclean (Or.inr h))
  exact hresult

theorem certificateCacheGame_clean (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127)
    (result : CertificateCacheGameResult)
    (hr : result ∈ (certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateGameExceptional result) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.1.2 := by
  rw [certificateCacheGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [probCompLift_support] at hgenerated
  have hwhole : (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2).IsQueryBoundP
      (· matches .inr _) q := hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q hwhole ∅ generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, isQueryBoundP_map_iff] at hrest
  have hcache := boundaryRun_enncard_le 0 scheme.keygen ∅ generated hgenerated
  rw [QueryCache.enncard_empty, zero_add] at hcache
  have hkeys : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hgenerated, rfl⟩
  have hnone := keygen_cache_message_none (generated.1.1, generated.2) hkeys
  have hready := initialCertificateMonitor_ready generated.1.1.2 q generated.1.2.hashCalls
    generated.2 false hq hkeygen.1 hcache hnone
  have hresult := certificateCacheProposal_rest_clean adversary generated.1.1.1 generated.1.1.2
    q (q - generated.1.2.hashCalls) required hq hrest
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls false, false)
    hready rfl rfl (by change generated.1.2.hashCalls + (q - generated.1.2.hashCalls) ≤ q; omega)
    result hr hvalid hclean
  exact ⟨hresult.1, hresult.2.1⟩

theorem certificateCacheGame_clean_win (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127)
    (result : CertificateCacheGameResult)
    (hr : result ∈ (certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false).support)
    (hwin : certificateGameVerdict result.1 = true) (hclean : ¬ CertificateGameExceptional result) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.1.2 := by
  rw [certificateGameVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
  exact certificateCacheGame_clean adversary q required hbound hq result hr hwin.1.1 hclean

theorem probEvent_certificateCacheGame_valid_stop_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    Pr[fun result => SigningTranscript.Valid result.1.1.2 ∧
      (result.2.2.2.1.stopped = true ∨ result.2.2.2.1.log ≠ result.1.1.2) |
        certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false] ≤
      (q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹ := by
  apply le_trans _ (probEvent_certificateGameExceptional_le adversary q required
    (fun _ => proposalPrefixStop) false hbound hq)
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false).support
  · by_cases hclean : ¬ CertificateGameExceptional result
    · by_cases hvalid : SigningTranscript.Valid result.1.1.2
      · have h := certificateCacheGame_clean adversary q required hbound hq result hr hvalid hclean
        simp only [hclean, hvalid, h.1, h.2, Bool.false_eq_true, ne_eq, not_true_eq_false,
          or_self, and_false, if_false, le_refl]
      · simp only [hvalid, false_and, if_false, zero_le]
    · simp only [not_not] at hclean
      simp only [hclean, if_true]
      split <;> simp only [le_refl, zero_le]
  · simp only [(PMF.apply_eq_zero_iff _ _).mpr hr, ite_self, le_refl]

theorem forgeAdvantage_le_certificateCacheGame_live_add (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => certificateGameVerdict result.1 = true ∧ result.2.2.2.1.stopped = false ∧
        result.2.2.2.1.log = result.1.1.2 ∧ ¬ CertificateGameExceptional result |
          certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false] +
        ((q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹) := by
  apply (forgeAdvantage_le_certificateCacheGame_clean_add adversary q required
    (fun _ => proposalPrefixStop) false hbound hq).trans
  refine add_le_add ?_ le_rfl
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (certificateCacheGame adversary q required (fun _ => proposalPrefixStop) false).support
  · by_cases hw : certificateGameVerdict result.1 = true ∧ ¬ CertificateGameExceptional result
    · have h := certificateCacheGame_clean_win adversary q required hbound hq result hr hw.1 hw.2
      simp only [hw.1, hw.2, h.1, h.2, not_false_eq_true, and_self, if_true, le_refl]
    · simp only [hw, if_false, zero_le]
  · simp only [(PMF.apply_eq_zero_iff _ _).mpr hr, ite_self, le_refl]

end SphincsSecurity.Concrete
