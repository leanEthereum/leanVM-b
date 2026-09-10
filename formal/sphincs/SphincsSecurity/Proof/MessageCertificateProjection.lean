import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CertificateBoundaryInvariants
import SphincsSecurity.Proof.MessageCacheProjection

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable

theorem messageOnlyCache_idempotent (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    messageOnlyCache parameter (messageOnlyCache parameter cache) = messageOnlyCache parameter cache := by
  funext input
  by_cases hinput : MessageHashInput parameter input <;> simp only [messageOnlyCache, hinput, if_true, if_false]

theorem messageOnlyCache_le (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    messageOnlyCache parameter cache ≤ cache := by
  intro input output houtput
  by_cases hinput : MessageHashInput parameter input
  · simpa only [messageOnlyCache, if_pos hinput] using houtput
  · simp only [messageOnlyCache, if_neg hinput] at houtput
    cases houtput

theorem messageOnlyCache_enncard_le (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    QueryCache.enncard (messageOnlyCache parameter cache) ≤ QueryCache.enncard cache :=
  QueryCache.enncard_mono (messageOnlyCache_le parameter cache)

theorem signingDigestsCached_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) :
    SigningDigestsCached parameter (messageOnlyCache parameter cache) root log ↔
      SigningDigestsCached parameter cache root log := by
  simp only [SigningDigestsCached, messageAnswers_messageOnlyCache]

theorem proposalCacheBound_messageOnlyCache (key : SecretKey) (cache : QueryCache HashSpec) (spent : Nat)
    (hcache : QueryCache.enncard cache ≤ spent) :
    ProposalCacheBound key (messageOnlyCache key.parameter cache) spent ↔ ProposalCacheBound key cache spent := by
  constructor
  · intro h
    exact ⟨h.spent_le, hcache, (messageDeficitExceptional_messageOnlyCache key cache).not.mp h.no_deficit,
      fun index => by simpa only [cachedIndexMultiplicity_messageOnlyCache] using h.index_le index⟩
  · intro h
    exact ⟨h.spent_le, (messageOnlyCache_enncard_le key.parameter cache).trans hcache,
      (messageDeficitExceptional_messageOnlyCache key cache).not.mpr h.no_deficit,
      fun index => by simpa only [cachedIndexMultiplicity_messageOnlyCache] using h.index_le index⟩

theorem certificateMonitorReady_messageOnlyCache (key : SecretKey) (budget : Nat)
    (cache : QueryCache HashSpec) (monitor : CertificateMonitor)
    (hcache : QueryCache.enncard cache ≤ monitor.spent) :
    CertificateMonitorReady key budget (messageOnlyCache key.parameter cache, monitor) ↔
      CertificateMonitorReady key budget (cache, monitor) := by
  simp only [CertificateMonitorReady, signingDigestsCached_messageOnlyCache,
    proposalCacheBound_messageOnlyCache key cache monitor.spent hcache]

theorem certificateMonitorActive_messageOnlyCache (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (monitor : CertificateMonitor)
    (hcache : QueryCache.enncard cache ≤ monitor.spent) :
    CertificateMonitorActive key budget input (messageOnlyCache key.parameter cache, monitor) ↔
      CertificateMonitorActive key budget input (cache, monitor) := by
  simp only [CertificateMonitorActive, certificateMonitorReady_messageOnlyCache key budget cache monitor hcache]

theorem targetCoveredOn_messageOnlyCache (key : SecretKey) (required : Finset FtsTree)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) :
    TargetCoveredOn key required (messageOnlyCache key.parameter cache, log) payload target ↔
      TargetCoveredOn key required (cache, log) payload target := by
  simp only [TargetCoveredOn, messageAnswers_messageOnlyCache]

theorem targetCertificateAt_messageOnlyCache (key : SecretKey) (required : Finset FtsTree)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) :
    TargetCertificateAt key required (messageOnlyCache key.parameter cache, log) input ↔
      TargetCertificateAt key required (cache, log) input := by
  simp only [TargetCertificateAt, targetCoveredOn_messageOnlyCache]
  constructor <;> rintro ⟨output, houtput, hmessage, hadmissible, hcovered⟩
  · exact ⟨output, (messageOnlyCache_apply key.parameter cache input hmessage).symm.trans houtput,
      hmessage, hadmissible, hcovered⟩
  · exact ⟨output, (messageOnlyCache_apply key.parameter cache input hmessage).trans houtput,
      hmessage, hadmissible, hcovered⟩

theorem completedTargetBank_messageOnlyCache (key : SecretKey) (required : Finset FtsTree)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (bank : HashInput → Bool) :
    completedTargetBank key required (messageOnlyCache key.parameter cache, log) bank =
      completedTargetBank key required (cache, log) bank := by
  funext input
  simp only [completedTargetBank, targetCertificateAt_messageOnlyCache]

theorem freshDigestSelectionProbability_messageOnlyCache (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message (messageOnlyCache key.parameter cache) =
      freshDigestSelectionProbability key message cache := by
  unfold freshDigestSelectionProbability
  rw [← signDigestLoop_messageOnlyCache, probEvent_map]
  congr 1
  funext result
  obtain ⟨selected, after⟩ := result
  cases selected <;> simp only [Function.comp_apply, freshSelectedLoopView?, Prod.map_apply, id_eq,
    messageOnlyCache_payload]

theorem freshWorldTargetHashCost_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : OracleWorld.Domain) :
    freshWorldTargetHashCost parameter (messageOnlyCache parameter cache) input =
      freshWorldTargetHashCost parameter cache input := by
  cases input with
  | inl sample => rfl
  | inr input =>
      by_cases hinput : MessageHashInput parameter input <;>
        simp only [freshWorldTargetHashCost, hinput, messageOnlyCache, if_true, if_false, false_and]

theorem targetCreationMultiplier_messageOnlyCache (key : SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetCreationMultiplier key (messageOnlyCache key.parameter cache) input =
      targetCreationMultiplier key cache input := by
  cases input with
  | inl world => simp only [targetCreationMultiplier, freshWorldTargetHashCost_messageOnlyCache]
  | inr message => simp only [targetCreationMultiplier, freshDigestSelectionProbability_messageOnlyCache]

theorem targetCreationPrice_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    targetCreationPrice key reuse budget signatures required (messageOnlyCache key.parameter cache, log) =
      targetCreationPrice key reuse budget signatures required (cache, log) := by
  unfold targetCreationPrice
  rw [reuseRawEnvelope_messageOnlyCache key reuse budget signatures (cache, log)]

def SpentIndexExceptional (parameter : PublicParameter) (cache : QueryCache HashSpec) (spent : Nat) : Prop :=
  ∃ index, (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal) <
    cachedIndexMultiplicity parameter cache index

theorem spentIndexExceptional_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) (spent : Nat) :
    SpentIndexExceptional parameter (messageOnlyCache parameter cache) spent ↔ SpentIndexExceptional parameter cache spent := by
  simp only [SpentIndexExceptional, cachedIndexMultiplicity_messageOnlyCache]

theorem spentIndexExceptional_implies_cacheException (key : SecretKey) (cache : QueryCache HashSpec)
    (spent : Nat) (hcache : QueryCache.enncard cache ≤ spent)
    (hbad : SpentIndexExceptional key.parameter cache spent) : CertificateCacheExceptional key cache := by
  obtain ⟨index, hindex⟩ := hbad
  exact Or.inr (cachedIndexExcessExceptional_of_bound_failure key.parameter cache
    (Finite.of_enncard_le hcache) spent hcache index hindex)

noncomputable def messageCertificateRecord (parameter : PublicParameter)
    {input : (OracleWorld + SigningSpec).Domain} (record : ProposalExecutionRecord input) : ProposalExecutionRecord input :=
  { record with cache := messageOnlyCache parameter record.cache }

noncomputable def messageCertificateState (parameter : PublicParameter)
    (state : CertificateMonitorState) : CertificateMonitorState :=
  (messageOnlyCache parameter state.1, state.2)

noncomputable def messageCertificateStop (parameter : PublicParameter) (stopAfter : CertificateStopRule) : CertificateStopRule :=
  fun input state length record => stopAfter input (messageCertificateState parameter state) length
    (messageCertificateRecord parameter record)

theorem certificateMonitorUpdate_messageOnlyCache (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (monitor : CertificateMonitor)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hcache : QueryCache.enncard cache ≤ monitor.spent)
    (hafter : QueryCache.enncard record.cache ≤ (monitor.spent + record.trace.hashCalls : Nat)) :
    certificateMonitorUpdate key budget required (messageCertificateStop key.parameter stopAfter)
      input (cache, monitor) length record =
    certificateMonitorUpdate key budget required stopAfter
      input (messageOnlyCache key.parameter cache, monitor) length (messageCertificateRecord key.parameter record) := by
  have hactive := certificateMonitorActive_messageOnlyCache key budget input cache monitor hcache
  by_cases ha : CertificateMonitorActive key budget input (cache, monitor)
  · rw [certificateMonitorUpdate, if_pos ha, certificateMonitorUpdate, if_pos (hactive.mpr ha)]
    simp only [messageCertificateRecord, messageCertificateStop, messageCertificateState, proposalRecordLogState,
      certificateMonitorCoverState, targetCreationMultiplier_messageOnlyCache, targetCreationPrice_messageOnlyCache,
      completedTargetBank_messageOnlyCache]
    congr 1
    congr 1
    apply decide_eq_decide.mpr
    simp only [CertificateMonitorReady, signingDigestsCached_messageOnlyCache,
      proposalCacheBound_messageOnlyCache key record.cache (monitor.spent + record.trace.hashCalls) hafter]
  · rw [certificateMonitorUpdate, if_neg ha, certificateMonitorUpdate, if_neg (hactive.not.mpr ha)]

theorem certificateMonitorUpdate_messageOnlyCache_of_originalRecord (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (monitor : CertificateMonitor)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hcache : QueryCache.enncard cache ≤ monitor.spent)
    (hrecord : record ∈ (originalProposalRecord key input cache).support) :
    certificateMonitorUpdate key budget required (messageCertificateStop key.parameter stopAfter)
      input (cache, monitor) length record =
    certificateMonitorUpdate key budget required stopAfter
      input (messageOnlyCache key.parameter cache, monitor) length (messageCertificateRecord key.parameter record) := by
  apply certificateMonitorUpdate_messageOnlyCache key budget required stopAfter input cache monitor length record hcache
  simpa only [Nat.cast_add] using (originalProposalRecord_enncard_le key input cache record hrecord).trans
    (add_le_add hcache le_rfl)

theorem observedTargetShapeVector_messageOnlyCache (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    observedTargetShapeVector key payload target (messageOnlyCache key.parameter cache, log) =
      observedTargetShapeVector key payload target (cache, log) := by
  funext groups remaining
  simp only [observedTargetShapeVector, targetShapeMoments, normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_messageOnlyCache, normalizedTargetLogProduct, normalizedTargetLogMatch,
    messageAnswers_messageOnlyCache]

theorem targetCertificateForecast_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (input : HashInput) (target : FewTimeView) :
    targetCertificateForecast key reuse budget signatures required (messageOnlyCache key.parameter cache, log) input target =
      targetCertificateForecast key reuse budget signatures required (cache, log) input target := by
  simp only [targetCertificateForecast, reuseTargetEnvelope, observedTargetShapeVector_messageOnlyCache]

theorem bankedCacheWeight_messageOnlyCache (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool) (stopped : Bool) (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank stopped (messageOnlyCache parameter cache) =
      bankedCacheWeight parameter weight bank stopped cache := by
  cases stopped <;> simp only [bankedCacheWeight_stopped, bankedCacheWeight_live, cacheMessageWeight_messageOnlyCache]

theorem bankedTargetEnvelope_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required (messageOnlyCache key.parameter cache, log) bank stopped =
      bankedTargetEnvelope key reuse budget signatures required (cache, log) bank stopped := by
  simp only [bankedTargetEnvelope]
  have hweight := funext fun input => funext fun target =>
    targetCertificateForecast_messageOnlyCache key reuse budget signatures required cache log input target
  rw [hweight, bankedCacheWeight_messageOnlyCache]

theorem bankedTargetEnvelope_congr_messageHistory (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (before after : QueryCache HashSpec)
    (hcache : messageAnswers key.parameter before = messageAnswers key.parameter after)
    (log : QueryLog SigningSpec) (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required (before, log) bank stopped =
      bankedTargetEnvelope key reuse budget signatures required (after, log) bank stopped := by
  rw [← bankedTargetEnvelope_messageOnlyCache key reuse budget signatures required before log bank stopped,
    ← bankedTargetEnvelope_messageOnlyCache key reuse budget signatures required after log bank stopped,
    messageOnlyCache_eq_of_messageAnswers_eq key.parameter before after hcache]

theorem certificateMonitorPotential_messageOnlyCache (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (monitor : CertificateMonitor) :
    certificateMonitorPotential key budget required (messageOnlyCache key.parameter cache, monitor) =
      certificateMonitorPotential key budget required (cache, monitor) := by
  simp only [certificateMonitorPotential, certificateMonitorCoverState, bankedTargetEnvelope_messageOnlyCache]

theorem bankedTargetEnvelope_complete_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required state (completedTargetBank key required state bank) stopped ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false := by
  apply bankedCacheWeight_bank_le
  intro input hcomplete
  exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required state input
    (of_decide_eq_true hcomplete)

theorem bankedProposalRecordValue_world_le_of_messageHistory (key : SecretKey) (reuse : ENNReal)
    (budget signatures : Nat) (required : Finset FtsTree) (state : CoverLogState)
    (bank : HashInput → Bool) (input : OracleWorld.Domain) (record : ProposalExecutionRecord (.inl input))
    (stopped : Bool) (hcache : messageAnswers key.parameter record.cache = messageAnswers key.parameter state.1) :
    bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) record stopped ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false := by
  simp only [bankedProposalRecordValue, proposalRecordLogState, signingLogFragment, List.append_nil]
  apply (bankedTargetEnvelope_complete_le key reuse (budget - record.trace.hashCalls) signatures required
    (record.cache, state.2) bank stopped).trans
  rw [bankedTargetEnvelope_congr_messageHistory key reuse (budget - record.trace.hashCalls) signatures required
    record.cache state.1 hcache state.2 bank false]
  exact bankedTargetEnvelope_budget_mono key reuse signatures required state bank false (Nat.sub_le _ _)

theorem expected_world_bankedProposalRecord_le_of_messageHistory {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (law : PMF α) (record : α → ProposalExecutionRecord (.inl input)) (stopped : α → Bool)
    (hcache : ∀ result ∈ law.support,
      messageAnswers key.parameter (record result).cache = messageAnswers key.parameter state.1) :
    (∑' result, law result *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) (record result) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false := by
  classical
  calc
    _ ≤ ∑' result, law result * bankedTargetEnvelope key reuse budget signatures required state bank false := by
      apply ENNReal.tsum_le_tsum
      intro result
      rcases Classical.em (law result = 0) with hr | hr
      · simp only [hr, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (bankedProposalRecordValue_world_le_of_messageHistory key reuse budget signatures
          required state bank input (record result) (stopped result) (hcache result hr))
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem expected_certificateMonitor_world_le_of_messageHistory {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : OracleWorld.Domain) (state : CertificateMonitorState)
    (law : PMF α) (length : α → Nat) (record : α → ProposalExecutionRecord (.inl input))
    (hcache : ∀ result ∈ law.support,
      messageAnswers key.parameter (record result).cache = messageAnswers key.parameter state.1) :
    (∑' result, law result * certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
        (.inl input) state (length result) (record result))) ≤
      certificateMonitorPotential key budget required state := by
  by_cases hactive : CertificateMonitorActive key budget (.inl input) state
  · simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inl input) state _ _ hactive,
      signingLogFragment, List.append_nil]
    have h := expected_world_bankedProposalRecord_le_of_messageHistory key nearUniformDigestReuseWeight
      (budget - state.2.spent) (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state)
      state.2.bank input law record
      (fun result => (certificateMonitorUpdate key budget required stopAfter (.inl input) state
        (length result) (record result)).stopped) hcache
    simpa only [certificateMonitorPotential, hactive.1] using h
  · simp only [certificateMonitorPotential_advance_inactive key budget required stopAfter (.inl input) state _ _ hactive]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

end SphincsSecurity.Concrete
