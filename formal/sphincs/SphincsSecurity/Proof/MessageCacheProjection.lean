import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.SigningProposalRecord

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAttempt

noncomputable def messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => if MessageHashInput parameter input then cache input else none

theorem messageOnlyCache_apply (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : MessageHashInput parameter input) : messageOnlyCache parameter cache input = cache input :=
  if_pos hinput

theorem messageOnlyCache_payload (parameter : PublicParameter) (cache : QueryCache HashSpec) (payload : HashInput) :
    messageOnlyCache parameter cache (tweakableHashInput parameter .message payload) =
      cache (tweakableHashInput parameter .message payload) :=
  messageOnlyCache_apply parameter cache _ ⟨payload, rfl⟩

theorem messageAnswers_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    messageAnswers parameter (messageOnlyCache parameter cache) = messageAnswers parameter cache := by
  funext payload
  exact messageOnlyCache_payload parameter cache payload

theorem messageOnlyCache_eq_of_messageAnswers_eq (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hcache : messageAnswers parameter left = messageAnswers parameter right) :
    messageOnlyCache parameter left = messageOnlyCache parameter right := by
  funext input
  by_cases hmessage : MessageHashInput parameter input
  · obtain ⟨payload, rfl⟩ := hmessage
    rw [messageOnlyCache_payload, messageOnlyCache_payload]
    exact congrFun hcache payload
  · simp only [messageOnlyCache, if_neg hmessage]

theorem messageOnlyCache_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hinput : MessageHashInput parameter input) :
    messageOnlyCache parameter (cache.cacheQuery input output) =
      (messageOnlyCache parameter cache).cacheQuery input output := by
  funext other
  by_cases heq : other = input
  · subst other
    rw [messageOnlyCache_apply parameter _ _ hinput, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · simp only [messageOnlyCache, QueryCache.cacheQuery_of_ne _ _ heq]

theorem messageOnlyCache_randomOracle (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (hinput : MessageHashInput parameter input) :
    Prod.map id (messageOnlyCache parameter) <$> (randomOracle input).run cache =
      (randomOracle input).run (messageOnlyCache parameter cache) := by
  have hlookup := messageOnlyCache_apply parameter cache input hinput
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc,
        QueryImpl.withCaching_run_none _ (hlookup.trans hc)]
      simp only [Functor.map_map, Prod.map_apply, id_eq,
        messageOnlyCache_cacheQuery parameter cache input _ hinput]
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ (hlookup.trans hc), map_pure]
      rfl

theorem signDigestLoop_messageOnlyCache (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    Prod.map id (messageOnlyCache key.parameter) <$>
      (simulateQ romImpl (signDigestLoop attempts key message)).run cache =
        (simulateQ romImpl (signDigestLoop attempts key message)).run (messageOnlyCache key.parameter cache) := by
  induction attempts generalizing cache with
  | zero => simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, signDigestLoop_run_succ_eq, map_bind]
      apply bind_congr
      intro randomness
      rw [simulateQ_signAttempt_run_eq, simulateQ_signAttempt_run_eq]
      simp only [bind_assoc, pure_bind, map_bind]
      rw [← messageOnlyCache_randomOracle key.parameter cache _
        ⟨messageDigestPayload key.root message randomness, rfl⟩, bind_map_left]
      apply bind_congr
      rintro ⟨output, after⟩
      cases hattempt : signAttemptResultOfOutput output with
      | none => simpa only [signDigestLoopContinuation, Prod.map_apply, id_eq, hattempt] using ih after
      | some selected =>
          obtain ⟨index, leaves⟩ := selected
          simp only [signDigestLoopContinuation, Prod.map_apply, id_eq, hattempt, map_pure]

theorem signDigestLoop_publicFields (attempts : Nat) (left right : SecretKey)
    (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root) (message : Message) :
    signDigestLoop attempts left message = signDigestLoop attempts right message := by
  induction attempts with
  | zero => simp only [signDigestLoop]
  | succ attempts ih => simp only [signDigestLoop, signAttempt, hparameter, hroot, ih]

theorem completeSelectedLoopIndex_messageOnlyCache (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)) =
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run (messageOnlyCache key.parameter cache) >>=
      fun result => completeSelectedIndex (selectedLoopView? result)) := by
  rw [← signDigestLoop_messageOnlyCache, bind_map_left]
  rfl

theorem completeSelectedLoopIndex_congr (left right : SecretKey)
    (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root)
    (before after : QueryCache HashSpec)
    (hcache : messageAnswers left.parameter before = messageAnswers right.parameter after) (message : Message) :
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit left message)).run before >>=
      fun result => completeSelectedIndex (selectedLoopView? result)) =
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit right message)).run after >>=
      fun result => completeSelectedIndex (selectedLoopView? result)) := by
  rw [completeSelectedLoopIndex_messageOnlyCache left message before,
    completeSelectedLoopIndex_messageOnlyCache right message after,
    signDigestLoop_publicFields digestAttemptLimit left right hparameter hroot message, hparameter]
  congr 2
  apply messageOnlyCache_eq_of_messageAnswers_eq
  simpa only [hparameter] using hcache

private theorem probCompLift_apply {α : Type} (comp : ProbComp α) (value : α) :
    (liftM comp : PMF α) value = Pr[= value | comp] := by
  rw [← PMF.probOutput_eq_apply]
  rfl

theorem completedSigningRecord_index_congr_messageHistory {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (firstTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω₁)
    (secondTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω₂)
    (left right : SecretKey) (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root)
    (before after : QueryCache HashSpec)
    (hcache : messageAnswers left.parameter before = messageAnswers right.parameter after) (message : Message) :
    (completedSigningRecord firstTrace left message before).map Prod.snd =
      (completedSigningRecord secondTrace right message after).map Prod.snd := by
  ext index
  rw [completedSigningRecord_index, completedSigningRecord_index, probCompLift_apply, probCompLift_apply,
    probOutput_tracedSigningIndex_eq_loop, probOutput_tracedSigningIndex_eq_loop,
    completeSelectedLoopIndex_congr left right hparameter hroot before after hcache message]

noncomputable def signingProposalRejectedLaw {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) : PMF Index :=
  proposalResidualLaw (PMF.uniformOfFintype Index) ((completedSigningRecord trace key message cache).map Prod.snd)
    targetProposalAcceptance targetProposalAcceptance_lt_one
    (completedSigningRecord_acceptance_cap trace key message cache spent hbound)

theorem signingProposalRejectedLaw_congr_messageHistory {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (firstTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω₁)
    (secondTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω₂)
    (left right : SecretKey) (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root)
    (before after : QueryCache HashSpec)
    (hcache : messageAnswers left.parameter before = messageAnswers right.parameter after)
    (message : Message) (firstSpent secondSpent : Nat)
    (hleft : ProposalCacheBound left before firstSpent) (hright : ProposalCacheBound right after secondSpent) :
    signingProposalRejectedLaw firstTrace left message before firstSpent hleft =
      signingProposalRejectedLaw secondTrace right message after secondSpent hright := by
  ext index
  simp only [signingProposalRejectedLaw, proposalResidualLaw_apply,
    completedSigningRecord_index_congr_messageHistory firstTrace secondTrace left right hparameter hroot before after hcache message]

theorem cachedMessageInputSet_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) :
    cachedMessageInputSet (messageOnlyCache parameter cache) parameter root message =
      cachedMessageInputSet cache parameter root message := by
  ext ⟨input, output⟩
  constructor <;> rintro ⟨hcached, randomness, hinput⟩
  · refine ⟨?_, randomness, hinput⟩
    change input = tweakableHashInput parameter .message (messageDigestPayload root message randomness) at hinput
    subst input
    simpa only [QueryCache.mem_toSet, messageOnlyCache_payload] using hcached
  · refine ⟨?_, randomness, hinput⟩
    change input = tweakableHashInput parameter .message (messageDigestPayload root message randomness) at hinput
    subst input
    simpa only [QueryCache.mem_toSet, messageOnlyCache_payload] using hcached

theorem cachedMessageEntryCount_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) :
    cachedMessageEntryCount (messageOnlyCache parameter cache) parameter root message =
      cachedMessageEntryCount cache parameter root message := by
  rw [cachedMessageEntryCount, cachedMessageEntryCount, cachedMessageInputSet_messageOnlyCache]

theorem cachedMessageEntryCountWhere_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedMessageEntryCountWhere (messageOnlyCache parameter cache) parameter root message P =
      cachedMessageEntryCountWhere cache parameter root message P := by
  simp only [cachedMessageEntryCountWhere, cachedMessageInputSetWhere, cachedMessageInputSet_messageOnlyCache]

theorem messageDeficitExceptional_messageOnlyCache (key : SecretKey) (cache : QueryCache HashSpec) :
    MessageDeficitExceptional key (messageOnlyCache key.parameter cache) ↔ MessageDeficitExceptional key cache := by
  simp only [MessageDeficitExceptional, messageAdmissibleDeficit, cachedMessageEntryCount_messageOnlyCache,
    cachedMessageEntryCountWhere_messageOnlyCache]

theorem cacheMessageWeight_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight (messageOnlyCache parameter cache) = cacheMessageWeight parameter weight cache := by
  apply tsum_congr
  intro input
  by_cases hmessage : MessageHashInput parameter input
  · simp only [cacheMessageEntryWeight, messageOnlyCache_apply parameter cache input hmessage]
  · simp only [cacheMessageEntryWeight, messageOnlyCache, if_neg hmessage]
    cases cache input <;> simp only [hmessage, false_and, if_false]

theorem cachedIndexMultiplicity_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) (index : Index) :
    cachedIndexMultiplicity parameter (messageOnlyCache parameter cache) index = cachedIndexMultiplicity parameter cache index :=
  cacheMessageWeight_messageOnlyCache parameter cache _

theorem targetIndexMoments_messageOnlyCache (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) :
    targetIndexMoments key (messageOnlyCache key.parameter cache) log power degree =
      targetIndexMoments key cache log power degree := by
  simp only [targetIndexMoments, cachedIndexMultiplicity_messageOnlyCache, messageAnswers_messageOnlyCache]

theorem observedRawIndexShapeVector_messageOnlyCache (key : SecretKey) (state : CoverLogState) :
    observedRawIndexShapeVector key (messageOnlyCache key.parameter state.1, state.2) =
      observedRawIndexShapeVector key state := by
  funext groups remaining
  exact targetIndexMoments_messageOnlyCache key state.1 state.2 groups.card remaining.card

theorem reuseRawEnvelope_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (state : CoverLogState) :
    reuseRawEnvelope key reuse queries signatures (messageOnlyCache key.parameter state.1, state.2) =
      reuseRawEnvelope key reuse queries signatures state := by
  unfold reuseRawEnvelope
  rw [observedRawIndexShapeVector_messageOnlyCache]

theorem reuseRawEnvelope_publicFields (left right : SecretKey)
    (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root)
    (reuse : ENNReal) (queries signatures : Nat) (state : CoverLogState) :
    reuseRawEnvelope left reuse queries signatures state = reuseRawEnvelope right reuse queries signatures state := by
  unfold reuseRawEnvelope observedRawIndexShapeVector targetIndexMoments
  rw [hparameter, hroot]

theorem reuseRawEnvelope_congr_messageHistory (left right : SecretKey)
    (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root)
    (before after : QueryCache HashSpec)
    (hcache : messageAnswers left.parameter before = messageAnswers right.parameter after)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signatures : Nat) :
    reuseRawEnvelope left reuse queries signatures (before, log) =
      reuseRawEnvelope right reuse queries signatures (after, log) := by
  rw [← reuseRawEnvelope_messageOnlyCache left reuse queries signatures (before, log),
    ← reuseRawEnvelope_messageOnlyCache right reuse queries signatures (after, log),
    reuseRawEnvelope_publicFields left right hparameter hroot, hparameter]
  congr 2
  apply messageOnlyCache_eq_of_messageAnswers_eq
  simpa only [hparameter] using hcache

end SphincsSecurity.Concrete
