import SphincsSecurity.Proof.FutureTargetAssignment
import SphincsSecurity.Proof.AllMessageReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetAssignmentInputIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (input : HashInput) (source : FewTimeView) : ENNReal :=
  if input = tweakableHashInput key.parameter .message payload then 0 else
    futureTargetAssignmentIncrement
      (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) remaining target source

noncomputable def cachedTargetAssignmentIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (source : FewTimeView) : ENNReal :=
  cacheMessageWeight key.parameter (fun targetInput target =>
    targetAssignmentInputIncrement remaining key before log (payloadOf targetInput) target input source) before

noncomputable def allMessageTargetAssignmentReuseCharge (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (cachedTargetAssignmentIncrement remaining key before log) before * digestReuseWeight q

theorem targetCoverageInputIncrement_le_assignment (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (input : HashInput) (source : FewTimeView) :
    targetCoverageInputIncrement remaining key before log payload target input source ≤
      targetAssignmentInputIncrement remaining key before log payload target input source := by
  unfold targetCoverageInputIncrement targetAssignmentInputIncrement
  split_ifs
  · exact le_rfl
  · exact futureFewTimeCoverageIncrement_le_assignment _ remaining target source

theorem cachedTargetFutureIncrement_le_assignment (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (source : FewTimeView) :
    cachedTargetFutureIncrement remaining key before log input source ≤
      cachedTargetAssignmentIncrement remaining key before log input source :=
  cacheMessageWeight_mono _ _ _ _ (fun targetInput target =>
    targetCoverageInputIncrement_le_assignment remaining key before log (payloadOf targetInput) target input source)

theorem allMessageTargetReuseCharge_le_assignment (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) :
    allMessageTargetReuseCharge remaining key before log q ≤
      allMessageTargetAssignmentReuseCharge remaining key before log q :=
  mul_le_mul' (cacheMessageWeight_mono _ _ _ _ (cachedTargetFutureIncrement_le_assignment remaining key before log)) le_rfl

theorem targetAssignmentInputIncrement_self (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView) :
    targetAssignmentInputIncrement remaining key before log payload target
      (tweakableHashInput key.parameter .message payload) source = 0 := by
  simp only [targetAssignmentInputIncrement, if_true]

theorem targetAssignmentInputIncrement_cache_stable (remaining : Nat) (key : SecretKey)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView)
    (input : HashInput) (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetAssignmentInputIncrement remaining key after log payload target input source =
      targetAssignmentInputIncrement remaining key before log payload target input source := by
  have hstable : eligibleSigningViews (messageAnswers key.parameter after) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  simp only [targetAssignmentInputIncrement, hstable]

theorem targetTreeMatchCount_log (log : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view (log.get slot)) target tree =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0)).sum := by
  rw [targetTreeMatchCount, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0))

theorem targetTreeMatchCount_log_append (log suffix : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view ((log ++ suffix).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        targetTreeMatchCount (fun slot => view (suffix.get slot)) target tree := by
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append]

theorem targetAssignmentInputIncrement_log_mono (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log suffix : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView)
    (input : HashInput) :
    targetAssignmentInputIncrement remaining key before log payload target input source ≤
      targetAssignmentInputIncrement remaining key before (log ++ suffix) payload target input source := by
  unfold targetAssignmentInputIncrement
  split_ifs
  · exact le_rfl
  · apply futureTargetAssignmentIncrement_mono
    intro tree
    change targetTreeMatchCount (fun slot => eligibleSigningView? (messageAnswers key.parameter before) key.root payload (log.get slot)) target tree ≤
      targetTreeMatchCount (fun slot => eligibleSigningView? (messageAnswers key.parameter before) key.root payload ((log ++ suffix).get slot)) target tree
    rw [targetTreeMatchCount_log_append]
    exact Nat.le_add_right _ _

theorem allMessageTargetAssignmentReuseCharge_log_mono (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log suffix : QueryLog SigningSpec) (q : Nat) :
    allMessageTargetAssignmentReuseCharge remaining key before log q ≤
      allMessageTargetAssignmentReuseCharge remaining key before (log ++ suffix) q := by
  apply mul_le_mul' _ le_rfl
  apply cacheMessageWeight_mono
  intro input source
  apply cacheMessageWeight_mono
  intro targetInput target
  exact targetAssignmentInputIncrement_log_mono remaining key before log suffix (payloadOf targetInput) target source input

theorem cachedTargetAssignmentIncrement_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input sourceInput : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (source : FewTimeView) :
    cachedTargetAssignmentIncrement remaining key (before.cacheQuery input output) log sourceInput source =
      cachedTargetAssignmentIncrement remaining key before log sourceInput source +
        if FtsProbeSimulation.MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          targetAssignmentInputIncrement remaining key before log (payloadOf input) (hashOutputFewTimeView output) sourceInput source else 0 := by
  have hweight : (fun targetInput target => targetAssignmentInputIncrement remaining key
        (before.cacheQuery input output) log (payloadOf targetInput) target sourceInput source) =
      (fun targetInput target => targetAssignmentInputIncrement remaining key before log (payloadOf targetInput) target sourceInput source) := by
    funext targetInput target
    exact targetAssignmentInputIncrement_cache_stable remaining key before _ log _ target source sourceInput
      (QueryCache.le_cacheQuery before hfresh) hsigned
  rw [cachedTargetAssignmentIncrement, hweight, cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  rfl

theorem cachedTargetAssignmentIncrement_cacheQuery_self (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) (source : FewTimeView) :
    cachedTargetAssignmentIncrement remaining key (before.cacheQuery input output) log input source =
      cachedTargetAssignmentIncrement remaining key before log input source := by
  rw [cachedTargetAssignmentIncrement_cacheQuery remaining key before log input input output hfresh hsigned source]
  split_ifs with hgood
  · obtain ⟨payload, rfl⟩ := hgood.1
    rw [payloadOf_tweakableHashInput, targetAssignmentInputIncrement_self, add_zero]
  · exact add_zero _

end SphincsSecurity.Concrete
