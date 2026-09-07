import SphincsSecurity.Proof.SubsetTargetExpectation
import SphincsSecurity.Proof.TargetAssignmentSigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetSubsetMatch (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  cacheMessageWeight parameter (fun input source =>
    if input = targetInput then 0 else (sourceSubsetMatch target source required : ENNReal)) cache

noncomputable def cachedPartialTargetIncrement (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (views : Fin n → Option FewTimeView) (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  cacheMessageWeight parameter (fun input source =>
    if input = targetInput then 0 else (partialTargetAssignmentIncrement views target source required : ENNReal)) cache

theorem cachedPartialTargetIncrement_eq_subsets (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (views : Fin n → Option FewTimeView) (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) :
    cachedPartialTargetIncrement parameter cache views targetInput target required =
      ∑ selected ∈ required.powerset.erase ∅, cachedTargetSubsetMatch parameter cache targetInput target selected *
        (partialTargetAssignmentCount views target (required \ selected) : ENNReal) := by
  unfold cachedPartialTargetIncrement partialTargetAssignmentIncrement
  simp only [Nat.cast_sum, Nat.cast_mul]
  have hpoint (input : HashInput) (source : FewTimeView) :
      (if input = targetInput then 0 else ∑ selected ∈ required.powerset.erase ∅,
        (sourceSubsetMatch target source selected : ENNReal) * (partialTargetAssignmentCount views target (required \ selected) : ENNReal)) =
      ∑ selected ∈ required.powerset.erase ∅,
        (if input = targetInput then 0 else (sourceSubsetMatch target source selected : ENNReal)) *
          (partialTargetAssignmentCount views target (required \ selected) : ENNReal) := by
    split_ifs <;> simp only [zero_mul, Finset.sum_const_zero]
  simp only [hpoint, cacheMessageWeight_sum, cacheMessageWeight_mul_right]
  rfl

theorem targetAssignmentInputReuseCharge_zero_le_subsets (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (q : Nat) :
    targetAssignmentInputReuseCharge 0 key message before log payload target q ≤
      (∑ selected ∈ (Finset.univ : Finset FtsTree).powerset.erase ∅,
        cachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
          (partialTargetAssignmentCount (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter before)
            key.root payload log) target (Finset.univ \ selected) : ENNReal)) * digestReuseWeight q := by
  rw [← cachedPartialTargetIncrement_eq_subsets]
  apply mul_le_mul' _ le_rfl
  exact ENNReal.tsum_le_tsum (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before _)

theorem expected_successfulSignerInput_subsetMatch_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hne : required.Nonempty) (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message
        (fun input source => if input = targetInput then 0 else (sourceSubsetMatch target source required : ENNReal)) result) ≤
      (Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) : Nat) / (Fintype.card FewTimeView : ENNReal) +
        cachedTargetSubsetMatch key.parameter before targetInput target required * digestReuseWeight q := by
  have hweight (input : HashInput) (source : FewTimeView) :
      (if input = targetInput then 0 else (sourceSubsetMatch target source required : ENNReal)) ≤
        (sourceSubsetMatch target source required : ENNReal) := by split_ifs; exact bot_le; exact le_rfl
  simpa only [expected_sourceSubsetMatch target required hne, cachedTargetSubsetMatch] using
    expected_successfulSignerInputWeight_le_allMessage key message before _ _ hweight q hq hcache

theorem cachedTargetSubsetMatch_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery input output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required +
        if FtsProbeSimulation.MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
          if input = targetInput then 0 else (sourceSubsetMatch target (hashOutputFewTimeView output) required : ENNReal) else 0 := by
  exact cacheMessageWeight_cacheQuery parameter _ before input output hfresh

theorem cachedTargetSubsetMatch_cacheQuery_self (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (output : HashOutput)
    (hfresh : before targetInput = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery targetInput output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required := by
  rw [cachedTargetSubsetMatch_cacheQuery parameter before targetInput target required targetInput output hfresh]
  simp only [if_true, ite_self, add_zero]

end SphincsSecurity.Concrete
