import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalProbeRouting

namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp HiddenLabelObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshResponse (parameter : PublicParameter) (actual : Labels)
    (replies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) : PMF HashOutput :=
  match decodePosition parameter input with
  | none => outside
  | some position =>
      if input = inputOf parameter actual position then PMF.pure (replies position)
      else PMF.uniformOfFintype HashOutput

theorem freshResponse_at (parameter : PublicParameter) (actual : Labels) (replies : CanonicalGraphLabels)
    (input : HashInput) (outside : PMF HashOutput) (position : Position) (hat : AtPosition parameter input position) :
    freshResponse parameter actual replies input outside =
      if input = inputOf parameter actual position then PMF.pure (replies position)
      else PMF.uniformOfFintype HashOutput := by
  simp only [freshResponse, (decodePosition_some_iff parameter input position).mpr hat]

noncomputable def stoppedResponse (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) : SPMF HashOutput := do
  let answer ← (liftM (freshResponse parameter actual replies input outside) : SPMF HashOutput)
  if ¬Bad parameter words disclosed actual input answer then pure answer else failure

theorem stoppedResponse_apply (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) (answer : HashOutput) :
    stoppedResponse parameter words disclosed actual replies input outside answer =
      if ¬Bad parameter words disclosed actual input answer then freshResponse parameter actual replies input outside answer else 0 := by
  rw [stoppedResponse, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : ¬Bad parameter words disclosed actual input answer <;>
      simp only [h, not_false_eq_true, if_true, if_false, SPMF.liftM_apply, SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : ¬Bad parameter words disclosed actual input other <;>
      simp only [h, not_false_eq_true, if_true, if_false, SPMF.liftM_apply, SPMF.pure_apply,
        if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]

noncomputable def routedResponse (outside : PMF HashOutput) (publicReplies : CanonicalGraphLabels)
    (actual : Labels) : Route → SPMF HashOutput
  | .outside => liftM outside
  | .canonical position => pure (publicReplies position)
  | .probe request => response actual request

theorem stoppedResponse_eq_routed (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (input : HashInput) (outside : PMF HashOutput) (routing : Route)
    (hspec : RouteSpec parameter words disclosed actual input routing) :
    stoppedResponse parameter words disclosed actual replies input outside =
      routedResponse outside publicReplies actual routing := by
  apply SPMF.ext
  intro answer
  rw [stoppedResponse_apply]
  simp only [← safe_iff_not_bad parameter words disclosed actual input routing hspec answer]
  cases routing with
  | outside =>
      have hdecode := (decodePosition_none_iff parameter input).mpr hspec
      simp only [Safe, if_true, freshResponse, hdecode, routedResponse, SPMF.liftM_apply]
  | canonical position =>
      obtain ⟨hat, hinput, hpublic⟩ := hspec
      have hreply := hreplies position (parent_public_of_no_hidden_child words disclosed position hpublic)
      rw [freshResponse_at parameter actual replies input outside position hat]
      simp only [Safe, if_true, if_pos hinput, routedResponse, hreply, PMF.pure_apply, SPMF.pure_apply]
      split_ifs <;> rfl
  | probe request =>
      rw [routedResponse, response_apply]
      cases request with
      | pair child parent hne candidate =>
          obtain ⟨position, hat, rfl, hslot, hhidden, hinput⟩ := hspec
          have heq : input = inputOf parameter actual position ↔ candidate = actual child := by
            rw [hinput, unary_eq_inputOf_iff parameter actual position child hslot candidate]
          rw [freshResponse_at parameter actual replies input outside position hat]
          by_cases hcanonical : input = inputOf parameter actual position
          · have hchild := heq.mp hcanonical
            simp only [Safe, Probe.keep, hchild, ne_eq, not_true_eq_false, false_and, if_false]
          · simp only [Safe, if_neg hcanonical]
      | output parent =>
          obtain ⟨position, hat, rfl, hinput⟩ := hspec
          rw [freshResponse_at parameter actual replies input outside position hat]
          simp only [Safe, if_neg hinput]

theorem stoppedResponse_route (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (input : HashInput) (outside : PMF HashOutput) :
    stoppedResponse parameter words disclosed actual replies input outside =
      routedResponse outside publicReplies actual (route parameter words disclosed known input) :=
  stoppedResponse_eq_routed parameter words disclosed actual replies publicReplies hreplies input outside _
    (route_spec parameter words disclosed known actual hagrees input)

end SphincsSecurity.Concrete.CanonicalProbeRouting
