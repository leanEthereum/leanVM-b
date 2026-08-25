import SphincsSecurity.Proof.FewTimeTargetMonitor

/-!
# One-step invariant for one adaptive few-time target

The joint potential lifts the origin supermartingale while a fixed candidate ordinal is pending,
then fixes the candidate's view when that ordinal is reached.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def OriginTargetMonitorState.afterDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput) : OriginTargetMonitorState configuration :=
  let advanced := state.advanceOrigin (state.origin.afterDirect input output)
  if state.origin.viewed.cache input = none then
    advanced.recordCandidate targetOrdinal
      (decide (configuration.sourceAt? state.origin.directOrdinal = none))
      (hashOutputFewTimeView output)
  else advanced

theorem OriginTargetMonitorState.targetScheduleCoherent_afterDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.afterDirect targetOrdinal input output).TargetScheduleCoherent
      targetOrdinal := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [OriginTargetMonitorState.afterDirect, hfresh, if_true]
    exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate targetOrdinal
      (state.advanceOrigin (state.origin.afterDirect input output)) _ _
      (state.targetScheduleCoherent_advanceOrigin targetOrdinal _ hcoherent)
  · simpa [OriginTargetMonitorState.afterDirect, hfresh] using
      state.targetScheduleCoherent_advanceOrigin targetOrdinal
        (state.origin.afterDirect input output) hcoherent

theorem OriginTargetMonitorState.potential_afterDirect_of_ordinal_ne
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterDirect targetOrdinal input output).potential event =
      (state.advanceOrigin (state.origin.afterDirect input output)).potential event := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [OriginTargetMonitorState.afterDirect, hfresh, if_true]
    exact OriginTargetMonitorState.potential_recordCandidate_of_ordinal_ne
      targetOrdinal _ _ _ event hne
  · simp [OriginTargetMonitorState.afterDirect, hfresh]

theorem OriginTargetMonitorState.expected_potential_advanceOrigin_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (mass : α → ℝ≥0∞) (nextOrigin : α → OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hnext : ∀ target,
      (∑' result, mass result *
        (nextOrigin result).potential (fun views => event (views, target))) ≤
      state.origin.potential (fun views => event (views, target))) :
    (∑' result, mass result *
      (state.advanceOrigin (nextOrigin result)).potential event) ≤
      state.potential event := by
  classical
  cases hvalid : state.valid with
  | false =>
      simp [OriginTargetMonitorState.potential,
        OriginTargetMonitorState.advanceOrigin, hvalid]
  | true =>
      cases htarget : state.targetView with
      | some target =>
          simpa [OriginTargetMonitorState.potential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget] using hnext target
      | none =>
          simp only [OriginTargetMonitorState.potential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget, if_true]
          calc
            (∑' result, mass result *
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    (nextOrigin result).potential (fun views => event (views, target))) =
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    ∑' result, mass result *
                      (nextOrigin result).potential
                        (fun views => event (views, target)) := by
              calc
                _ = ∑' result, ∑ target,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).potential
                          (fun views => event (views, target))) := by
                    apply tsum_congr
                    intro result
                    rw [Finset.mul_sum]
                _ = ∑ target, ∑' result,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).potential
                          (fun views => event (views, target))) := by
                    exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
                _ = _ := by
                    apply Finset.sum_congr rfl
                    intro target _
                    calc
                      _ = ∑' result,
                          Pr[fun value : FewTimeView => value = target |
                              ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                            (mass result *
                              (nextOrigin result).potential
                                (fun views => event (views, target))) := by
                            apply tsum_congr
                            intro result
                            ac_rfl
                      _ = _ := ENNReal.tsum_mul_left
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro target _
              exact mul_le_mul' le_rfl (hnext target)

theorem OriginTargetMonitorState.expected_potential_afterDirect_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result, Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
      (state.afterDirect targetOrdinal input result.1).potential event) ≤
      state.potential event := by
  classical
  by_cases hfresh : state.origin.viewed.cache input = none
  · by_cases heq : state.candidateOrdinal = targetOrdinal
    · cases hsource : configuration.sourceAt? state.origin.directOrdinal with
      | some selected =>
          have hzero : ∀ output,
              (state.afterDirect targetOrdinal input output).potential event = 0 := by
            intro output
            rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
            rw [show decide
              (configuration.sourceAt? state.origin.directOrdinal = none) = false by
                simp [hsource]]
            apply OriginTargetMonitorState.potential_recordCandidate_eq_of_disallowed
            simpa [OriginTargetMonitorState.advanceOrigin] using heq
          simp_rw [hzero]
          simp
      | none =>
          cases hvalid : state.valid with
          | false =>
              have hzero : ∀ output,
                  (state.afterDirect targetOrdinal input output).potential event = 0 := by
                intro output
                rw [OriginTargetMonitorState.afterDirect, if_pos hfresh]
                apply OriginTargetMonitorState.potential_eq_zero_of_invalid
                simp [OriginTargetMonitorState.recordCandidate,
                  OriginTargetMonitorState.advanceOrigin, heq, hvalid]
              simp_rw [hzero]
              simp [OriginTargetMonitorState.potential, hvalid]
          | true =>
              have htargetView : state.targetView = none :=
                state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
              calc
                (∑' result,
                    Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
                      (state.afterDirect targetOrdinal input result.1).potential event) ≤
                    ∑ target, Pr[fun value : FewTimeView => value = target |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        state.origin.potential (fun views => event (views, target)) := by
                  apply tsum_probOutput_randomOracle_fresh_view_mul_le_expected
                    input state.origin.viewed.cache hfresh
                  intro result _
                  simp [OriginTargetMonitorState.afterDirect, hfresh, hsource,
                    OriginTargetMonitorState.recordCandidate,
                    OriginTargetMonitorState.advanceOrigin,
                    OriginTargetMonitorState.potential, heq, hvalid,
                    state.origin.potential_afterDirect_of_sourceAt?_eq_none
                      input result.1 _ hsource]
                _ = state.potential event := by
                  simp [OriginTargetMonitorState.potential, hvalid, htargetView]
    · simp_rw [state.potential_afterDirect_of_ordinal_ne targetOrdinal input _ event heq]
      apply state.expected_potential_advanceOrigin_le
      intro target
      exact state.origin.expected_potential_afterDirect_le input
        (fun views => event (views, target)) horigin
  · simp_rw [OriginTargetMonitorState.afterDirect, hfresh, if_false]
    apply state.expected_potential_advanceOrigin_le
    intro target
    exact state.origin.expected_potential_afterDirect_le input
      (fun views => event (views, target)) horigin

end Concrete

end SphincsSecurity
