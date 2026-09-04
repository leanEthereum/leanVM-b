import SphincsSecurity.Proof.FewTimeTargetInvariant
import SphincsSecurity.Proof.FewTime125Count

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginTargetMonitorState.rawPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  (if state.targetView = none then ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ else 1) *
    state.potential event

noncomputable def OriginTargetMonitorState.afterRawDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput) : OriginTargetMonitorState configuration :=
  let advanced := state.advanceOrigin (state.origin.afterDirect input output)
  if state.origin.viewed.cache input = none then
    advanced.recordCandidate targetOrdinal
      (decide (configuration.sourceAt? state.origin.directOrdinal = none ∧
        signAttemptResultOfOutput output ≠ none))
      (hashOutputFewTimeView output)
  else advanced

theorem OriginTargetMonitorState.expected_rawPotential_advanceOrigin_le
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
      (state.advanceOrigin (nextOrigin result)).rawPotential event) ≤
      state.rawPotential event := by
  have hbound := state.expected_potential_advanceOrigin_le mass nextOrigin event hnext
  simp only [advanceOrigin] at hbound
  cases htarget : state.targetView with
  | none =>
      simp only [htarget] at hbound
      simp only [rawPotential, advanceOrigin, htarget, ↓reduceIte]
      simp_rw [mul_left_comm (mass _)]
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul_right hbound (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹)
  | some target =>
      simpa only [rawPotential, advanceOrigin, htarget, reduceCtorEq, ↓reduceIte, one_mul]
        using hbound

theorem OriginTargetMonitorState.rawPotential_afterRawDirect_of_ordinal_ne
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterRawDirect targetOrdinal input output).rawPotential event =
      (state.advanceOrigin (state.origin.afterDirect input output)).rawPotential event := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp [afterRawDirect, hfresh, rawPotential, potential, recordCandidate, advanceOrigin, hne]
  · simp [afterRawDirect, hfresh]

theorem OriginTargetMonitorState.expected_rawPotential_afterRawDirect_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result, Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
      (state.afterRawDirect targetOrdinal input result.1).rawPotential event) ≤
      state.rawPotential event := by
  classical
  by_cases hfresh : state.origin.viewed.cache input = none
  · by_cases heq : state.candidateOrdinal = targetOrdinal
    · cases hsource : configuration.sourceAt? state.origin.directOrdinal with
      | some selected =>
          have hzero : ∀ output,
              (state.afterRawDirect targetOrdinal input output).rawPotential event = 0 := by
            intro output
            simp [afterRawDirect, hfresh, hsource, rawPotential, potential,
              recordCandidate, advanceOrigin, heq]
          simp_rw [hzero]
          simp
      | none =>
          cases hvalid : state.valid with
          | false =>
              have hzero : ∀ output,
                  (state.afterRawDirect targetOrdinal input output).rawPotential event = 0 := by
                intro output
                simp [afterRawDirect, hfresh, hsource, rawPotential, potential,
                  recordCandidate, advanceOrigin, heq, hvalid]
              simp_rw [hzero]
              simp
          | true =>
              have htargetView : state.targetView = none :=
                state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
              calc
                _ ≤ ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
                    ∑ target, Pr[fun value : FewTimeView => value = target |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        state.origin.potential (fun views => event (views, target)) := by
                  apply tsum_probOutput_randomOracle_fresh_admissible_view_mul_le_expected
                    input state.origin.viewed.cache hfresh
                  · intro result _ hnone
                    simp [afterRawDirect, hfresh, hsource, rawPotential, potential,
                      recordCandidate, advanceOrigin, heq, hvalid, hnone]
                  · intro result _ hsome
                    simp [afterRawDirect, hfresh, hsource, rawPotential, potential,
                      recordCandidate, advanceOrigin, heq, hvalid, hsome,
                      state.origin.potential_afterDirect_of_sourceAt?_eq_none
                        input result.1 _ hsource]
                _ = state.rawPotential event := by
                  simp [rawPotential, potential, hvalid, htargetView]
    · simp_rw [state.rawPotential_afterRawDirect_of_ordinal_ne targetOrdinal input _ event heq]
      apply state.expected_rawPotential_advanceOrigin_le
      intro target
      exact state.origin.expected_potential_afterDirect_le input
        (fun views => event (views, target)) horigin
  · simp_rw [afterRawDirect, hfresh, if_false]
    apply state.expected_rawPotential_advanceOrigin_le
    intro target
    exact state.origin.expected_potential_afterDirect_le input
      (fun views => event (views, target)) horigin

theorem OriginTargetMonitorState.expected_rawPotential_afterSigner_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (secretKey : SecretKey) (request : SignRequest)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125)
    (hcache : QueryCache.enncard state.origin.viewed.cache ≤ q)
    (hcoherent : state.origin.ScheduleCoherent) :
    (∑' result, Pr[= result |
      (simulateQ romImpl (signWithView secretKey request)).run state.origin.viewed.cache] *
        (state.advanceOrigin (state.origin.afterSigner secretKey request result)).rawPotential event) ≤
      state.rawPotential event := by
  apply state.expected_rawPotential_advanceOrigin_le
  intro target
  exact state.origin.expected_potential_afterSigner_le secretKey request
    (fun views => event (views, target)) q hq hcache hcoherent

theorem OriginTargetMonitorState.targetScheduleCoherent_afterRawDirect
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.afterRawDirect targetOrdinal input output).TargetScheduleCoherent targetOrdinal := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp only [afterRawDirect, hfresh, if_true]
    exact OriginTargetMonitorState.targetScheduleCoherent_recordCandidate targetOrdinal
      (state.advanceOrigin (state.origin.afterDirect input output)) _ _
      (state.targetScheduleCoherent_advanceOrigin targetOrdinal _ hcoherent)
  · simpa [afterRawDirect, hfresh] using
      state.targetScheduleCoherent_advanceOrigin targetOrdinal
        (state.origin.afterDirect input output) hcoherent


end SphincsSecurity.Concrete
