import SphincsSecurity.Proof.FewTimeOriginInvariant
import SphincsSecurity.Proof.FewTimeTargetSigner

/-!
# Monitoring one adaptive target candidate

This proof-only wrapper follows an origin monitor while retaining the view at one fixed ordinal in
the stream of fresh direct answers and fresh signer selections. Its signer uses
`signWithTargetView`, whose projection is the ordinary viewed signer.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem probEvent_randomOracle_fresh_view
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (P : FewTimeView → Prop) :
    Pr[fun result : HashOutput × QueryCache HashSpec => P (hashOutputFewTimeView result.1) |
      (randomOracle input).run cache] =
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache]
  change Pr[fun result : HashOutput × QueryCache HashSpec =>
      P (hashOutputFewTimeView result.1) |
    (fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [probEvent_map]
  calc
    Pr[fun output : HashOutput => P (hashOutputFewTimeView output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        Pr[P | hashOutputFewTimeView <$> ($ᵗ HashOutput : ProbComp HashOutput)] :=
      (probEvent_map (mx := ($ᵗ HashOutput : ProbComp HashOutput))
        (f := hashOutputFewTimeView) P).symm
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      evalDist_hashOutputFewTimeView_uniform

theorem tsum_probOutput_randomOracle_fresh_view_mul_le_expected
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (cost : HashOutput × QueryCache HashSpec → ℝ≥0∞)
    (risk : FewTimeView → ℝ≥0∞)
    (hon : ∀ source ∈ support ((randomOracle input).run cache),
      cost source ≤ risk (hashOutputFewTimeView source.1)) :
    (∑' source, Pr[= source | (randomOracle input).run cache] * cost source) ≤
      ∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
  let classify : HashOutput × QueryCache HashSpec → Option FewTimeView :=
    fun source => some (hashOutputFewTimeView source.1)
  have hbound := tsum_probOutput_mul_le_classifiedRisk
    ((randomOracle input).run cache) classify risk cost
    (by
      intro source _ hnone
      simp [classify] at hnone)
    (by
      intro source hsource view hview
      have : hashOutputFewTimeView source.1 = view := by
        simpa [classify] using hview
      rw [← this]
      exact hon source hsource)
  refine hbound.trans ?_
  apply Finset.sum_le_sum
  intro view _
  apply mul_le_mul' _ le_rfl
  exact le_of_eq (calc
    Pr[fun source => classify source = some view | (randomOracle input).run cache] =
        Pr[fun source : HashOutput × QueryCache HashSpec =>
          hashOutputFewTimeView source.1 = view | (randomOracle input).run cache] := by
      apply probEvent_congr'
      · intro source _
        simp only [classify, Option.some.injEq]
      · rfl
    _ = _ := probEvent_randomOracle_fresh_view input cache hcache
      (fun value => value = view))

theorem tsum_probOutput_signWithTargetView_fresh_mul_le_expected
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec)
    (cost : (TargetSignerResult × QueryCache HashSpec) → ℝ≥0∞)
    (risk : FewTimeView → ℝ≥0∞)
    (hoff : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache),
      freshTargetSignerView? initialCache signerResult = none → cost signerResult = 0)
    (hon : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache),
      ∀ view, freshTargetSignerView? initialCache signerResult = some view →
        cost signerResult ≤ risk view) :
    (∑' signerResult,
      Pr[= signerResult |
        (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache] *
          cost signerResult) ≤
      ∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
  have hbound := tsum_probOutput_mul_le_classifiedRisk
    ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache)
    (freshTargetSignerView? initialCache) risk cost hoff hon
  refine hbound.trans ?_
  apply Finset.sum_le_sum
  intro view _
  exact mul_le_mul'
    (probEvent_freshTargetSignerView?_eq_some_le_uniform secretKey message initialCache view)
    le_rfl

structure OriginTargetMonitorState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) where
  origin : OriginMonitorState configuration
  candidateOrdinal : Nat
  candidateViews : List FewTimeView
  candidateAllowed : List Bool
  targetView : Option FewTimeView
  valid : Bool

noncomputable def OriginTargetMonitorState.initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) : OriginTargetMonitorState configuration :=
  ⟨OriginMonitorState.initial configuration cache, 0, [], [], none, true⟩

def OriginTargetMonitorState.recordCandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView) : OriginTargetMonitorState configuration :=
  { state with
    candidateOrdinal := state.candidateOrdinal + 1
    candidateViews := state.candidateViews ++ [view]
    candidateAllowed := state.candidateAllowed ++ [allowed]
    targetView := if state.candidateOrdinal = targetOrdinal then some view else state.targetView
    valid := if state.candidateOrdinal = targetOrdinal then state.valid && allowed else state.valid }

def OriginTargetMonitorState.advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration) : OriginTargetMonitorState configuration :=
  { state with origin := origin }

noncomputable def OriginTargetMonitorState.potential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if state.valid then
    match state.targetView with
    | some target => state.origin.potential fun views => event (views, target)
    | none => ∑ target, Pr[fun value : FewTimeView => value = target |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          state.origin.potential (fun views => event (views, target))
  else 0

def OriginTargetMonitorState.TargetScheduleCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration) : Prop :=
  (state.targetView = none) ↔ state.candidateOrdinal ≤ targetOrdinal

def OriginTargetMonitorState.CandidateViewsCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration) : Prop :=
  state.candidateOrdinal = state.candidateViews.length ∧
    state.targetView = state.candidateViews[targetOrdinal]?

theorem OriginTargetMonitorState.candidateViewsCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec)
    (targetOrdinal : Nat) :
    (OriginTargetMonitorState.initial configuration cache).CandidateViewsCoherent
      targetOrdinal := by
  simp [OriginTargetMonitorState.CandidateViewsCoherent,
    OriginTargetMonitorState.initial]

theorem OriginTargetMonitorState.candidateViewsCoherent_advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration)
    (hcoherent : state.CandidateViewsCoherent targetOrdinal) :
    (state.advanceOrigin origin).CandidateViewsCoherent targetOrdinal := hcoherent

theorem OriginTargetMonitorState.candidateViewsCoherent_recordCandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (hcoherent : state.CandidateViewsCoherent targetOrdinal) :
    (state.recordCandidate targetOrdinal allowed view).CandidateViewsCoherent
      targetOrdinal := by
  rcases hcoherent with ⟨hcount, hview⟩
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · constructor
    · change state.candidateOrdinal + 1 = (state.candidateViews ++ [view]).length
      simpa only [List.length_append, List.length_singleton] using
        congrArg (fun value => value + 1) hcount
    · simp [OriginTargetMonitorState.recordCandidate, heq, ← hcount]
  · constructor
    · change state.candidateOrdinal + 1 = (state.candidateViews ++ [view]).length
      simpa only [List.length_append, List.length_singleton] using
        congrArg (fun value => value + 1) hcount
    · by_cases hlt : targetOrdinal < state.candidateViews.length
      · simp only [OriginTargetMonitorState.recordCandidate, heq, if_false]
        rw [hview, List.getElem?_append_left hlt]
      · have hgt : state.candidateViews.length < targetOrdinal := by
          omega
        simp only [OriginTargetMonitorState.recordCandidate, heq, if_false]
        change state.targetView = (state.candidateViews ++ [view])[targetOrdinal]?
        rw [hview, List.getElem?_append_right hgt.le]
        simp [hlt]
        omega

def OriginTargetMonitorState.CandidateAllowedCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration) : Prop :=
  state.candidateOrdinal = state.candidateAllowed.length ∧
    state.valid = state.candidateAllowed[targetOrdinal]?.getD true

theorem OriginTargetMonitorState.candidateAllowedCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec)
    (targetOrdinal : Nat) :
    (OriginTargetMonitorState.initial configuration cache).CandidateAllowedCoherent
      targetOrdinal := by
  simp [OriginTargetMonitorState.CandidateAllowedCoherent,
    OriginTargetMonitorState.initial]

theorem OriginTargetMonitorState.candidateAllowedCoherent_advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration)
    (hcoherent : state.CandidateAllowedCoherent targetOrdinal) :
    (state.advanceOrigin origin).CandidateAllowedCoherent targetOrdinal := hcoherent

theorem OriginTargetMonitorState.candidateAllowedCoherent_recordCandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (hcoherent : state.CandidateAllowedCoherent targetOrdinal) :
    (state.recordCandidate targetOrdinal allowed view).CandidateAllowedCoherent
      targetOrdinal := by
  rcases hcoherent with ⟨hcount, hvalid⟩
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · constructor
    · change state.candidateOrdinal + 1 = (state.candidateAllowed ++ [allowed]).length
      simpa only [List.length_append, List.length_singleton] using
        congrArg (fun value => value + 1) hcount
    · have hlookup : state.candidateAllowed[targetOrdinal]? = none := by
        rw [← heq, hcount]
        simp
      have hstateValid : state.valid = true := by
        rw [hvalid, hlookup]
        rfl
      simp [OriginTargetMonitorState.recordCandidate, heq, ← hcount, hstateValid]
  · constructor
    · change state.candidateOrdinal + 1 = (state.candidateAllowed ++ [allowed]).length
      simpa only [List.length_append, List.length_singleton] using
        congrArg (fun value => value + 1) hcount
    · by_cases hlt : targetOrdinal < state.candidateAllowed.length
      · simp only [OriginTargetMonitorState.recordCandidate, heq, if_false]
        rw [hvalid, List.getElem?_append_left hlt]
      · have hgt : state.candidateAllowed.length < targetOrdinal := by
          have hne : state.candidateAllowed.length ≠ targetOrdinal := by
            omega
          omega
        simp only [OriginTargetMonitorState.recordCandidate, heq, if_false]
        change state.valid = (state.candidateAllowed ++ [allowed])[targetOrdinal]?.getD true
        rw [hvalid, List.getElem?_append_right hgt.le]
        have hsub : targetOrdinal - state.candidateAllowed.length ≠ 0 :=
          Nat.sub_ne_zero_iff_lt.mpr hgt
        simp [hlt, hsub]

theorem OriginTargetMonitorState.targetScheduleCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec)
    (targetOrdinal : Nat) :
    (OriginTargetMonitorState.initial configuration cache).TargetScheduleCoherent
      targetOrdinal := by
  simp [OriginTargetMonitorState.TargetScheduleCoherent,
    OriginTargetMonitorState.initial]

theorem OriginTargetMonitorState.targetView_eq_none_of_candidateOrdinal_eq
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    {targetOrdinal : Nat} {state : OriginTargetMonitorState configuration}
    (hcoherent : state.TargetScheduleCoherent targetOrdinal)
    (heq : state.candidateOrdinal = targetOrdinal) : state.targetView = none := by
  exact hcoherent.mpr heq.le

theorem OriginTargetMonitorState.targetScheduleCoherent_advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.advanceOrigin origin).TargetScheduleCoherent targetOrdinal := hcoherent

theorem OriginTargetMonitorState.targetScheduleCoherent_recordCandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (hcoherent : state.TargetScheduleCoherent targetOrdinal) :
    (state.recordCandidate targetOrdinal allowed view).TargetScheduleCoherent
      targetOrdinal := by
  by_cases heq : state.candidateOrdinal = targetOrdinal
  · simp [OriginTargetMonitorState.TargetScheduleCoherent,
      OriginTargetMonitorState.recordCandidate, heq]
  · have hview : state.targetView = none ↔ state.candidateOrdinal ≤ targetOrdinal := hcoherent
    simp only [OriginTargetMonitorState.TargetScheduleCoherent,
      OriginTargetMonitorState.recordCandidate, heq, if_false]
    constructor
    · intro hnone
      have hle : state.candidateOrdinal ≤ targetOrdinal := hview.mp hnone
      exact Nat.add_one_le_iff.mpr (lt_of_le_of_ne hle heq)
    · intro hle
      apply hview.mpr
      exact (Nat.le_add_right state.candidateOrdinal 1).trans hle

theorem OriginTargetMonitorState.potential_eq_zero_of_invalid
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hinvalid : state.valid = false) : state.potential event = 0 := by
  simp [OriginTargetMonitorState.potential, hinvalid]

theorem OriginTargetMonitorState.potential_advanceOrigin
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (origin : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    (state.advanceOrigin origin).potential event =
      if state.valid then
        match state.targetView with
        | some target => origin.potential fun views => event (views, target)
        | none => ∑ target, Pr[fun value : FewTimeView => value = target |
            ($ᵗ FewTimeView : ProbComp FewTimeView)] *
              origin.potential (fun views => event (views, target))
      else 0 := by
  rfl

theorem OriginTargetMonitorState.potential_recordCandidate_of_ordinal_ne
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (allowed : Bool) (view : FewTimeView)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.recordCandidate targetOrdinal allowed view).potential event =
      state.potential event := by
  simp [OriginTargetMonitorState.recordCandidate, OriginTargetMonitorState.potential, hne]

theorem OriginTargetMonitorState.potential_recordCandidate_eq_of_allowed
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (view : FewTimeView)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (heq : state.candidateOrdinal = targetOrdinal) (hvalid : state.valid = true) :
    (state.recordCandidate targetOrdinal true view).potential event =
      state.origin.potential (fun views => event (views, view)) := by
  simp [OriginTargetMonitorState.recordCandidate, OriginTargetMonitorState.potential,
    heq, hvalid]

theorem OriginTargetMonitorState.potential_recordCandidate_eq_of_disallowed
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (view : FewTimeView)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (heq : state.candidateOrdinal = targetOrdinal) :
    (state.recordCandidate targetOrdinal false view).potential event = 0 := by
  simp [OriginTargetMonitorState.recordCandidate, OriginTargetMonitorState.potential, heq]

noncomputable def originTargetMonitoredAdversaryImpl
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (OriginTargetMonitorState configuration) ProbComp) := by
  intro input
  cases input with
  | inl worldInput =>
      exact fun state => do
        let (output, origin) ←
          ((originMonitoredAdversaryImpl configuration secretKey (.inl worldInput)).run
            state.origin)
        let advanced := state.advanceOrigin origin
        match worldInput with
        | .inl _ => pure (output, advanced)
        | .inr hashInput =>
            if state.origin.viewed.cache hashInput = none then
              pure (output, advanced.recordCandidate targetOrdinal
                (decide (configuration.sourceAt? state.origin.directOrdinal = none))
                (hashOutputFewTimeView output))
            else
              pure (output, advanced)
  | inr request =>
      exact fun state => do
        let (targetResult, finalCache) ←
          (simulateQ romImpl (signWithTargetView secretKey request)).run
            state.origin.viewed.cache
        let result := targetSignerResultView targetResult
        let trace := fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache result.1
          finalCache state.origin.viewed.trace
        let monitored := monitorSigner secretKey request state.origin (result, finalCache)
        let origin : OriginMonitorState configuration :=
          ⟨⟨finalCache, trace, state.origin.viewed.views ++ [result.2],
            state.origin.viewed.targetView⟩, monitored.1, state.origin.directOrdinal,
            state.origin.signerOrdinal + 1, monitored.2⟩
        let advanced := state.advanceOrigin origin
        match targetResult.2 with
        | none => pure (result.1, advanced)
        | some (input, view) =>
            if state.origin.viewed.cache input = none then
              pure (result.1, advanced.recordCandidate targetOrdinal
                (decide (pattern.selectedAt? state.origin.signerOrdinal = none)) view)
            else
              pure (result.1, advanced)

theorem originTargetMonitoredAdversaryImpl_query_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration) :
    (fun result => (result.1, result.2.origin)) <$>
        ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
          state) =
      (originMonitoredAdversaryImpl configuration secretKey input).run state.origin := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          apply bind_congr
          intro result
          rfl
      | inr hashInput =>
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp [OriginTargetMonitorState.advanceOrigin,
              OriginTargetMonitorState.recordCandidate, hfresh, Function.comp_def]
          · simp [OriginTargetMonitorState.advanceOrigin,
              hfresh, Function.comp_def]
  | inr request =>
      let updateOrigin := fun
          run : (Option Signature × Option FewTimeView) × QueryCache HashSpec =>
        let trace := fullAdversaryTraceUpdate (.inr request) state.origin.viewed.cache
          run.1.1 run.2 state.origin.viewed.trace
        let monitored := monitorSigner secretKey request state.origin run
        (⟨⟨run.2, trace, state.origin.viewed.views ++ [run.1.2],
            state.origin.viewed.targetView⟩, monitored.1, state.origin.directOrdinal,
            state.origin.signerOrdinal + 1, monitored.2⟩ : OriginMonitorState configuration)
      calc
        _ = (fun run => (run.1.1, updateOrigin run)) <$>
            ((fun run => (targetSignerResultView run.1, run.2)) <$>
              (simulateQ romImpl (signWithTargetView secretKey request)).run
                state.origin.viewed.cache) := by
          rw [originTargetMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc]
          apply bind_congr
          intro targetRun
          cases hselection : targetRun.1.2 with
          | none =>
              simp only [pure_bind]
              rfl
          | some selection =>
              rcases selection with ⟨input, view⟩
              by_cases hfresh : state.origin.viewed.cache input = none
              · simp only [hfresh, if_pos, pure_bind]
                rfl
              · simp only [hfresh]
                rfl
        _ = (fun run => (run.1.1, updateOrigin run)) <$>
            (simulateQ romImpl (signWithView secretKey request)).run
              state.origin.viewed.cache := by
          rw [simulateQ_signWithTargetView_projection_run]
        _ = _ := by
          rw [originMonitoredAdversaryImpl]
          simp only [StateT.run, map_eq_bind_pure_comp]
          rfl

theorem originTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration) :
    Prod.map id OriginTargetMonitorState.origin <$>
        (simulateQ (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState =
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (originMonitoredAdversaryImpl configuration secretKey)
    OriginTargetMonitorState.origin
  intro input state
  exact originTargetMonitoredAdversaryImpl_query_projection configuration secretKey
    targetOrdinal input state

theorem probEvent_originTargetMonitoredAdversaryImpl_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (event : α × OriginMonitorState configuration → Prop) :
    Pr[event |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] =
      Pr[fun result : α × OriginTargetMonitorState configuration =>
          event (result.1, result.2.origin) |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  rw [← originTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState, probEvent_map]
  rfl

theorem probEvent_originMonitored_le_originTargetMonitored
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (originEvent : α × OriginMonitorState configuration → Prop)
    (targetEvent : α × OriginTargetMonitorState configuration → Prop)
    (himp : ∀ result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState),
      originEvent (result.1, result.2.origin) → targetEvent result) :
    Pr[originEvent |
      (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState.origin] ≤
      Pr[targetEvent |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  classical
  rw [probEvent_originTargetMonitoredAdversaryImpl_projection configuration secretKey
    targetOrdinal computation initialState originEvent]
  exact probEvent_mono himp

end Concrete

end SphincsSecurity
