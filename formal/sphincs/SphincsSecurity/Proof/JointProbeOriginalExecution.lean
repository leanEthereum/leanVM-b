import SphincsSecurity.Proof.JointProbeOriginalQueryCoupling

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def secretKey (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) : SecretKey :=
  ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
    fun index tree leaf => ftsTable (index, tree, leaf)⟩

structure Frame where
  state : AdaptiveRevealProbe.State Coordinate
  ftsFuel : Nat
  context : OtsProbeSimulation.DeferredContext
  fuel : Nat
  cache : JointSourceCache

def Frame.Valid (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (ftsTable : Coordinate → Digest) (frame : Frame) (actualCache : QueryCache HashSpec) : Prop :=
  AdaptiveRevealProbe.tableHits frame.state ftsTable = false ∧
    RevealedSynced parameter ftsTable frame.state frame.cache.2 ∧
    OtsProbeSimulation.ResolvedContextInvariant parameter otsTable frame.context
      (mergedCache parameter ftsTable frame.cache.2) actualCache ∧
    OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable frame.context actualCache ∧
    OtsProbeSimulation.PublishedValues frame.context.state

def Frame.Enabled (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (ftsTable : Coordinate → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Frame) (actualCache : QueryCache HashSpec) (hit : Bool) : Prop :=
  hit = false ∧ frame.Valid parameter otsTable ftsTable actualCache ∧
    (OtsProbeSimulation.IsOuterHash input → 0 < frame.ftsFuel)

noncomputable def queryCoupling
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (actualCache : QueryCache HashSpec) (hit : Bool)
    (h : frame.Enabled parameter otsTable ftsTable input actualCache hit) :=
  Classical.choose ((relTriple_iff_relWP).mp (relTriple_jointResolvedQuery_originalMonitor exception
    parameter root otsTable ftsTable input frame.state frame.ftsFuel frame.context frame.fuel frame.cache actualCache hit
    h.2.2 h.2.1.1 h.2.1.2.1 h.2.1.2.2.1 h.2.1.2.2.2.1 h.2.1.2.2.2.2))

theorem queryCoupling_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (actualCache : QueryCache HashSpec) (hit : Bool)
    (h : frame.Enabled parameter otsTable ftsTable input actualCache hit)
    (pair) (hpair : pair ∈ support (queryCoupling exception parameter root otsTable ftsTable input frame actualCache hit h).1) :
    JointOriginalRunRel parameter otsTable ftsTable pair.1 pair.2.1 ∧
      pair.1 ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)) ∧
      pair.2 ∈ support (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) actualCache hit) :=
  Classical.choose_spec ((relTriple_iff_relWP).mp (relTriple_jointResolvedQuery_originalMonitor exception
    parameter root otsTable ftsTable input frame.state frame.ftsFuel frame.context frame.fuel frame.cache actualCache hit
    h.2.2 h.2.1.1 h.2.1.2.1 h.2.1.2.2.1 h.2.1.2.2.2.1 h.2.1.2.2.2.2)) pair hpair

noncomputable def remainingFtsFuel (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (fuel : Nat) : Nat :=
  match input with
  | .inl (.inr input) => jointHashRemaining parameter input (fuel - 1)
  | _ => fuel

noncomputable def resume (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (ftsFuel : Nat) :
    AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult ((OracleWorld + SigningSpec).Range input × JointSourceCache))) → Option Frame
  | .done false state (some entry) =>
      if OtsProbeSimulation.DeferredCompletable otsTable entry.context then
        some ⟨state, remainingFtsFuel parameter input ftsFuel, entry.context, entry.remaining, entry.value.2⟩
      else none
  | _ => none

theorem resume_ftsFuel
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (ftsFuel : Nat) (left) (frame : Frame)
    (hresume : resume parameter otsTable input ftsFuel left = some frame) :
    frame.ftsFuel = remainingFtsFuel parameter input ftsFuel := by
  cases left with
  | stopped hit => simp [resume] at hresume
  | done hit state entry =>
      cases hit with
      | true => simp [resume] at hresume
      | false =>
          cases entry with
          | none => simp [resume] at hresume
          | some entry =>
              simp only [resume] at hresume
              split at hresume
              · cases Option.some.inj hresume
                rfl
              · contradiction

theorem remainingFtsFuel_ge
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) (ftsFuel : Nat) :
    ftsFuel - (if OtsProbeSimulation.IsOuterHash input then 1 else 0) ≤ remainingFtsFuel parameter input ftsFuel := by
  cases input with
  | inl world =>
      cases world with
      | inl n => simp [remainingFtsFuel, OtsProbeSimulation.IsOuterHash]
      | inr input => exact jointHashRemaining_ge parameter input (ftsFuel - 1)
  | inr message => simp [remainingFtsFuel, OtsProbeSimulation.IsOuterHash]

noncomputable def step
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (actualCache : QueryCache HashSpec) (hit : Bool) :
    SPMF (Option Frame × (((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool)) :=
  match frame with
  | none => (fun result => (none, result)) <$>
      evalDist (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) actualCache hit)
  | some frame =>
      if h : frame.Enabled parameter otsTable ftsTable input actualCache hit then
        (fun pair => (if pair.2.2 then none else resume parameter otsTable input frame.ftsFuel pair.1, pair.2)) <$>
          (queryCoupling exception parameter root otsTable ftsTable input frame actualCache hit h).1
      else (fun result => (none, result)) <$>
        evalDist (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) actualCache hit)

theorem resume_valid
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame finalFrame : Frame)
    (left) (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hclean : AdaptiveRevealProbe.tableHits frame.state ftsTable = false)
    (hsynced : RevealedSynced parameter ftsTable frame.state frame.cache.2)
    (hleft : left ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)))
    (hrel : JointOriginalRunRel parameter otsTable ftsTable left actual)
    (hresume : resume parameter otsTable input frame.ftsFuel left = some finalFrame) :
    finalFrame.Valid parameter otsTable ftsTable actual.2 := by
  cases left with
  | stopped hit => simp [resume] at hresume
  | done hit state entry =>
      cases hit with
      | true => simp [resume] at hresume
      | false =>
          cases entry with
          | none => simp [resume] at hresume
          | some entry =>
              by_cases hcomplete : OtsProbeSimulation.DeferredCompletable otsTable entry.context
              · simp only [resume, if_pos hcomplete, Option.some.injEq] at hresume
                subst finalFrame
                have hnext := jointOriginalQuery_continuation_invariants parameter root otsTable ftsTable input
                  frame.state state frame.ftsFuel frame.context frame.fuel frame.cache entry actual hclean hsynced hleft hrel hcomplete
                exact ⟨hnext.2.2.2.2.2.1, hnext.2.2.2.2.2.2, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2.1⟩
              · simp [resume, hcomplete] at hresume

theorem step_valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (actualCache : QueryCache HashSpec) (hit : Bool)
    (pair) (hpair : pair ∈ support (step exception parameter root otsTable ftsTable input frame actualCache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    finalFrame.Valid parameter otsTable ftsTable pair.2.1.2 ∧ pair.2.2 = false := by
  cases frame with
  | none =>
      rw [step, support_map] at hpair
      obtain ⟨result, _, rfl⟩ := hpair
      contradiction
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input actualCache hit
      · rw [step, dif_pos h, support_map] at hpair
        obtain ⟨raw, hraw, rfl⟩ := hpair
        have hsupport := queryCoupling_support exception parameter root otsTable ftsTable input frame actualCache hit h raw hraw
        cases hh : raw.2.2 with
        | true => simp [hh] at hframe
        | false =>
            simp only [hh, Bool.false_eq_true, if_false] at hframe
            exact ⟨resume_valid parameter root otsTable ftsTable input frame finalFrame raw.1 raw.2.1
              h.2.1.1 h.2.1.2.1 hsupport.2.1 hsupport.1 hframe, rfl⟩
      · rw [step, dif_neg h, support_map] at hpair
        obtain ⟨result, _, rfl⟩ := hpair
        contradiction

theorem step_original
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (actualCache : QueryCache HashSpec) (hit : Bool) :
    Prod.snd <$> step exception parameter root otsTable ftsTable input frame actualCache hit =
      evalDist (runExceptionMonitor exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) actualCache hit) := by
  cases frame with
  | none => simp [step, Functor.map_map]
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input actualCache hit
      · simp only [step, dif_pos h, Functor.map_map]
        exact (queryCoupling exception parameter root otsTable ftsTable input frame actualCache hit h).2.map_snd
      · simp [step, h, Functor.map_map]

theorem step_queryBound
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hbound : ((OracleSpec.query input : OracleComp (OracleWorld + SigningSpec) _) >>= next).IsQueryBoundP
      OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (pair) (hpair : pair ∈ support (step exception parameter root otsTable ftsTable input (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    (next pair.2.1.1).IsQueryBoundP OtsProbeSimulation.IsOuterHash finalFrame.ftsFuel := by
  rw [isQueryBoundP_query_bind_iff] at hbound
  by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
  · rw [step, dif_pos h, support_map] at hpair
    obtain ⟨raw, _, rfl⟩ := hpair
    cases hh : raw.2.2 with
    | true => simp [hh] at hframe
    | false =>
        simp only [hh, Bool.false_eq_true, if_false] at hframe
        rw [resume_ftsFuel parameter otsTable input frame.ftsFuel raw.1 finalFrame hframe]
        apply (hbound.2 raw.2.1.1).mono
        by_cases hhash : OtsProbeSimulation.IsOuterHash input <;>
          simpa only [hhash, if_true, if_false, Nat.sub_zero] using remainingFtsFuel_ge parameter input frame.ftsFuel
  · rw [step, dif_neg h, support_map] at hpair
    obtain ⟨result, _, rfl⟩ := hpair
    contradiction

noncomputable def run
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → SPMF (Option Frame × ((α × QueryCache HashSpec) × Bool)) :=
  OracleComp.construct (fun value frame cache hit => pure (frame, ((value, cache), hit)))
    (fun input _ next frame cache hit =>
      step exception parameter root otsTable ftsTable input frame cache hit >>= fun pair =>
        next pair.2.1.1 pair.1 pair.2.1.2 pair.2.2) computation

@[simp] theorem run_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    run exception parameter root otsTable ftsTable (pure value) frame cache hit = pure (frame, ((value, cache), hit)) := rfl

theorem run_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    run exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit =
      step exception parameter root otsTable ftsTable input frame cache hit >>= fun pair =>
        run exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2 := rfl

theorem run_original
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    Prod.snd <$> run exception parameter root otsTable ftsTable computation frame cache hit =
      evalDist (runExceptionMonitor exception (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit) := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind input next ih =>
      rw [run_query_bind, map_bind]
      simp_rw [ih]
      rw [simulateQ_bind, simulateQ_spec_query, runExceptionMonitor_bind, evalDist_bind]
      rw [← step_original exception parameter root otsTable ftsTable input frame cache hit, bind_map_left]

theorem run_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    run exception parameter root otsTable ftsTable (computation >>= next) frame cache hit =
      run exception parameter root otsTable ftsTable computation frame cache hit >>= fun pair =>
        run exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => simp
  | query_bind input continuation ih =>
      rw [bind_assoc, run_query_bind, run_query_bind, bind_assoc]
      exact bind_congr fun pair => ih pair.2.1.1 pair.1 pair.2.1.2 pair.2.2

theorem run_none
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (hit : Bool) :
    run exception parameter root otsTable ftsTable computation none cache hit =
      (fun result => (none, result)) <$> evalDist (runExceptionMonitor exception
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit) := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind input next ih =>
      rw [run_query_bind, step, bind_map_left]
      simp_rw [ih]
      rw [simulateQ_bind, simulateQ_spec_query, runExceptionMonitor_bind, evalDist_bind, map_bind]

theorem run_valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hvalid : ∀ live, frame = some live → live.Valid parameter otsTable ftsTable cache ∧ hit = false)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable computation frame cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    finalFrame.Valid parameter otsTable ftsTable pair.2.1.2 ∧ pair.2.2 = false := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit pair with
  | pure value =>
      simp only [run_pure, support_pure, Set.mem_singleton_iff] at hpair
      subst pair
      exact hvalid finalFrame hframe
  | query_bind input next ih =>
      rw [run_query_bind, mem_support_bind_iff] at hpair
      obtain ⟨head, hhead, htail⟩ := hpair
      exact ih head.2.1.1 head.1 head.2.1.2 head.2.2
        (fun live hlive => step_valid exception parameter root otsTable ftsTable input frame cache hit head hhead live hlive)
        pair htail hframe

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
