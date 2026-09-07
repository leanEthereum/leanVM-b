import SphincsSecurity.Proof.JointProbeOriginalExecution

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runDetailed_jointResolved_bind_probeFree
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : JointSource α) (next : α → JointSource β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hfree : (runJointResolved (left.run cache) context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe 0) :
    AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved ((left >>= next).run cache) context fuel otsTable) =
      AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable) >>=
        resumeJointResolved table ftsFuel next := by
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ hfree]
  apply bind_congr
  intro result
  cases result with
  | stopped hit => rfl
  | done hit finalState entry => cases entry <;> rfl

theorem runDetailed_jointSourceOuterQuery_bind
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → JointSource α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hhash : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel) :
    AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input >>= next).run cache) context fuel otsTable) =
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input).run cache) context fuel otsTable) >>=
        resumeJointResolved table (JointOriginal.remainingFtsFuel parameter input ftsFuel) next := by
  cases input with
  | inl world =>
      cases world with
      | inl n =>
          exact runDetailed_jointResolved_bind_probeFree table state ftsFuel _ next context fuel otsTable cache
            (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
      | inr input =>
          have hpositive := hhash trivial
          obtain ⟨remaining, rfl⟩ : ∃ remaining, ftsFuel = remaining + 1 := ⟨ftsFuel - 1, by omega⟩
          rw [StateT.run_bind, runJointResolved_bind]
          change AdaptiveRevealProbe.runDetailed table state (remaining + 1)
            (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable >>= _) = _
          rw [runDetailed_jointResolved_hashQuery_bind]
          apply bind_congr
          intro result
          cases result with
          | stopped hit => rfl
          | done hit finalState entry => cases entry <;> rfl
  | inr message =>
      exact runDetailed_jointResolved_bind_probeFree table state ftsFuel _ next context fuel otsTable cache
        (runJointResolved_probeBound _ 0 (jointSourceSign_probeFree parameter root message cache) context fuel otsTable)

namespace JointOriginal

def finalCache (cache : JointSourceCache) : JointSourceCache := (prepareNativeCache cache.2 cache.1, cache.2)

theorem step_shared_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (pair) (hpair : pair ∈ support (step exception parameter root otsTable ftsTable input (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    .done false finalFrame.state (some (⟨finalFrame.context, finalFrame.fuel, (pair.2.1.1, finalFrame.cache), otsTable⟩ :
      ResolvedRunResult ((OracleWorld + SigningSpec).Range input × JointSourceCache))) ∈
      support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)) ∧
      finalFrame.ftsFuel = remainingFtsFuel parameter input frame.ftsFuel := by
  by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
  · rw [step, dif_pos h, support_map] at hpair
    obtain ⟨raw, hraw, rfl⟩ := hpair
    have hs := queryCoupling_support exception parameter root otsTable ftsTable input frame cache hit h raw hraw
    cases hh : raw.2.2 with
    | true => simp [hh] at hframe
    | false =>
        simp only [hh, Bool.false_eq_true, if_false] at hframe
        have hfuel := resume_ftsFuel parameter otsTable input frame.ftsFuel raw.1 finalFrame hframe
        refine ⟨?_, hfuel⟩
        rcases raw with ⟨left, actual⟩
        cases left with
        | stopped hit => simp [resume] at hframe
        | done hit state entry =>
            cases hit with
            | true => simp [resume] at hframe
            | false =>
                cases entry with
                | none => simp [resume] at hframe
                | some entry =>
                    by_cases hc : OtsProbeSimulation.DeferredCompletable otsTable entry.context
                    · simp only [resume, if_pos hc, Option.some.injEq] at hframe
                      subst finalFrame
                      have hi := jointOriginalQuery_continuation_invariants parameter root otsTable ftsTable input
                        frame.state state frame.ftsFuel frame.context frame.fuel frame.cache entry actual.1
                        h.2.1.1 h.2.1.2.1 hs.2.1 hs.1 hc
                      convert hs.2.1 using 1
                      rw [← hi.1, ← hi.2.1]
                    · simp [resume, hc] at hframe
  · rw [step, dif_neg h, support_map] at hpair
    obtain ⟨result, _, rfl⟩ := hpair
    contradiction

theorem run_shared_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable computation (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    .done false finalFrame.state (some (⟨finalFrame.context, finalFrame.fuel, (pair.2.1.1, finalCache finalFrame.cache), otsTable⟩ :
      ResolvedRunResult (α × JointSourceCache))) ∈
      support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
        (runJointResolved ((jointSourceComputation parameter root computation).run frame.cache) frame.context frame.fuel otsTable)) := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit pair with
  | pure value =>
      simp only [run_pure, support_pure, Set.mem_singleton_iff] at hpair
      subst pair
      cases Option.some.inj hframe
      change _ ∈ support (AdaptiveRevealProbe.runDetailed ftsTable finalFrame.state finalFrame.ftsFuel
        (runJointResolved ((jointSourceNativeBlock (pure value)).run finalFrame.cache) finalFrame.context finalFrame.fuel otsTable))
      rw [runDetailed_jointSourceNativeBlock]
      simp only [StateT.run_pure, OtsProbeSimulation.runResolvedFromTable, construct_pure, map_pure,
        Option.map_some, packResolvedNativeBlock, withNativeOrdinaryCache_prepare, hvalid.1,
        support_pure, Set.mem_singleton_iff, finalCache]
  | query_bind input next ih =>
      rw [run_query_bind, mem_support_bind_iff] at hpair
      obtain ⟨head, hhead, htail⟩ := hpair
      cases hm : head.1 with
      | none =>
          rw [hm, run_none, support_map] at htail
          obtain ⟨result, _, rfl⟩ := htail
          contradiction
      | some middle =>
          have hmiddle := step_valid exception parameter root otsTable ftsTable input (some frame) cache hit head hhead middle hm
          have hnextBound := step_queryBound exception parameter root otsTable ftsTable input next frame cache hit hbound head hhead middle hm
          have hsharedHead := step_shared_support exception parameter root otsTable ftsTable input frame cache hit head hhead middle hm
          rw [hm] at htail
          have hsharedTail := ih head.2.1.1 middle head.2.1.2 head.2.2 hnextBound hmiddle.1 pair htail hframe
          rw [jointSourceComputation, construct_query_bind, runDetailed_jointSourceOuterQuery_bind]
          · rw [mem_support_bind_iff]
            refine ⟨.done false middle.state (some ⟨middle.context, middle.fuel, (head.2.1.1, middle.cache), otsTable⟩), hsharedHead.1, ?_⟩
            simpa only [resumeJointResolved, ← hsharedHead.2, jointSourceComputation] using hsharedTail
          · rw [isQueryBoundP_query_bind_iff] at hbound
            intro hhash
            exact hbound.1.elim (fun hnot => False.elim (hnot hhash)) id

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
