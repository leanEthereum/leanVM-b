import SphincsSecurity.Proof.FtsProbeJointQueryBind
import SphincsSecurity.Proof.AdaptiveRevealProbeDone

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def resumeJointStep (table : Coordinate → Digest) (fuel : Nat) (next : α → NativeFtsStep β) :
    AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult α × SplitHashCache) →
      ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult β × SplitHashCache))
  | .stopped hit => pure (.stopped hit)
  | .done _ state (none, cache) => AdaptiveRevealProbe.runDetailed table state fuel (pure (none, cache))
  | .done _ state (some entry, cache) => AdaptiveRevealProbe.runDetailed table state fuel
      ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run cache)

theorem relTriple_nativeStep_of_hit
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (left : ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult α × SplitHashCache)))
    (right : ProbComp (NativeStepResult α))
    (hhit : ∀ result ∈ support left, result.hit = true) :
    RelTriple left right (NativeStepCleanRel parameter table) := by
  exact relTriple_post_mono
    (relTriple_and_left_support (relTriple_true left right) (fun result => result.hit = true) hhit)
    (fun _ _ h => Or.inl h.2)

theorem relTriple_bindNativeSteps_of_resume
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel afterFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (nativeLeft : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (nativeNext : α → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hbind : AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((bindNativeSteps left next context fuel history cache).run ftsCache) =
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache) >>=
        resumeJointStep table afterFuel next))
    (hleft : RelTriple
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          (nativeLeft.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))))
        context fuel history)
      (NativeStepCleanRel parameter table))
    (hnext : ∀ finalState entry finalCache,
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      RelTriple
        (AdaptiveRevealProbe.runDetailed table finalState afterFuel
          ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run finalCache))
        (OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries
            ((nativeNext entry.value.1).run
              (OtsProbeSimulation.replaceOrdinaryCache entry.value.2 (mergedCache parameter table finalCache))))
          entry.context entry.remaining entry.history)
        (NativeStepCleanRel parameter table)) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((bindNativeSteps left next context fuel history cache).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((nativeLeft >>= nativeNext).run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))))
        context fuel history)
      (NativeStepCleanRel parameter table) := by
  rw [hbind, StateT.run_bind, OtsProbeSimulation.eraseProbeQueries_bind, OtsProbeSimulation.runResolvedHistoryPrefix_bind]
  apply relTriple_bind (relTriple_and_left_support hleft
    (fun result => result ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)))
    (fun _ h => h))
  intro detailed native hrelation
  obtain ⟨hrelation, hsupport⟩ := hrelation
  cases detailed with
  | stopped hit =>
      cases hit with
      | false =>
          have heq : none = native := hrelation.resolve_left (by simp [AdaptiveRevealProbe.DetailedResult.hit])
          subst native
          exact relTriple_pure_pure (Or.inr rfl)
      | true =>
          apply relTriple_nativeStep_of_hit
          intro result hresult
          simp only [resumeJointStep, mem_support_pure_iff] at hresult
          subst result
          rfl
  | done hit finalState value =>
      have hhit := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState ftsFuel
        ((left context fuel history cache).run ftsCache) hit value hsupport
      rcases value with ⟨entry, finalCache⟩
      cases hit with
      | true =>
          apply relTriple_nativeStep_of_hit
          cases entry with
          | none => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hhit
          | some entry => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hhit
      | false =>
          have heq := hrelation.resolve_left (by simp [AdaptiveRevealProbe.DetailedResult.hit])
          subst native
          cases entry with
          | none =>
              simp only [resumeJointStep, AdaptiveRevealProbe.runDetailed, construct_pure, hhit, projectNativeStepCache]
              exact relTriple_pure_pure (Or.inr rfl)
          | some entry => exact hnext finalState entry finalCache hsupport

end SphincsSecurity.Concrete.FtsProbeSimulation
