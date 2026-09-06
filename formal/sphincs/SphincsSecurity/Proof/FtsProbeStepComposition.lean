import SphincsSecurity.Proof.FtsProbeHashStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev NativeFtsStep (α : Type) :=
  OtsProbeSimulation.DeferredContext → Nat → List OtsProbeSimulation.Probe →
    OtsProbeSimulation.SplitHashCache →
    StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) (NativeStepResult α)

noncomputable def bindNativeSteps (left : NativeFtsStep α) (next : α → NativeFtsStep β) : NativeFtsStep β :=
  fun context fuel history cache => do
    match ← left context fuel history cache with
    | none => pure none
    | some entry => next entry.value.1 entry.context entry.remaining entry.history entry.value.2

def NativeStepCoupledAt (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (masked : NativeFtsStep α)
    (native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) : Prop :=
  projectNativeStepCache parameter table <$>
    AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache) =
    OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries
        (native.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history

theorem nativeStepCoupledAt_bind
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (nativeLeft : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (nativeNext : α → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hfree : ProbeFree (left context fuel history cache))
    (hleft : NativeStepCoupledAt parameter table state ftsFuel left nativeLeft context fuel history cache ftsCache)
    (hnext : ∀ finalState entry finalCache,
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      NativeStepCoupledAt parameter table finalState ftsFuel (next entry.value.1) (nativeNext entry.value.1)
        entry.context entry.remaining entry.history entry.value.2 finalCache) :
    NativeStepCoupledAt parameter table state ftsFuel (bindNativeSteps left next)
      (nativeLeft >>= nativeNext) context fuel history cache ftsCache := by
  let resume : NativeStepResult α → ProbComp (NativeStepResult β)
    | none => pure none
    | some entry => OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries ((nativeNext entry.value.1).run entry.value.2))
        entry.context entry.remaining entry.history
  unfold NativeStepCoupledAt at hleft ⊢
  rw [bindNativeSteps, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ (hfree ftsCache), map_bind]
  refine (OracleComp.bind_congr_of_forall_mem_support
    (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache))
    (g := fun result => resume (projectNativeStepCache parameter table result)) ?_).trans ?_
  · intro result hresult
    obtain ⟨finalState, value, heq, hfinalClean⟩ :=
      AdaptiveRevealProbe.runDetailed_probeFree_support table state ftsFuel _ (hfree ftsCache) hclean result hresult
    subst result
    rcases value with ⟨entry, finalCache⟩
    cases entry with
    | none => simp [StateT.run_pure, AdaptiveRevealProbe.runDetailed, projectNativeStepCache, resume, hfinalClean]
    | some entry => exact hnext finalState entry finalCache hresult
  · rw [← bind_map_left, hleft, StateT.run_bind, OtsProbeSimulation.eraseProbeQueries_bind,
      OtsProbeSimulation.runResolvedHistoryPrefix_bind]
    apply bind_congr
    intro entry
    cases entry <;> rfl

theorem bindNativeSteps_probeFree
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache)
    (hleft : ProbeFree (left context fuel history cache))
    (hnext : ∀ value context fuel history cache, ProbeFree (next value context fuel history cache)) :
    ProbeFree (bindNativeSteps left next context fuel history cache) := by
  apply hleft.bind
  intro entry
  cases entry with
  | none => exact ProbeFree.pure _
  | some entry => exact hnext entry.value.1 entry.context entry.remaining entry.history entry.value.2

end SphincsSecurity.Concrete.FtsProbeSimulation
