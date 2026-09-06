import SphincsSecurity.Proof.FtsProbeStepRelation
import SphincsSecurity.Proof.FtsProbeJointSigningLog

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def NativeStepRelAt (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (masked : NativeFtsStep α)
    (native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) : Prop :=
  RelTriple
    (AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache))
    (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries
        (native.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))))
      context fuel history)
    (NativeStepCleanRel parameter table)

theorem nativeStepRelAt_bind_probeFree
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (nativeLeft : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (nativeNext : α → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hfree : ProbeFree (left context fuel history cache))
    (hleft : NativeStepRelAt parameter table state ftsFuel left nativeLeft context fuel history cache ftsCache)
    (hnext : ∀ finalState entry finalCache,
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      NativeStepRelAt parameter table finalState ftsFuel (next entry.value.1) (nativeNext entry.value.1)
        entry.context entry.remaining entry.history entry.value.2 finalCache) :
    NativeStepRelAt parameter table state ftsFuel (bindNativeSteps left next) (nativeLeft >>= nativeNext)
      context fuel history cache ftsCache := by
  apply relTriple_bindNativeSteps_of_resume parameter table state ftsFuel ftsFuel left next nativeLeft nativeNext
    context fuel history cache ftsCache ?_ hleft hnext
  rw [bindNativeSteps, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ (hfree ftsCache)]
  apply bind_congr
  intro result
  cases result with
  | stopped hit => rfl
  | done hit finalState value => rcases value with ⟨entry, finalCache⟩; cases entry <;> rfl

theorem nativeStepRelAt_hashQuery_bind
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (next : HashOutput → NativeFtsStep β)
    (nativeNext : HashOutput → StateT OtsProbeSimulation.SplitHashCache
      (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hnext : ∀ finalState entry finalCache,
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache)) →
      NativeStepRelAt parameter table finalState (jointHashRemaining parameter input remaining)
        (next entry.value.1) (nativeNext entry.value.1) entry.context entry.remaining entry.history entry.value.2 finalCache) :
    NativeStepRelAt parameter table state (remaining + 1) (bindNativeSteps (maskedJointHashQuery parameter input) next)
      (OtsProbeSimulation.probingHashQuery parameter input >>= nativeNext) context fuel history cache ftsCache := by
  apply relTriple_bindNativeSteps_of_resume parameter table state (remaining + 1) (jointHashRemaining parameter input remaining)
    (maskedJointHashQuery parameter input) next (OtsProbeSimulation.probingHashQuery parameter input) nativeNext
    context fuel history cache ftsCache ?_
    (relTriple_maskedJointHashQuery parameter table input state remaining context fuel history cache ftsCache hclean hsynced) hnext
  rw [bindNativeSteps, StateT.run_bind, runDetailed_maskedJointHashQuery_bind]
  apply bind_congr
  intro result
  cases result with
  | stopped hit => rfl
  | done hit finalState value => rcases value with ⟨entry, finalCache⟩; cases entry <;> rfl

theorem nativeStepRelAt_sign_bind
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (next : Option Signature → NativeFtsStep β)
    (nativeNext : Option Signature → StateT OtsProbeSimulation.SplitHashCache
      (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hnext : ∀ finalState entry finalCache,
      .done false finalState (some entry, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel
          ((maskedJointSign parameter root message context fuel history cache).run ftsCache)) →
      NativeStepRelAt parameter table finalState ftsFuel (next entry.value.1) (nativeNext entry.value.1)
        entry.context entry.remaining entry.history entry.value.2 finalCache) :
    NativeStepRelAt parameter table state ftsFuel (bindNativeSteps (maskedJointSign parameter root message) next)
      (OtsProbeSimulation.maskedPublishedChronologicalSign parameter root (fun index tree leaf => table (index, tree, leaf)) message >>= nativeNext)
      context fuel history cache ftsCache := by
  exact nativeStepRelAt_bind_probeFree parameter table state ftsFuel _ next _ nativeNext context fuel history cache ftsCache
    (maskedJointSign_probeFree parameter root message context fuel history cache)
    (coupled_maskedJointSign parameter root table message state ftsFuel context fuel history cache ftsCache hclean hsynced).relTriple hnext

end SphincsSecurity.Concrete.FtsProbeSimulation
