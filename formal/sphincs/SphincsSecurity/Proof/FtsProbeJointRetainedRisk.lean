import SphincsSecurity.Proof.FtsProbeJointRoot
import SphincsSecurity.Proof.OtsProbeOuterCapFtsRisk

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

def flattenRetainedCache (result : Option RetainedGameResult × OtsProbeSimulation.SplitHashCache) :
    Option (RetainedGameResult × OtsProbeSimulation.SplitHashCache) :=
  result.1.map (fun value => (value, result.2))

theorem outerCappedRetainedComputation_eq_native
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    OtsProbeSimulation.outerCappedRetainedComputation adversary parameter ftsSecret q =
      flattenRetainedCache <$>
        (outerCappedNativeRetained adversary parameter ftsSecret q).run OtsProbeSimulation.emptySplitHashCache := by
  simp only [OtsProbeSimulation.outerCappedRetainedComputation, outerCappedNativeRetained,
    StateT.run_bind, simulateQ_map, StateT.run_map, map_bind, Functor.map_map]
  apply bind_congr
  intro root
  rw [bind_pure_comp]
  apply congrArg (fun f => f <$> _)
  funext result
  cases result with
  | mk value cache => cases value <;> rfl

def NativeRetainedFtsWitnessEvent
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : NativeStepResult (Option RetainedGameResult)) : Prop :=
  ∃ value, Option.map flattenRetainedCache (OtsProbeSimulation.historyPrefixValue result) = some (some value) ∧
    OtsProbeSimulation.UncoveredFtsValueWitness parameter (fun index tree leaf => table (index, tree, leaf)) value

theorem outerCappedErasedHistoryFtsWitnessRisk_eq_native
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    OtsProbeSimulation.outerCappedErasedHistoryFtsWitnessRisk adversary parameter
      (fun index tree leaf => table (index, tree, leaf)) q =
      Pr[NativeRetainedFtsWitnessEvent parameter table |
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries
            ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
              OtsProbeSimulation.emptySplitHashCache)) (OtsProbeSimulation.ensuredInitialContext ∅) 0 []] := by
  unfold OtsProbeSimulation.outerCappedErasedHistoryFtsWitnessRisk
  rw [outerCappedRetainedComputation_eq_native, OtsProbeSimulation.eraseProbeQueries_map,
    OtsProbeSimulation.runResolvedHistoryPrefix_map, probEvent_map]
  apply probEvent_congr' _ rfl
  intro result _
  cases result <;> rfl

noncomputable def jointRetainedDetailed
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :=
  AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
    ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
      OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)

theorem relTriple_jointRetainedDetailed
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    RelTriple (jointRetainedDetailed adversary parameter table q)
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
            OtsProbeSimulation.emptySplitHashCache)) (OtsProbeSimulation.ensuredInitialContext ∅) 0 [])
      (NativeStepCleanRel parameter table) := by
  have h := nativeStepRelAt_maskedJointRetained adversary parameter table q AdaptiveRevealProbe.State.empty
    (OtsProbeSimulation.ensuredInitialContext ∅) 0 [] OtsProbeSimulation.emptySplitHashCache emptySplitHashCache
    (by simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]) (revealedSynced_empty parameter table)
  have hcache : OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache ∅ =
      OtsProbeSimulation.emptySplitHashCache := by
    funext key
    cases key <;> rfl
  simpa only [NativeStepRelAt, jointRetainedDetailed, mergedCache_empty, hcache] using h

noncomputable def jointRetainedFtsWitnessRisk
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  Pr[fun result => result.hit = true ∨ NativeRetainedFtsWitnessEvent parameter table (projectNativeStepCache parameter table result) |
    jointRetainedDetailed adversary parameter table q]

theorem outerCappedErasedHistoryFtsWitnessRisk_le_joint
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    OtsProbeSimulation.outerCappedErasedHistoryFtsWitnessRisk adversary parameter
      (fun index tree leaf => table (index, tree, leaf)) q ≤ jointRetainedFtsWitnessRisk adversary parameter table q := by
  rw [outerCappedErasedHistoryFtsWitnessRisk_eq_native]
  apply probEvent_le_of_relTriple (relTriple_symm (relTriple_jointRetainedDetailed adversary parameter table q))
  intro native result hrelation hevent
  rcases hrelation with hhit | heq
  · exact Or.inl hhit
  · exact Or.inr (heq.symm ▸ hevent)

end SphincsSecurity.Concrete.FtsProbeSimulation
