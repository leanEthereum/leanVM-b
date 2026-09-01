import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceHidden

/-!
# Global root coupling boundary

This file states the target-neutral postcondition of the adaptive coupling. A successful observed
run must turn every source-side layer-root witness into a delayed source snapshot. The failure
alternative is therefore charged once, before any ordinal or position is selected.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def SnapshotObservedRootRel
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) : Prop :=
  observed = none ∨
    (WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput source) →
      WitnessFirstUsesSomeDelayedLayerRootSnapshot source)

theorem relTriple_graph_of_map_eq
    (left : ProbComp α) (right : ProbComp β) (project : α → β)
    (hproject : project <$> left = right) :
    RelTriple left right (fun leftOutput rightOutput =>
      project leftOutput = rightOutput) := by
  have hgraph : RelTriple left (project <$> left)
      (fun leftOutput rightOutput => project leftOutput = rightOutput) := by
    have hbase : RelTriple left left (fun leftOutput rightOutput =>
        project leftOutput = project rightOutput) := by
      apply relTriple_post_mono (relTriple_refl left)
      intro leftOutput rightOutput heq
      subst rightOutput
      rfl
    have hmapped : RelTriple (id <$> left) (project <$> left)
        (fun leftOutput rightOutput => project leftOutput = rightOutput) :=
      relTriple_map
        (R := fun leftOutput rightOutput => project leftOutput = rightOutput)
        (f := id) (g := project) hbase
    simpa using hmapped
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hproject) hgraph

theorem relTriple_sampledSnapshot_privateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel)
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
        ftsSecret fuel)
      (fun snapshot plan => erasePrivateWitnessSnapshotOutput snapshot = plan) := by
  exact relTriple_graph_of_map_eq _ _ erasePrivateWitnessSnapshotOutput
    (map_erase_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary
      parameter ftsSecret fuel)

theorem probEvent_root_le_observedFailure_add_delayed_of_relTriple
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (hrel : RelTriple source observed SnapshotObservedRootRel) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) | source] ≤
      Pr[= none | observed] +
        Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot | source] := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_le_failure_add_residual_of_relTriple source observed
    SnapshotObservedRootRel
    (fun output =>
      WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output))
    WitnessFirstUsesSomeDelayedLayerRootSnapshot (fun output => output = none) hrel
  intro sourceOutput observedOutput hrelation hroot hnotDelayed
  rcases hrelation with hfailure | hsuccess
  · exact hfailure
  · exact False.elim (hnotDelayed (hsuccess hroot))

theorem probEvent_root_map_erase_sampledSnapshot_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) |
      sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel] =
      Pr[WitnessFirstUsesSomeLayerRoot |
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
          ftsSecret fuel] := by
  calc
    _ = Pr[WitnessFirstUsesSomeLayerRoot |
        erasePrivateWitnessSnapshotOutput <$>
          sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
            ftsSecret fuel] := by
      rw [probEvent_map]
      exact OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) rfl
    _ = _ := OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (congrArg evalDist
        (map_erase_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary
          parameter ftsSecret fuel))

theorem probEvent_sampledPlan_root_le_observedFailure_add_delayed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (hrel : RelTriple
      (sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
        ftsSecret fuel)
      (sampledObservedRootAwareClean adversary parameter ftsSecret fuel)
      SnapshotObservedRootRel) :
    Pr[WitnessFirstUsesSomeLayerRoot |
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
          ftsSecret fuel] ≤
      Pr[= none | sampledObservedRootAwareClean adversary parameter ftsSecret fuel] +
        Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
          sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
            ftsSecret fuel] := by
  rw [← probEvent_root_map_erase_sampledSnapshot_eq adversary parameter ftsSecret fuel]
  exact probEvent_root_le_observedFailure_add_delayed_of_relTriple _ _ hrel

end SphincsSecurity.Concrete.OtsProbeSimulation
