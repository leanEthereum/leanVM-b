import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativePeekInput
import SphincsSecurity.Proof.OtsProbeNativeRootCache
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootAdaptive

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem rootEncodingNativeCouples_splitHashQuery_avoids
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (splitHashQuery (.ordinary input)) := by
  intro leftCache rightCache hcache context fuel table
  have hlookup := hcache.lookup_avoids input havoid
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := hlookup.symm.trans hleft
      simp only [hright, runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary input) = none := hlookup.symm.trans hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache.update_same_avoids input havoid leftOutput⟩

theorem rootEncodingNativeCouples_modifyOrdinary_avoids
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) (output : HashOutput) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (modify fun cache : SplitHashCache => Function.update cache (.ordinary input) (some output)) := by
  intro leftCache rightCache hcache context fuel table
  simp only [StateT.run_modify, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache.update_same_avoids input havoid output⟩

theorem rootEncodingNativeCouples_peekTableInput
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (peekTableInput parameter coordinate) := by
  intro leftCache rightCache hcache context fuel table
  rw [runResolvedFromTable_peekTableInput_eq_pure, runResolvedFromTable_peekTableInput_eq_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingNativeCouples_resolveKnownInput_avoids
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (coordinate : Coordinate) (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (rootEncodingNativeCouples_peekTableInput parameter target leftRoot rightRoot coordinate).bind
  intro known
  cases known with
  | none => exact rootEncodingNativeCouples_splitHashQuery_avoids parameter target leftRoot rightRoot input havoid
  | some known =>
      simp only
      by_cases hmatch : known = input
      · rw [if_pos hmatch]
        exact (rootEncodingNativeCouples_revealCoordinateOutput parameter target leftRoot rightRoot coordinate).bind fun output =>
          (rootEncodingNativeCouples_publishCoordinate parameter target leftRoot rightRoot coordinate).bind fun _ =>
            (rootEncodingNativeCouples_modifyOrdinary_avoids parameter target leftRoot rightRoot input havoid output).bind fun _ =>
              rootEncodingNativeCouples_pure parameter target leftRoot rightRoot output
      · rw [if_neg hmatch]
        exact rootEncodingNativeCouples_splitHashQuery_avoids parameter target leftRoot rightRoot input havoid

theorem rootEncodingNativeCouples_planProbingHashQuery
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest) (input : HashInput) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (planProbingHashQuery parameter input) := by
  intro leftCache rightCache hcache context fuel table
  rw [runResolved_planProbingHashQuery parameter input context.state context fuel table leftCache rfl,
    runResolved_planProbingHashQuery parameter input context.state context fuel table rightCache rfl]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingNativeCouples_probe
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest) (candidate : Probe) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (probe candidate) := by
  unfold probe
  exact rootEncodingNativeCouples_worldStep parameter target leftRoot rightRoot _ _ fun _ _ _ h => ⟨rfl, h⟩

theorem rootEncodingNativeCouples_executeCandidate
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest) (candidate : Option Probe) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (executeCandidate? candidate) := by
  cases candidate with
  | none => exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()
  | some candidate => exact rootEncodingNativeCouples_probe parameter target leftRoot rightRoot candidate

theorem rootEncodingNativeCouples_probingHashQueryAfterPlan_avoids
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) (plan : PlannedHashQuery) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  apply (rootEncodingNativeCouples_executeCandidate parameter target leftRoot rightRoot plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary => exact rootEncodingNativeCouples_splitHashQuery_avoids parameter target leftRoot rightRoot input havoid
  | resolve coordinate => exact rootEncodingNativeCouples_resolveKnownInput_avoids parameter target leftRoot rightRoot coordinate input havoid

theorem rootEncodingNativeCouples_probingHashQuery_avoids
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (probingHashQuery parameter input) := by
  rw [probingHashQuery_eq_plan_then_afterPlan]
  exact (rootEncodingNativeCouples_planProbingHashQuery parameter target leftRoot rightRoot input).bind
    (rootEncodingNativeCouples_probingHashQueryAfterPlan_avoids parameter target leftRoot rightRoot input havoid)

end SphincsSecurity.Concrete.OtsProbeSimulation
