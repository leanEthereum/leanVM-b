import SphincsSecurity.Proof.JointProbeResolvedCompletionRisk
import SphincsSecurity.Proof.OtsProbeOuterCapJointEvent

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ResolvedRetainedJointEvent (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : Option (ResolvedRunResult (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))) : Prop :=
  OtsProbeSimulation.retainCompletableResult result = none ∨
    ∃ value, OtsProbeSimulation.resolvedPrefixValue (OtsProbeSimulation.retainCompletableResult result) = some value ∧
      ∃ retained, flattenRetainedCache value = some retained ∧
        OtsProbeSimulation.UncoveredFtsValueWitness parameter (fun index tree leaf => table (index, tree, leaf)) retained

theorem probEvent_native_joint_eq_outerCapped_resolved
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest)
    (hfts : (fun index tree leaf => table (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun trace => trace.1 = none ∨ OtsProbeSimulation.NativeFtsTraceEvent parameter otsTable
        (fun index tree leaf => table (index, tree, leaf)) trace |
      OtsProbeSimulation.nativeRetainedParentTrace adversary parameter otsTable
        (fun index tree leaf => table (index, tree, leaf)) fuel] =
      Pr[ResolvedRetainedJointEvent parameter table |
        OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
          ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
            OtsProbeSimulation.emptySplitHashCache)] := by
  rw [OtsProbeSimulation.probEvent_native_joint_eq_outerCapped_live adversary q hq parameter hparameter otsTable _ hfts fuel,
    outerCappedRetainedComputation_eq_native, OtsProbeSimulation.runResolvedLiveValue_map, probEvent_map]
  have h := OtsProbeSimulation.probEvent_live_failure_or_value_eq_retained
    ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
      OtsProbeSimulation.emptySplitHashCache)
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
    (fun value => ∃ retained, flattenRetainedCache value = some retained ∧
      OtsProbeSimulation.UncoveredFtsValueWitness parameter (fun index tree leaf => table (index, tree, leaf)) retained)
    (OtsProbeSimulation.ensuredInitialContext_valid ∅).valuesConsistent
    (OtsProbeSimulation.startTableAgrees_of_deferredCompletable (OtsProbeSimulation.ensuredInitialContext_completable ∅ otsTable))
  apply Eq.trans _ h
  apply probEvent_congr' _ rfl
  intro result _
  cases result with
  | none => simp
  | some result =>
      rcases result with ⟨remaining, value⟩
      simp only [Function.comp_def, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq, false_or]
      constructor
      · rintro ⟨_, retained, ⟨_, hretained⟩, hwitness⟩
        exact ⟨remaining, value, ⟨rfl, rfl⟩, retained, hretained, hwitness⟩
      · rintro ⟨_, value', ⟨_, rfl⟩, retained, hretained, hwitness⟩
        exact ⟨remaining, retained, ⟨rfl, hretained⟩, hwitness⟩

theorem probEvent_native_joint_le_jointResolved
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest)
    (hfts : (fun index tree leaf => table (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun trace => trace.1 = none ∨ OtsProbeSimulation.NativeFtsTraceEvent parameter otsTable
        (fun index tree leaf => table (index, tree, leaf)) trace |
      OtsProbeSimulation.nativeRetainedParentTrace adversary parameter otsTable
        (fun index tree leaf => table (index, tree, leaf)) fuel] ≤
      Pr[fun result => ResolvedRetainedJointEvent parameter table (projectJointResolvedCache parameter table result) |
        jointResolvedRetainedDetailed adversary parameter otsTable table q fuel] := by
  rw [probEvent_native_joint_eq_outerCapped_resolved adversary q hq parameter hparameter otsTable table hfts fuel]
  apply probEvent_le_of_relTriple (relTriple_symm (relTriple_jointResolvedRetainedDetailed adversary parameter otsTable table q fuel))
  intro native joint hrel hevent
  rcases hrel with hhit | heq
  · have hnone := (projectJointResolvedCache_eq_none_iff parameter table joint).mpr
      (cleanJointResolved_eq_none_of_hit joint hhit)
    exact Or.inl (by rw [hnone]; rfl)
  · rwa [heq]

theorem probEvent_parentOtsOrFtsWitness_le_jointResolved
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest)
    (hfts : (fun index tree leaf => table (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[OtsProbeSimulation.ParentOtsOrFtsWitness parameter otsTable (fun index tree leaf => table (index, tree, leaf)) |
      OtsProbeSimulation.prehitRetainedQueryTrace adversary parameter otsTable (fun index tree leaf => table (index, tree, leaf))] ≤
      Pr[fun result => ResolvedRetainedJointEvent parameter table (projectJointResolvedCache parameter table result) |
        jointResolvedRetainedDetailed adversary parameter otsTable table q fuel] :=
  (OtsProbeSimulation.probEvent_parentOtsOrFtsWitness_le_native_joint adversary parameter otsTable _ fuel).trans
    (probEvent_native_joint_le_jointResolved adversary q hq parameter hparameter otsTable table hfts fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation
