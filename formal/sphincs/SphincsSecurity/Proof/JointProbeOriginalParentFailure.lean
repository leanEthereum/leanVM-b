import SphincsSecurity.Proof.JointProbeOriginalRetainedFailure
import SphincsSecurity.Proof.RootStructuralCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem runExceptionMonitor_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (f : α → β) (cache : QueryCache HashSpec) (hit : Bool) :
    runExceptionMonitor exception (f <$> computation) cache hit =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$> runExceptionMonitor exception computation cache hit := by
  rw [map_eq_bind_pure_comp, runExceptionMonitor_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  rfl

namespace Concrete.FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def parentException (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) :=
  CleanParentSettlement parameter (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
    (fun index tree leaf => ftsTable (index, tree, leaf))

noncomputable def originalParentMonitor
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) :=
  runExceptionMonitor (parentException parameter otsTable ftsTable)
    (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
      (fun index tree leaf => ftsTable (index, tree, leaf))) ∅ false

theorem monitoredRetained_parent_eq
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) :
    monitoredRetained (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q =
      (fun result => ((some result.1.1, result.1.2), result.2)) <$> originalParentMonitor adversary parameter otsTable ftsTable := by
  let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
  let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
  have hroot := runExceptionMonitor_treeRoot_empty (primitiveAccountingKey parameter otsSecret ftsSecret) topLayer rootTree
  change runExceptionMonitor (parentException parameter otsTable ftsTable)
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) ∅ false =
    (fun result => (result, false)) <$> originalRoot parameter otsTable at hroot
  rw [monitoredRetained, originalParentMonitor, OtsProbeSimulation.retainedAfterSecretsComputation,
    runExceptionMonitor_bind, hroot, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨root, cache⟩
  dsimp only
  have hcap := OtsProbeSimulation.simulateQ_expandedRetained_capOuterHashQueries adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root
  change simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ =
    some <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ at hcap
  rw [retainedComputation, simulateQ_map]
  change runExceptionMonitor (parentException parameter otsTable ftsTable)
    ((Option.map (fun rest => (root, rest))) <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (OtsProbeSimulation.capOuterHashQueries (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩) q)) cache false = _
  rw [hcap]
  simp only [runExceptionMonitor_map, bind_pure_comp, Functor.map_map]
  rfl

theorem probEvent_original_parentClean_ftsWitness_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => result.2 = false ∧ RetainedUncoveredFtsSecretWitness parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable result.1 |
      originalParentMonitor adversary parameter otsTable ftsTable] ≤
      Pr[fun result => result.2 = true |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  have h := probEvent_original_clean_ftsWitness_le_sharedFailure (parentException parameter otsTable ftsTable) adversary q hq
    parameter hparameter otsTable hots ftsTable hfts fuel
  rw [monitoredRetained_parent_eq adversary q hq parameter hparameter otsTable ftsTable hfts, probEvent_map] at h
  simpa only [CleanFtsWitness, Function.comp_def, Option.some.injEq, exists_eq_left'] using h

end Concrete.FtsProbeSimulation.JointOriginal
end SphincsSecurity
