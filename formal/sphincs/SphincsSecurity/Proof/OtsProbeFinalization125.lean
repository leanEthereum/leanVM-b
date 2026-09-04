import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassification

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

theorem relTriple_sampledMaterializedCleanUnguarded_fuelLE
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (hfuel : rightFuel ≤ leftFuel) :
    RelTriple
      (sampledMaterializedCleanUnguarded adversary parameter ftsSecret leftFuel)
      (sampledMaterializedCleanUnguarded adversary parameter ftsSecret rightFuel)
      CleanFinishFailureLE := by
  unfold sampledMaterializedCleanUnguarded
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  apply relTriple_bind
    (relTriple_materializedCleanRetainedRunFromTable_probeLE adversary parameter ftsSecret
      leftFuel rightFuel leftTable hfuel)
  intro leftResult rightResult hresult
  exact relTriple_finishCleanRunFromTable_probeLE leftResult rightResult hresult

theorem probEvent_sampledMaterializedCleanUnguarded_none_fuel_mono
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (hfuel : rightFuel ≤ leftFuel) :
    Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret leftFuel] ≤
      Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret rightFuel] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple
    (relTriple_sampledMaterializedCleanUnguarded_fuelLE adversary parameter ftsSecret
      leftFuel rightFuel hfuel)
  intro left right hrelation hleft
  exact hrelation hleft

theorem probEvent_sampledMaterializedCleanUnguarded_none_le_queryBound
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hbudget : q ≤ fuel) :
    Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledMaterializedCleanUnguarded_none_fuel_mono adversary parameter ftsSecret
    fuel q hbudget).trans
      (probEvent_sampledMaterializedCleanUnguarded_none_le adversary parameter ftsSecret q hbound)

theorem probEvent_sampledDiagnostic_final_none_le_queryBound
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hbudget : q ≤ fuel) :
    Pr[fun outcome => outcome.final = none |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledObservedMaterializedDiagnostic_final_none_eq]
  exact probEvent_sampledMaterializedCleanUnguarded_none_le_queryBound adversary parameter
    ftsSecret fuel q hbound hbudget

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
