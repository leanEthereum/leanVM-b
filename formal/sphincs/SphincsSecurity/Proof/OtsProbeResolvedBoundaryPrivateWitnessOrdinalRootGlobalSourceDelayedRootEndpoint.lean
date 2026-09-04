import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedProbability
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwapAfterTable

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem probEvent_uniformRight_privateOrdinalSelection_le_delayedRootGuess
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (hroot : IsLayerRoot target) :
    Pr[fun result : Option PrivateOrdinalSelection × Digest =>
        privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1 | do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
        table ftsSecret fuel
      pure (selection, rightRoot)] ≤
      Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
          PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret fuel table
        pure (selection, rightRoot)] := by
  exact probEvent_bind_le_bind_of_forall_le
    (mx := ($ᵗ Digest : ProbComp Digest))
    (left := fun rightRoot =>
      (fun selection => (selection, rightRoot)) <$>
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel)
    (right := fun rightRoot =>
      (fun selection => (selection, rightRoot)) <$>
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table)
    (leftEvent := fun result : Option PrivateOrdinalSelection × Digest =>
      privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1)
    (rightEvent := fun result : Option PermissivePrivateOrdinalSelection × Digest =>
      PermissiveDelayedRootGuess target result.2 ordinal result.1)
    (fun rightRoot _hrightRoot => by
      rw [probEvent_map, probEvent_map]
      change Pr[privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal |
          granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
            fuel] ≤
        Pr[PermissiveDelayedRootGuess target rightRoot ordinal |
          delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
            ftsSecret fuel table]
      exact probEvent_privateOrdinalSelectionGoodForSomeOutput_le_delayedRootGuess ordinal
        adversary parameter table ftsSecret fuel target rightRoot hroot)

set_option maxRecDepth 100000 in
theorem probEvent_privateOrdinalSelectionGoodForSomeOutput_pair_le_delayedRootGuess
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (hroot : IsLayerRoot target) :
    Pr[fun result : Option PrivateOrdinalSelection × Digest =>
        privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1 | do
      let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
        table ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)] ≤
      Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
          PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
        let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret fuel table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)] := by
  let left := granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table
    ftsSecret fuel
  let right := delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
    ftsSecret fuel table
  let leftEvent := fun result : Option PrivateOrdinalSelection × Digest =>
    privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1
  let rightEvent := fun result : Option PermissivePrivateOrdinalSelection × Digest =>
    PermissiveDelayedRootGuess target result.2 ordinal result.1
  calc
    _ = Pr[leftEvent | do
          let rightRoot ← ($ᵗ Digest : ProbComp Digest)
          let selection ← left
          pure (selection, rightRoot)] := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact OracleComp.DeferredSampling.evalDist_bind_comm left
        ($ᵗ Digest : ProbComp Digest) (fun selection rightRoot => pure (selection, rightRoot))
    _ ≤ Pr[rightEvent | do
          let rightRoot ← ($ᵗ Digest : ProbComp Digest)
          let selection ← right
          pure (selection, rightRoot)] := by
      exact probEvent_uniformRight_privateOrdinalSelection_le_delayedRootGuess ordinal adversary
        parameter table ftsSecret fuel target hroot
    _ = _ := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact (OracleComp.DeferredSampling.evalDist_bind_comm right
        ($ᵗ Digest : ProbComp Digest)
        (fun selection rightRoot => pure (selection, rightRoot))).symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_delayedGoodComparison_le_common_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result : Option PrivateOrdinalSelection × Digest =>
          privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1 | do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)] :=
      probEvent_delayedGoodComparison_le_privateOrdinalSelection ordinal adversary parameter table
        ftsSecret fuel target
    _ ≤ Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
          PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
        let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret fuel table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)] :=
      probEvent_privateOrdinalSelectionGoodForSomeOutput_pair_le_delayedRootGuess ordinal
        adversary parameter table ftsSecret fuel target hroot
    _ ≤ _ := probEvent_delayedRootGuess_afterTable_le_common_mul ordinal adversary parameter
      ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
