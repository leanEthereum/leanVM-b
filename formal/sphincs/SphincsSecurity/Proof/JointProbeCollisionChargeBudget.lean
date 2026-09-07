import SphincsSecurity.Proof.JointProbeCollisionInitialization
import SphincsSecurity.Proof.JointProbeMessageHashBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initializedBeforeFailureCharge_le_fullQueryCharge
    (charge : QueryCache HashSpec → HashInput → ENNReal) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) charge
        parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
          initial.1 initial.2.2 false initial.1.isNone) ≤ expectedQueryCharge charge (gameAfterSecrets adversary parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
      (fun index tree leaf => ftsTable (index, tree, leaf))) ∅ := by
  let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
  let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
  let restCost := fun initial : Digest × QueryCache HashSpec =>
    expectedQueryCharge charge
      (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
        (OtsProbeSimulation.retainedGameRestComputation adversary ⟨initial.1, parameter⟩)) initial.2
  have hm := tsum_probOutput_map_mul (initializeRoot parameter otsTable ftsTable q fuel) Prod.snd restCost
  rw [initializeRoot_original] at hm
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] * restCost initial.2 := by
      apply ENNReal.tsum_le_tsum
      intro initial
      apply mul_le_mul' le_rfl
      apply (expectedBeforeFailureCharge_le_preExceptionCharge _ _ _ _ _ _ _ _ _ _ _).trans
      rw [preCharge_retainedComputation_eq_uncapped _ _ adversary q hq parameter hparameter otsTable ftsTable hfts]
      exact expectedPreExceptionCharge_le_queryCharge _ _ _ _ _
    _ = ∑' initial, Pr[= initial | originalRoot parameter otsTable] * restCost initial := hm.symm
    _ ≤ expectedQueryCharge charge (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
      rw [gameAfterSecrets, expectedQueryCharge_bind]
      apply le_trans _ (le_add_left le_rfl)
      apply ENNReal.tsum_le_tsum
      intro initial
      apply mul_le_mul' le_rfl
      exact (OtsProbeSimulation.expectedQueryCharge_retained_eq_gameRest _ _ _ _ _).le

noncomputable def initializedBeforeFailureCollisionBaseCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
      (fun cache input => collisionParentStoppedEncodingBaseCharge (secretKey parameter default otsTable ftsTable) cache input +
        ftsParentQueryCharge (secretKey parameter default otsTable ftsTable) cache input)
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
        initial.1 initial.2.2 false initial.1.isNone

noncomputable def initializedBeforeFailureEncodingPairCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
      (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
        initial.1 initial.2.2 false initial.1.isNone

theorem initializedBeforeFailureCollisionCharge_eq_base_add_pairs
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel =
      initializedBeforeFailureCollisionBaseCharge adversary parameter otsTable ftsTable q fuel +
        initializedBeforeFailureEncodingPairCharge adversary parameter otsTable ftsTable q fuel := by
  have heq : collisionSigningStructuralCharge (secretKey parameter default otsTable ftsTable) = fun cache input =>
      (collisionParentStoppedEncodingBaseCharge (secretKey parameter default otsTable ftsTable) cache input +
        ftsParentQueryCharge (secretKey parameter default otsTable ftsTable) cache input) +
      encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable) cache input := by
    funext cache input
    simp only [collisionSigningStructuralCharge, collisionParentStoppedEncodingQueryCharge]
    exact add_right_comm _ _ _
  simp only [initializedBeforeFailureCollisionCharge, initializedBeforeFailureCollisionBaseCharge,
    initializedBeforeFailureEncodingPairCharge, heq, expectedBeforeFailureCharge_add, mul_add, ENNReal.tsum_add]

theorem initializedBeforeFailureEncodingPairCharge_scaled_le_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedBeforeFailureEncodingPairCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hbefore := initializedBeforeFailureCharge_le_fullQueryCharge
    (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable)) adversary q hq parameter hparameter otsTable ftsTable hfts fuel
  apply (mul_le_mul' hbefore le_rfl).trans
  apply expected_encodingPairIncrementCharge_scaled_le_127
  · exact isQueryBoundP_gameAfterSecrets adversary q hq hparameter (OtsProbeSimulation.mem_support_sampleOtsSecrets_all _) hfts
  · exact hqMax

theorem initializedBeforeFailureCollisionCharge_le_base_add_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      initializedBeforeFailureCollisionBaseCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [initializedBeforeFailureCollisionCharge_eq_base_add_pairs, add_mul]
  exact add_le_add le_rfl (initializedBeforeFailureEncodingPairCharge_scaled_le_127 adversary q hq hqMax parameter hparameter otsTable ftsTable hfts fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
