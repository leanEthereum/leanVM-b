import SphincsSecurity.Proof.JointProbeOriginalParentFailure
import SphincsSecurity.Proof.PreExceptionOuterCapCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem preStructural_add_probeCharge_le_preHash_add_outerHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit +
      probeCharge parameter otsTable ftsTable input frame cache hit ≤
      expectedPreExceptionCharge exception (fun _ _ => 1)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit +
        if hit then 0 else outerHashQueryCharge (fun _ _ => 1) input cache := by
  have houter : outerHashQueryCharge (fun _ _ => (1 : ENNReal)) input cache =
      if OtsProbeSimulation.IsOuterHash input then 1 else 0 := by
    cases input with
    | inl query => cases query <;> rfl
    | inr message => rfl
  rw [houter]
  have hbase := preStructural_add_jointProbe_le_preHash_add_outerHash exception
    (secretKey parameter root otsTable ftsTable) input cache hit
    (OtsProbeSimulation.ensuredInitialContext ∅) OtsProbeSimulation.emptySplitHashCache
    AdaptiveRevealProbe.State.empty emptySplitHashCache
  cases frame with
  | none =>
      rw [probeCharge, add_zero]
      exact le_self_add.trans hbase
  | some frame =>
      by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
      · rw [probeCharge, if_pos h]
        simpa only [h.1, Bool.false_eq_true, if_false, secretKey] using
          preStructural_add_jointProbe_le_preHash_add_outerHash exception (secretKey parameter root otsTable ftsTable)
            input cache hit frame.context frame.cache.1 frame.state frame.cache.2
      · rw [probeCharge, if_neg h, add_zero]
        exact le_self_add.trans hbase

theorem preStructural_add_expectedProbeCharge_le_preHash_add_preOuterHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit +
      expectedProbeCharge exception parameter root otsTable ftsTable computation frame cache hit ≤
      expectedPreExceptionCharge exception (fun _ _ => 1)
        (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache hit +
      expectedPreExceptionOuterCharge exception (secretKey parameter root otsTable ftsTable) (fun _ _ => 1) computation cache hit := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind,
        expectedProbeCharge_query_bind, expectedPreExceptionOuterCharge_query_bind]
      rw [← step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => expectedPreExceptionCharge exception (signingStructuralCharge key)
          (simulateQ (expandedAdversaryImpl key) (next result.1.1)) result.1.2 result.2)]
      rw [← step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => expectedPreExceptionCharge exception (fun _ _ => 1)
          (simulateQ (expandedAdversaryImpl key) (next result.1.1)) result.1.2 result.2)]
      rw [← step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => expectedPreExceptionOuterCharge exception key (fun _ _ => 1) (next result.1.1) result.1.2 result.2)]
      calc
        _ = (expectedPreExceptionCharge exception (signingStructuralCharge key) (expandedAdversaryImpl key input) cache hit +
              probeCharge parameter otsTable ftsTable input frame cache hit) +
            ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
              (expectedPreExceptionCharge exception (signingStructuralCharge key)
                (simulateQ (expandedAdversaryImpl key) (next pair.2.1.1)) pair.2.1.2 pair.2.2 +
                expectedProbeCharge exception parameter root otsTable ftsTable (next pair.2.1.1) pair.1 pair.2.1.2 pair.2.2) := by
                  simp_rw [mul_add, ENNReal.tsum_add]
                  ac_rfl
        _ ≤ (expectedPreExceptionCharge exception (fun _ _ => 1) (expandedAdversaryImpl key input) cache hit +
              if hit then 0 else outerHashQueryCharge (fun _ _ => 1) input cache) +
            ∑' pair, Pr[= pair | step exception parameter root otsTable ftsTable input frame cache hit] *
              (expectedPreExceptionCharge exception (fun _ _ => 1)
                (simulateQ (expandedAdversaryImpl key) (next pair.2.1.1)) pair.2.1.2 pair.2.2 +
                expectedPreExceptionOuterCharge exception key (fun _ _ => 1) (next pair.2.1.1) pair.2.1.2 pair.2.2) :=
          add_le_add (preStructural_add_probeCharge_le_preHash_add_outerHash exception parameter root otsTable ftsTable input frame cache hit)
            (ENNReal.tsum_le_tsum fun pair => mul_le_mul' le_rfl (ih pair.2.1.1 pair.1 pair.2.1.2 pair.2.2))
        _ = _ := by
          simp_rw [mul_add, ENNReal.tsum_add]
          ac_rfl

noncomputable def initializedProbeCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedProbeCharge exception parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false

theorem preStructural_add_initializedProbeCharge_le_restHash_add_outerHash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (∑' initial, Pr[= initial | originalRoot parameter otsTable] *
      expectedPreExceptionCharge exception (signingStructuralCharge (secretKey parameter initial.1 otsTable ftsTable))
        (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
          (retainedComputation adversary parameter initial.1 q)) initial.2 false) +
      initializedProbeCharge exception adversary parameter otsTable ftsTable q fuel ≤
    ∑' initial, Pr[= initial | originalRoot parameter otsTable] *
      (expectedPreExceptionCharge exception (fun _ _ => 1)
        (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
          (retainedComputation adversary parameter initial.1 q)) initial.2 false +
      expectedPreExceptionOuterCharge exception (secretKey parameter initial.1 otsTable ftsTable) (fun _ _ => 1)
        (retainedComputation adversary parameter initial.1 q) initial.2 false) := by
  have hm := initializeRoot_original parameter otsTable ftsTable q fuel
  change Prod.snd <$> initializeRoot parameter otsTable ftsTable q fuel = evalDist (originalRoot parameter otsTable) at hm
  change (∑' initial, Pr[= initial | evalDist (originalRoot parameter otsTable)] * _) + _ ≤
    ∑' initial, Pr[= initial | evalDist (originalRoot parameter otsTable)] * _
  rw [← hm, tsum_probOutput_map_mul, tsum_probOutput_map_mul, initializedProbeCharge, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add]
  exact mul_le_mul' le_rfl (preStructural_add_expectedProbeCharge_le_preHash_add_preOuterHash exception
    parameter initial.2.1 otsTable ftsTable _ initial.1 initial.2.2 false)

theorem preCharge_retainedComputation_eq_uncapped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets)
    (root : Digest) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
        (retainedComputation adversary parameter root q)) cache hit =
    expectedPreExceptionCharge exception charge
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
        (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩)) cache hit := by
  rw [retainedComputation, simulateQ_map, expectedPreExceptionCharge_map]
  change expectedPreExceptionCharge exception charge
    (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (OtsProbeSimulation.capOuterHashQueries (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩) q)) cache hit = _
  have hcap := OtsProbeSimulation.simulateQ_expandedRetained_capOuterHashQueries adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root
  change simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ =
    some <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ at hcap
  rw [hcap, expectedPreExceptionCharge_map]

theorem preOuterCharge_retainedComputation_eq_uncapped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets)
    (root : Digest) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception (secretKey parameter root otsTable ftsTable) charge
      (retainedComputation adversary parameter root q) cache hit =
    expectedPreExceptionOuterCharge exception (secretKey parameter root otsTable ftsTable) charge
      (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩) cache hit := by
  rw [retainedComputation, expectedPreExceptionOuterCharge_map]
  apply expectedPreExceptionOuterCharge_capOuterHashQueries
  exact OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root

theorem originalPreParentStructural_add_initializedProbeCharge_le_restBudget
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
    let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
    let exception := parentException parameter otsTable ftsTable
    expectedPreExceptionCharge exception (signingStructuralCharge (primitiveAccountingKey parameter otsSecret ftsSecret))
      (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ false +
      initializedProbeCharge exception adversary parameter otsTable ftsTable q fuel ≤
    ∑' initial, Pr[= initial | originalRoot parameter otsTable] *
      (expectedPreExceptionCharge exception (fun _ _ => 1)
        (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
          (OtsProbeSimulation.retainedGameRestComputation adversary ⟨initial.1, parameter⟩)) initial.2 false +
      expectedPreExceptionOuterCharge exception (secretKey parameter initial.1 otsTable ftsTable) (fun _ _ => 1)
        (OtsProbeSimulation.retainedGameRestComputation adversary ⟨initial.1, parameter⟩) initial.2 false) := by
  dsimp only
  have h := preStructural_add_initializedProbeCharge_le_restHash_add_outerHash
    (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel
  simp_rw [preCharge_retainedComputation_eq_uncapped _ _ adversary q hq parameter hparameter otsTable ftsTable hfts] at h
  simp_rw [preOuterCharge_retainedComputation_eq_uncapped _ _ adversary q hq parameter hparameter otsTable ftsTable hfts] at h
  change expectedPreExceptionCharge (CleanParentSettlement parameter _ _)
    (fun cache input => parentStoppedEncodingQueryCharge (primitiveAccountingKey parameter _ _) cache input +
      ftsParentQueryCharge (primitiveAccountingKey parameter _ _) cache input) _ ∅ false + _ ≤ _
  rw [preParentStructuralCharge_retained_eq_afterRoot]
  exact h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
