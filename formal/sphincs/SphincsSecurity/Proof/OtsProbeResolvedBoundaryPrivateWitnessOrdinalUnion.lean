import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalInterpreter

/-!
# Retained ordinal union

The retained normalized witness trace reduces to one fixed-ordinal estimate. Candidate coverage,
the source query bound, the finite union and projection to the existing granular private Boolean
are discharged here.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem probEvent_retainedPrivateWitness_le_of_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (hcovered : PendingCoveredBy candidates context)
    (hordinal : ∀ ordinal : Fin (candidates.length + q),
      Pr[fun output =>
          boundedPrivateWitnessOrdinal? (candidates.length + q) output = some ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun output => output.1.isSome = true |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      ((candidates.length + q : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_privateWitness_le_of_bounded_ordinals _ (candidates.length + q)
    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  · intro output houtput hwitness
    cases hvalue : output.1 with
    | none => simp [hvalue] at hwitness
    | some witness =>
        exact supported_retained_privateWitness_has_bounded_ordinal adversary parameter table
          ftsSecret context fuel value candidates q hbound hcovered output houtput witness hvalue
  · exact hordinal

theorem probEvent_isSome_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    Pr[fun output => output.1.isSome = true |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] =
      Pr[= true | granularDetailedRetainedRestPrivateObserve adversary parameter table ftsSecret
        context fuel value] := by
  calc
    _ = Pr[fun output => output.1 = true |
        erasePrivateWitnessPlanOutput <$>
          granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
            ftsSecret context fuel value candidates] := by
      rw [probEvent_map]
      exact OracleComp.probEvent_congr' (fun output _ => by
        simp [erasePrivateWitnessPlanOutput]) rfl
    _ = Pr[fun output => output.1 = true |
        granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
          ftsSecret context fuel value candidates] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
        (congrArg evalDist
          (map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary
            parameter table ftsSecret context fuel value candidates))
    _ = Pr[= true | Prod.fst <$>
        granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
          ftsSecret context fuel value candidates] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = _ := OracleComp.probOutput_congr rfl
      (evalDist_fst_granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter
        table ftsSecret context fuel value candidates)

theorem probEvent_granularDetailedRetainedRestPrivateObserve_le_of_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (hcovered : PendingCoveredBy candidates context)
    (hordinal : ∀ ordinal : Fin (candidates.length + q),
      Pr[fun output =>
          boundedPrivateWitnessOrdinal? (candidates.length + q) output = some ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[= true | granularDetailedRetainedRestPrivateObserve adversary parameter table ftsSecret
        context fuel value] ≤
      ((candidates.length + q : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_isSome_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve_eq
    adversary parameter table ftsSecret context fuel value candidates]
  exact probEvent_retainedPrivateWitness_le_of_ordinals adversary parameter table ftsSecret
    context fuel value candidates q hbound hcovered hordinal

end SphincsSecurity.Concrete.OtsProbeSimulation
