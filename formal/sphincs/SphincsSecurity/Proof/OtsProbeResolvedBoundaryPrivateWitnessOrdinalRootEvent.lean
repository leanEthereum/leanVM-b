import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootProbeCoupling

/-!
# Root ordinal event

The sampled granular witness trace is split at its least matching candidate. This module packages
the exact layer-root event that remains to be coupled to the root-aware lazy comparison and keeps
the existing Boolean private-failure endpoint as its marginal.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def WitnessFirstUsesSomeLayerRoot (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ ordinal, WitnessFirstUsesLayerRootOrdinal ordinal output

def WitnessFirstUsesSomeNonLayerRoot (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ ordinal, WitnessFirstUsesNonLayerRootOrdinal ordinal output

theorem witnessFirstUsesSome_root_or_nonRoot
    {output : PrivateWitnessPlanOutput}
    (hcovered : PrivateWitnessCovered output)
    (hwitness : output.1.isSome = true) :
    WitnessFirstUsesSomeLayerRoot output ∨ WitnessFirstUsesSomeNonLayerRoot output := by
  cases hwitnessValue : output.1 with
  | none => simp [hwitnessValue] at hwitness
  | some witness =>
      have hhit := hcovered witness hwitnessValue
      obtain ⟨ordinal, hfirst, _hsource⟩ :=
        firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits witness output.2 hhit
      have huses : WitnessFirstUsesOrdinal ordinal.val output :=
        ⟨witness, ordinal, hwitnessValue, rfl, hfirst⟩
      exact (witnessFirstUsesOrdinal_iff_root_or_nonRoot.mp huses).imp
        (fun hroot => ⟨ordinal.val, hroot⟩)
        (fun hnonRoot => ⟨ordinal.val, hnonRoot⟩)

theorem probEvent_privateWitness_le_root_add_nonRoot
    (run : ProbComp PrivateWitnessPlanOutput)
    (hcovered : ∀ output ∈ support run, PrivateWitnessCovered output) :
    Pr[fun output => output.1.isSome = true | run] ≤
      Pr[WitnessFirstUsesSomeLayerRoot | run] +
        Pr[WitnessFirstUsesSomeNonLayerRoot | run] := by
  calc
    _ ≤ Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot output ∨ WitnessFirstUsesSomeNonLayerRoot output | run] := by
      apply probEvent_mono
      intro output houtput hwitness
      exact witnessFirstUsesSome_root_or_nonRoot (hcovered output houtput) hwitness
    _ ≤ _ := probEvent_or_le _ _ _

noncomputable def sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessPlanOutput := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter table ftsSecret fuel

theorem probEvent_isSome_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => output.1.isSome = true |
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
          ftsSecret fuel] =
      Pr[= true | sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
        ftsSecret fuel] := by
  unfold sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan
    sampledGranularAllDirectBoundaryDetailedRetainedPrivate
  rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro table
  congr 1
  calc
    Pr[fun output => output.1.isSome = true |
        granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter table ftsSecret
          fuel] =
      Pr[fun output => output.1 = true |
        erasePrivateWitnessPlanOutput <$>
          granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter table
            ftsSecret fuel] := by
        rw [probEvent_map]
        exact OracleComp.probEvent_congr' (fun output _ => by
          simp [erasePrivateWitnessPlanOutput]) rfl
    _ = Pr[fun output => output.1 = true |
        granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table ftsSecret
          fuel] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
        (congrArg evalDist
          (map_erase_granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter
            table ftsSecret fuel))
    _ = Pr[= true | Prod.fst <$>
        granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table ftsSecret
          fuel] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = _ := OracleComp.probOutput_congr rfl
      (evalDist_fst_granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table
        ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
