import SphincsSecurity.Proof.OtsProbeInitializedKnownRootCharge
import SphincsSecurity.Proof.OtsProbeLiveHashCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedRootHashQuerySelectionAfterTable
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel ordinal : Nat) : ProbComp (Option CanonicalQuerySelection) := do
  let result ← runResolvedFromTable (ensuredInitialContext targets) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match result with
  | none => pure none
  | some result =>
      liveNativeHashQuerySelection
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        ordinal result.context result.remaining table result.value.2

noncomputable def nativeChronologicalRootHashCut
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) : OracleComp (LazyRevealProbe.World Coordinate) (OuterQueryCut RetainedRestResult × SplitHashCache) := do
  let (root, cache) ← maskedPublishedTreeRoot.run emptySplitHashCache
  (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (outerHashQueryCutAt (retainedGameRestComputation adversary ⟨root, parameter⟩) ordinal)).run cache

theorem nativeChronologicalRootHashCut_probeBound
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) :
    (nativeChronologicalRootHashCut adversary parameter ftsSecret ordinal).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) ordinal := by
  unfold nativeChronologicalRootHashCut
  have htail : ∀ rootCache ∈ support (maskedPublishedTreeRoot.run emptySplitHashCache),
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter rootCache.1 ftsSecret)
        (outerHashQueryCutAt (retainedGameRestComputation adversary ⟨rootCache.1, parameter⟩) ordinal)).run rootCache.2).IsQueryBoundP
          (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) ordinal := by
    intro rootCache _
    exact (outerHashQueryCutAt_hashBound _ ordinal).simulateQ_run_StateT_of_step
      (maskedChronologicalExpandedAdversaryImpl_step_isProbeBound parameter rootCache.1 ftsSecret) rootCache.2
  simpa only [Nat.zero_add] using OracleComp.isQueryBoundP_bind
    (n := 0) (m := ordinal) (maskedPublishedTreeRoot_probeFree emptySplitHashCache) htail

theorem evalDist_initializedRootHashQuerySelection_eq_cut
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    evalDist (initializedRootHashQuerySelectionAfterTable targets adversary parameter table ftsSecret fuel ordinal) =
      evalDist (liveNativeHashCutSelection <$> runResolvedFromTable (ensuredInitialContext targets) fuel table
        (nativeChronologicalRootHashCut adversary parameter ftsSecret ordinal)) := by
  unfold initializedRootHashQuerySelectionAfterTable nativeChronologicalRootHashCut
  rw [runResolvedFromTable_bind, map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => simp [liveNativeHashCutSelection]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (maskedPublishedTreeRoot.run emptySplitHashCache)
        (ensuredInitialContext targets) fuel table result (ensuredInitialContext_valid targets).valuesConsistent
        (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hresult
      dsimp only
      rw [hcore.1]
      exact evalDist_liveNativeHashQuerySelection_eq_cut _ _ ordinal result.context result.remaining table
        result.value.2 hcore.2.1 hcore.2.2

theorem tsum_initializedRootHashQuerySelection_probability_eq_charge
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' ordinal, Pr[KnownHiddenEncodingRootSelection parameter |
      initializedRootHashQuerySelectionAfterTable targets adversary parameter table ftsSecret fuel ordinal]) * (4 / 3 : ENNReal) =
      initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel := by
  unfold initializedRootHashQuerySelectionAfterTable initializedKnownRootChargeAfterTable
  simp only [probEvent_bind_eq_tsum]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  rw [ENNReal.tsum_mul_left, mul_assoc]
  congr 1
  cases result with
  | none => simp [KnownHiddenEncodingRootSelection]
  | some result => exact tsum_knownEncodingRootHashSelection_probability_eq_charge parameter _ _ _ _ _ _

noncomputable def sampledInitializedRootHashQuerySelection
    (targets : Finset Position) (adversary : Adversary) (fuel ordinal : Nat) :
    ProbComp (PublicParameter × Option CanonicalQuerySelection) := do
  let parameter ← sampleParameter
  let table ← sampleOtsHashTable
  let ftsSecret ← sampleFtsSecrets
  let selection ← initializedRootHashQuerySelectionAfterTable targets adversary parameter table ftsSecret fuel ordinal
  pure (parameter, selection)

def SampledKnownHiddenEncodingRootSelection (result : PublicParameter × Option CanonicalQuerySelection) : Prop :=
  KnownHiddenEncodingRootSelection result.1 result.2

theorem probEvent_sampledInitializedRootHashQuerySelection_eq
    (targets : Finset Position) (adversary : Adversary) (fuel ordinal : Nat) :
    Pr[SampledKnownHiddenEncodingRootSelection | sampledInitializedRootHashQuerySelection targets adversary fuel ordinal] =
      ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' table, Pr[= table | sampleOtsHashTable] *
          ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
            Pr[KnownHiddenEncodingRootSelection parameter |
              initializedRootHashQuerySelectionAfterTable targets adversary parameter table ftsSecret fuel ordinal] := by
  simp only [sampledInitializedRootHashQuerySelection, probEvent_bind_eq_tsum, probEvent_pure,
    SampledKnownHiddenEncodingRootSelection]
  simp only [probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero]

theorem tsum_sampledInitializedRootHashQuerySelection_probability_eq_charge
    (targets : Finset Position) (adversary : Adversary) (fuel : Nat) :
    (∑' ordinal, Pr[SampledKnownHiddenEncodingRootSelection |
      sampledInitializedRootHashQuerySelection targets adversary fuel ordinal]) * (4 / 3 : ENNReal) =
      sampledInitializedKnownRootCharge targets adversary fuel := by
  simp only [probEvent_sampledInitializedRootHashQuerySelection_eq, sampledInitializedKnownRootCharge]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro parameter
  rw [ENNReal.tsum_mul_left, mul_assoc]
  congr 1
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro table
  rw [ENNReal.tsum_mul_left, mul_assoc]
  congr 1
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro ftsSecret
  rw [ENNReal.tsum_mul_left, mul_assoc, tsum_initializedRootHashQuerySelection_probability_eq_charge]

theorem sum_sampledInitializedRootHashQuerySelection_probability_le_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    (∑ ordinal ∈ Finset.range q, Pr[SampledKnownHiddenEncodingRootSelection |
      sampledInitializedRootHashQuerySelection targets adversary fuel ordinal]) * (4 / 3 : ENNReal) ≤
      sampledInitializedKnownRootCharge targets adversary fuel := by
  rw [← tsum_sampledInitializedRootHashQuerySelection_probability_eq_charge]
  exact mul_le_mul' (ENNReal.sum_le_tsum (Finset.range q)) le_rfl

theorem sampledInitializedNativeDirectRisk_add_rootSelectionBudget_le_refinedReserve
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q +
      (∑ ordinal ∈ Finset.range q, Pr[SampledKnownHiddenEncodingRootSelection |
        sampledInitializedRootHashQuerySelection targets adversary fuel ordinal]) * (4 / 3 : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add le_rfl (mul_le_mul'
    (sum_sampledInitializedRootHashQuerySelection_probability_le_charge targets adversary fuel q) le_rfl)).trans
  exact sampledInitializedNativeDirectRisk_add_knownRootCharge_le_refinedReserve targets adversary fuel q hq

end SphincsSecurity.Concrete.OtsProbeSimulation
