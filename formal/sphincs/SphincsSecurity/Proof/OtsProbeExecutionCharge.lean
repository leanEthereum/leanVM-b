import SphincsSecurity.Proof.OtsProbeStepCharge
import SphincsSecurity.Proof.LazyRevealProbeSimulationCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def otsHashInputCharge (parameter : PublicParameter) (input : HashInput) : ℝ≥0∞ :=
  by
    classical
    exact if ∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position then 1 else 0

noncomputable def otsOuterQueryCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → ℝ≥0∞
  | .inl (.inr input) => otsHashInputCharge parameter input
  | _ => 0

theorem otsHashInputCharge_le_queryReserve (secretKey : SecretKey)
    (actualCache : QueryCache HashSpec) (input : HashInput) :
    otsHashInputCharge secretKey.parameter input ≤ otsOpeningQueryReserve secretKey actualCache input := by
  classical
  unfold otsHashInputCharge
  split_ifs with hots
  · obtain ⟨position, hposition, hat⟩ := hots
    exact otsOpeningQueryReserve_ge_one_of_atOtsPosition secretKey actualCache input position hat hposition
  · exact bot_le

theorem probingHashQuery_expectedCharge_le_otsHashInputCharge (parameter : PublicParameter)
    (input : HashInput) (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((probingHashQuery parameter input).run cache) state fuel ≤
      otsHashInputCharge parameter input := by
  classical
  unfold otsHashInputCharge
  split_ifs with hots
  · simpa only [Nat.cast_one] using LazyRevealProbe.expectedProbeCharge_le_queryBound _ state fuel 1
      (probingHashQuery_run_isProbeBound parameter input cache)
  · rw [probingHashQuery_eq_split_of_not_atOtsPosition parameter input hots,
      LazyRevealProbe.expectedProbeCharge_eq_zero_of_probeFree _ state fuel (splitHashQuery_probeFree _ cache)]

theorem maskedExpandedAdversaryImpl_expectedCharge_le (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        state fuel ≤ otsOuterQueryCharge parameter input := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          change LazyRevealProbe.expectedProbeCharge ((splitUniformImpl n).run cache) state fuel ≤ 0
          rw [LazyRevealProbe.expectedProbeCharge_eq_zero_of_probeFree _ state fuel (splitUniformImpl_probeFree n cache)]
      | inr input => exact probingHashQuery_expectedCharge_le_otsHashInputCharge parameter input cache state fuel
  | inr message =>
      change LazyRevealProbe.expectedProbeCharge ((maskedSign parameter root ftsSecret message).run cache) state fuel ≤ 0
      rw [maskedSign_expectedProbeCharge_eq_zero]

noncomputable def expectedMaskedOtsQueryCount {α : Type} (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) : ℝ≥0∞ :=
  LazyRevealProbe.expectedSimulationCharge (maskedExpandedAdversaryImpl parameter root ftsSecret)
    (fun input _ _ _ => otsOuterQueryCharge parameter input) computation cache state fuel

theorem simulateQ_maskedExpanded_expectedCharge_le {α : Type} (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) state fuel ≤
      expectedMaskedOtsQueryCount parameter root ftsSecret computation cache state fuel :=
  LazyRevealProbe.expectedProbeCharge_simulateQ_le _ _
    (maskedExpandedAdversaryImpl_expectedCharge_le parameter root ftsSecret) computation cache state fuel

noncomputable def deferredOtsQueryCount (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' result, Pr[= result | LazyRevealProbe.runRaw LazyRevealProbe.State.empty fuel
      (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | .stopped _ => 0
    | .done state remaining value => expectedMaskedOtsQueryCount parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩) value.2 state remaining

theorem deferredOtsProbeCharge_le_queryCount (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    deferredOtsProbeCharge adversary parameter ftsSecret fuel ≤ deferredOtsQueryCount adversary parameter ftsSecret fuel := by
  unfold deferredOtsProbeCharge deferredCleanRetainedRun
  rw [LazyRevealProbe.expectedProbeCharge_bind_of_probeFree _ _ _ _
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache)]
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  cases result with
  | stopped hit => exact le_rfl
  | done state remaining value =>
      dsimp only [LazyRevealProbe.RawResult.continuationCharge]
      rw [LazyRevealProbe.expectedProbeCharge_bind_pure]
      unfold deferredCleanRetainedRest
      rw [← simulateQ_maskedExpanded_retainedGameRestComputation]
      exact simulateQ_maskedExpanded_expectedCharge_le parameter value.1 ftsSecret _ value.2 state remaining

theorem probEvent_sampledDeferredCleanFinish_none_le_queryCount
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (deferredCleanRetainedRun adversary parameter ftsSecret)] ≤
      deferredOtsQueryCount adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  (probEvent_sampledDeferredCleanFinish_none_le_expectedCharge adversary q hq parameter hparameter ftsSecret hfts).trans
    (mul_le_mul' (deferredOtsProbeCharge_le_queryCount adversary parameter ftsSecret q) le_rfl)

end SphincsSecurity.Concrete.OtsProbeSimulation
