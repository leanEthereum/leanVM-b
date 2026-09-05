import SphincsSecurity.Proof.FtsProbeSampling
import SphincsSecurity.Proof.AdaptiveRevealProbeCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

noncomputable def maskedFtsProbeCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat) : ℝ≥0∞ :=
  AdaptiveRevealProbe.expectedProbeCharge
    ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache)
    AdaptiveRevealProbe.State.empty q

theorem maskedFtsProbeCharge_le_q (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤ q :=
  AdaptiveRevealProbe.expectedProbeCharge_le_fuel _ _ _

set_option maxRecDepth 30000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedFts_uncovered_le_probeCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledActualRetainedFts adversary parameter otsSecret] ≤
      maskedFtsProbeCharge adversary parameter otsSecret q * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let maskedRun :=
    (maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache
  calc
    Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledActualRetainedFts adversary parameter otsSecret] ≤
      Pr[fun result : (Coordinate → Digest) ×
          AdaptiveRevealProbe.DetailedResult Coordinate
            (RetainedGameResult × SplitHashCache) => result.2.hit = true |
        AdaptiveRevealProbe.detailedExperiment AdaptiveRevealProbe.State.empty q
          maskedRun] := by
      unfold sampledActualRetainedFts AdaptiveRevealProbe.detailedExperiment
      apply probEvent_bind_le_bind_of_forall_le
      intro table _htable
      have hextend : AdaptiveRevealProbe.extendTable
          (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table =
          table := by
        funext coordinate
        simp [AdaptiveRevealProbe.extendTable, AdaptiveRevealProbe.State.empty]
      rw [hextend]
      have hfts := mem_support_sampleFtsSecrets
        (fun index tree leafIdx => table (index, tree, leafIdx))
      have hbound := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
      simpa [SampledRetainedUncoveredFtsSecretWitness,
        AdaptiveRevealProbe.extendTable, AdaptiveRevealProbe.State.empty,
        probEvent_map, Function.comp_def, maskedRun] using
        (probEvent_actualRetained_uncovered_le_detailed_hit adversary parameter
          otsSecret table q hbound)
    _ = Pr[fun hit : Bool => hit = true |
        AdaptiveRevealProbe.experiment AdaptiveRevealProbe.State.empty q maskedRun] := by
      rw [← AdaptiveRevealProbe.detailedExperiment_hit_eq_experiment]
      rw [probEvent_map]
      rfl
    _ ≤ maskedFtsProbeCharge adversary parameter otsSecret q * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      letI : Nonempty Coordinate :=
        ⟨(⟨0, by norm_num [totalHeight]⟩,
          ⟨0, by norm_num [ftsTrees]⟩,
          ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
      exact AdaptiveRevealProbe.experiment_empty_probability_le_expectedProbeCharge q maskedRun


theorem probEvent_sampledFtsViewedGame_uncovered_le_probeCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledFtsViewedUncoveredWitness parameter otsSecret |
        sampledFtsViewedGame adversary parameter otsSecret] ≤
      maskedFtsProbeCharge adversary parameter otsSecret q * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    Pr[SampledFtsViewedUncoveredWitness parameter otsSecret |
        sampledFtsViewedGame adversary parameter otsSecret] ≤
      Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledConcreteActualRetainedFts adversary parameter otsSecret] := by
      unfold sampledFtsViewedGame sampledConcreteActualRetainedFts
      apply probEvent_bind_le_bind_of_forall_le
      intro ftsSecret _hfts
      let table := curryFtsTableEquiv ftsSecret
      simpa [SampledFtsViewedUncoveredWitness,
        SampledRetainedUncoveredFtsSecretWitness, table, curryFtsTableEquiv,
        probEvent_map, Function.comp_def] using
        (probEvent_gameAfterSecretsWithViewTrace_uncovered_le_actualRetained
          adversary parameter otsSecret table)
    _ = Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledActualRetainedFts adversary parameter otsSecret] := by
      apply _root_.OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalDist_sampledConcreteActualRetainedFts_eq adversary parameter otsSecret
    _ ≤ maskedFtsProbeCharge adversary parameter otsSecret q * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      probEvent_sampledActualRetainedFts_uncovered_le_probeCharge adversary parameter hparameter
        otsSecret hots q hq


noncomputable def sampledMaskedFtsProbeCharge (adversary : Adversary) (q : Nat) : ℝ≥0∞ :=
  ∑' parameter : PublicParameter, Pr[= parameter | sampleParameter] *
    ∑' otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest,
      Pr[= otsSecret | sampleOtsSecrets] * maskedFtsProbeCharge adversary parameter otsSecret q

set_option maxRecDepth 30000 in
theorem probEvent_sampledViewedGame_cleanUncovered_le_probeCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
      sampledMaskedFtsProbeCharge adversary q * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [sampledViewedGame, sampleSecrets]
  simp only [bind_assoc, pure_bind]
  rw [probEvent_bind_eq_tsum, sampledMaskedFtsProbeCharge, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_assoc]
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro otsSecret
    rw [mul_assoc]
    by_cases hots : otsSecret ∈ support sampleOtsSecrets
    · apply mul_le_mul' le_rfl
      let pack : ((Index → FtsTree → FtsLeaf → Digest) ×
          ((Digest × Forgery × Bool) × ViewedFullTraceState)) → SampledViewedResult :=
        fun result => ⟨⟨parameter, otsSecret, result.1⟩, result.2⟩
      have hrun : (sampleFtsSecrets >>= fun ftsSecret =>
          gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret >>= fun result =>
            pure (⟨⟨parameter, otsSecret, ftsSecret⟩, result⟩ : SampledViewedResult)) =
          pack <$> sampledFtsViewedGame adversary parameter otsSecret := by
        simp [sampledFtsViewedGame, pack]
      rw [hrun, probEvent_map]
      apply le_trans (probEvent_mono fun result _hresult hevent => hevent.2)
      exact probEvent_sampledFtsViewedGame_uncovered_le_probeCharge adversary parameter hparameter
        otsSecret hots q hq
    · rw [probOutput_eq_zero_of_not_mem_support hots, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hparameter, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation
