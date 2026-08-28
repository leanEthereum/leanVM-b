import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveProbability

/-!
# Clean terminal lift for adaptive one-time probes

The canonical delayed failure is transported to the uniformly completed clean interpreter. The
clean endpoint itself is already the generic `q * 2^-128` lazy-probe bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedTreeRoot

noncomputable def chronologicalCleanRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedRestResult × SplitHashCache) :=
  (do
    let (forgery, log) ←
      simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩))
    let verified ← simulateQ (probingRomImpl parameter)
      (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
    pure ((forgery, log), verified)).run cache

noncomputable def chronologicalCleanRetainedRun
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedGameResult × SplitHashCache) := do
  let rootResult ← maskedPublishedTreeRoot.run emptySplitHashCache
  let restResult ← chronologicalCleanRetainedRest adversary parameter rootResult.1 ftsSecret
    rootResult.2
  pure ((rootResult.1, restResult.1), restResult.2)

set_option maxRecDepth 100000 in
theorem chronologicalCleanRetainedRun_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    chronologicalCleanRetainedRun adversary parameter ftsSecret =
      (maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
        emptySplitHashCache := by
  unfold chronologicalCleanRetainedRun chronologicalCleanRetainedRest
    maskedChronologicalRetainedGameAfterFtsSecrets
    maskedChronologicalRetainedPrefixAfterFtsSecrets
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

theorem maskedPublishedTreeRoot_probeFree : ProbeFree maskedPublishedTreeRoot := by
  intro cache
  rw [maskedPublishedTreeRoot_eq, StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (maskedTreeRoot_probeFree topLayer rootTree cache)
  intro rootResult _hroot
  rcases rootResult with ⟨root, nextCache⟩
  rw [StateT.run_bind]
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (publishCoordinate_probeFree (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
        nextCache)
    (fun _ _ => by simp)

set_option maxRecDepth 100000 in
theorem chronologicalCleanRetainedRun_isProbeBound
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    (chronologicalCleanRetainedRun adversary parameter ftsSecret).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  unfold chronologicalCleanRetainedRun
  have htail : ∀ rootResult ∈ support (maskedPublishedTreeRoot.run emptySplitHashCache),
      (do
        let restResult ← chronologicalCleanRetainedRest adversary parameter rootResult.1
          ftsSecret rootResult.2
        pure ((rootResult.1, restResult.1), restResult.2)).IsQueryBoundP
          (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
    intro rootResult _hroot
    rcases rootResult with ⟨root, cache⟩
    let rest := chronologicalCleanRetainedRest adversary parameter root ftsSecret cache
    change ((fun result : RetainedRestResult × SplitHashCache =>
      ((root, result.1), result.2)) <$> rest).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q
    rw [OracleComp.isQueryBoundP_map_iff]
    unfold rest chronologicalCleanRetainedRest
    exact maskedChronologicalRetainedGameRest_run_isProbeBound adversary parameter root ftsSecret q
      (hbound root) cache
  simpa only [Nat.zero_add] using OracleComp.isQueryBoundP_bind
    (n := 0) (m := q) (maskedPublishedTreeRoot_probeFree emptySplitHashCache) htail

theorem probEvent_sampledChronologicalCleanFinish_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (chronologicalCleanRetainedRun adversary parameter ftsSecret)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledRunThenFinalizeClean_empty_none_le
    (chronologicalCleanRetainedRun adversary parameter ftsSecret) q
      (chronologicalCleanRetainedRun_isProbeBound adversary parameter ftsSecret q hbound)

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_of_fixed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (bound : ℝ≥0∞)
    (hfixed : ∀ table : OtsSecretIndex → HashOutput,
      Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret
          (extendStartTable table)] ≤ bound) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound := by
  unfold sampledActualRetainedOtsHashTable
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  simpa [probEvent_map, Function.comp_def] using hfixed table

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedOtsSecrets_verifyProbe_le_of_fixed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (bound : ℝ≥0∞)
    (hfixed : ∀ table : OtsSecretIndex → HashOutput,
      Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret
          (extendStartTable table)] ≤ bound) :
    Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
        ftsSecret result.2 |
      sampledActualRetainedOtsSecrets adversary parameter ftsSecret] ≤ bound := by
  rw [← probEvent_sampledWinningRetainedVerifyProbe_eq_secrets adversary parameter ftsSecret]
  exact probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_of_fixed adversary parameter
    ftsSecret bound hfixed

noncomputable def sampledViewedOtsSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
      ((Digest × Forgery × Bool) × ViewedFullTraceState)) := do
  let otsSecret ← sampleOtsSecrets
  let result ← gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  pure (otsSecret, result)

theorem probEvent_cleanFresh_le_verifyProbeAfterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanFreshEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      Pr[WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret |
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret] := by
  let table := tableOfOtsSecret otsSecret
  calc
    _ ≤ Pr[WinningRetainedFreshLayerOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      simpa [table, tableOtsSecret_tableOfOtsSecret] using
        probEvent_cleanFresh_le_actualRetained adversary parameter table ftsSecret
    _ ≤ Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
      probEvent_winningRetainedFresh_le_verifyProbe adversary parameter table ftsSecret
    _ = _ := by
      rw [actualRetainedGameAfterTable_eq_afterOtsSecret]
      simp only [table, tableOtsSecret_tableOfOtsSecret]
      rfl

theorem probEvent_cleanBackward_le_verifyProbeAfterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanBackwardEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      Pr[WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret |
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret] := by
  let table := tableOfOtsSecret otsSecret
  calc
    _ ≤ Pr[WinningRetainedBackwardChainOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      simpa [table, tableOtsSecret_tableOfOtsSecret] using
        probEvent_cleanBackward_le_actualRetained adversary parameter table ftsSecret
    _ ≤ Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
      probEvent_winningRetainedBackward_le_verifyProbe adversary parameter table ftsSecret
    _ = _ := by
      rw [actualRetainedGameAfterTable_eq_afterOtsSecret]
      simp only [table, tableOtsSecret_tableOfOtsSecret]
      rfl

theorem probEvent_sampledViewedOtsSecrets_cleanFresh_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => cleanFreshEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] ≤
      Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  unfold sampledViewedOtsSecrets sampledActualRetainedOtsSecrets
  apply probEvent_bind_le_bind_of_forall_le
  intro otsSecret _hots
  simpa [probEvent_map, Function.comp_def] using
    probEvent_cleanFresh_le_verifyProbeAfterOtsSecret adversary parameter otsSecret ftsSecret

theorem probEvent_sampledViewedOtsSecrets_cleanBackward_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => cleanBackwardEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] ≤
      Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  unfold sampledViewedOtsSecrets sampledActualRetainedOtsSecrets
  apply probEvent_bind_le_bind_of_forall_le
  intro otsSecret _hots
  simpa [probEvent_map, Function.comp_def] using
    probEvent_cleanBackward_le_verifyProbeAfterOtsSecret adversary parameter otsSecret ftsSecret

noncomputable def sampledViewedGameFtsFirst (adversary : Adversary) :
    ProbComp SampledViewedResult := do
  let parameter ← sampleParameter
  let ftsSecret ← sampleFtsSecrets
  let result ← sampledViewedOtsSecrets adversary parameter ftsSecret
  pure ⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩

set_option maxRecDepth 100000 in
theorem evalDist_sampledViewedGame_eq_ftsFirst (adversary : Adversary) :
    𝒟[sampledViewedGame adversary] = 𝒟[sampledViewedGameFtsFirst adversary] := by
  unfold sampledViewedGame sampleSecrets sampledViewedGameFtsFirst sampledViewedOtsSecrets
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  exact OracleComp.DeferredSampling.evalDist_bind_comm sampleOtsSecrets sampleFtsSecrets
    (fun otsSecret ftsSecret => do
      let result ← gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
      pure (⟨⟨parameter, otsSecret, ftsSecret⟩, result⟩ : SampledViewedResult))

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledViewedGame_cleanFresh_le_of_fixed
    (adversary : Adversary) (bound : ℝ≥0∞)
    (hfixed : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
      ∀ table : OtsSecretIndex → HashOutput,
        Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
          actualRetainedGameAfterTable adversary parameter ftsSecret
            (extendStartTable table)] ≤ bound) :
    Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] ≤ bound := by
  have hrewrite :
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] =
        Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGameFtsFirst adversary] :=
    OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_sampledViewedGame_eq_ftsFirst adversary)
  rw [hrewrite]
  unfold sampledViewedGameFtsFirst
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret hfts
  calc
    _ = Pr[fun result => cleanFreshEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] := by
      change Pr[SampledViewedEvent cleanFreshEvent |
          (fun result =>
            (⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩ : SampledViewedResult)) <$>
            sampledViewedOtsSecrets adversary parameter ftsSecret] = _
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] :=
      probEvent_sampledViewedOtsSecrets_cleanFresh_le_verifyProbe adversary parameter ftsSecret
    _ ≤ bound :=
      probEvent_sampledActualRetainedOtsSecrets_verifyProbe_le_of_fixed adversary parameter
        ftsSecret bound (hfixed parameter hparameter ftsSecret hfts)

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledViewedGame_cleanBackward_le_of_fixed
    (adversary : Adversary) (bound : ℝ≥0∞)
    (hfixed : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
      ∀ table : OtsSecretIndex → HashOutput,
        Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
          actualRetainedGameAfterTable adversary parameter ftsSecret
            (extendStartTable table)] ≤ bound) :
    Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] ≤ bound := by
  have hrewrite :
      Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] =
        Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGameFtsFirst adversary] :=
    OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_sampledViewedGame_eq_ftsFirst adversary)
  rw [hrewrite]
  unfold sampledViewedGameFtsFirst
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret hfts
  calc
    _ = Pr[fun result => cleanBackwardEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] := by
      change Pr[SampledViewedEvent cleanBackwardEvent |
          (fun result =>
            (⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩ : SampledViewedResult)) <$>
            sampledViewedOtsSecrets adversary parameter ftsSecret] = _
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] :=
      probEvent_sampledViewedOtsSecrets_cleanBackward_le_verifyProbe adversary parameter ftsSecret
    _ ≤ bound :=
      probEvent_sampledActualRetainedOtsSecrets_verifyProbe_le_of_fixed adversary parameter
        ftsSecret bound (hfixed parameter hparameter ftsSecret hfts)

end SphincsSecurity.Concrete.OtsProbeSimulation
