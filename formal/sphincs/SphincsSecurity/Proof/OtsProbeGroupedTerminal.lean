import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

/-!
# Grouped one-time terminal event

Fresh layer openings and backward chain openings both imply the same retained verifier probe.
Grouping them before the terminal union bound charges that probe event once.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def cleanOtsOpeningEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  cleanFreshEvent parameter otsSecret ftsSecret result ∨
    cleanBackwardEvent parameter otsSecret ftsSecret result

theorem probEvent_win_le_grouped_terminal_cases (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
      (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
        Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run])))) := by
  classical
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let opening := cleanOtsOpeningEvent parameter otsSecret ftsSecret
  let encoding := cleanEncodingEvent parameter otsSecret ftsSecret
  let message := cleanMessageEvent parameter otsSecret ftsSecret
  let proper := fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
  let uncovered := cleanUncoveredEvent parameter otsSecret ftsSecret
  calc
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] =
        Pr[fun result => result.1.2.2 = true | run] := by
      rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput,
        ← gameAfterSecretsWithViewTrace_verdictCache_projection adversary parameter otsSecret
          ftsSecret, probEvent_map]
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache ∨
          opening result ∨ encoding result ∨ message result ∨ proper result ∨
            uncovered result | run] := by
      apply probEvent_mono
      intro result hresult hwin
      rcases gameAfterSecretsWithViewTrace_winning_terminal_classify adversary parameter
          otsSecret ftsSecret result hresult hwin with hbad | hterminal
      · exact Or.inl hbad
      · by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
        · exact Or.inl hbad
        · rcases viewedWinningTerminalWitness_cases parameter otsSecret ftsSecret result
            hterminal with hfresh | hencoding | hbackward | hmessage | hproper | huncovered
          · exact Or.inr (Or.inl (Or.inl ⟨⟨hbad, hwin⟩, hfresh⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hbad, hencoding⟩))
          · exact Or.inr (Or.inl (Or.inr ⟨⟨hbad, hwin⟩, hbackward⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hmessage⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hproper⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbad, huncovered⟩))))
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        Pr[fun result => opening result ∨ encoding result ∨ message result ∨
          proper result ∨ uncovered result | run] := probEvent_or_le _ _ _
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        (Pr[opening | run] +
        (Pr[encoding | run] +
        (Pr[message | run] +
        (Pr[proper | run] + Pr[uncovered | run])))) := by
      gcongr
      calc
        _ ≤ Pr[opening | run] +
            Pr[fun result => encoding result ∨ message result ∨ proper result ∨
              uncovered result | run] := probEvent_or_le _ _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ Pr[encoding | run] +
                Pr[fun result => message result ∨ proper result ∨ uncovered result | run] :=
              probEvent_or_le _ _ _
            _ ≤ _ := by
              gcongr
              calc
                _ ≤ Pr[message | run] +
                    Pr[fun result => proper result ∨ uncovered result | run] :=
                  probEvent_or_le _ _ _
                _ ≤ _ := by
                  gcongr
                  exact probEvent_or_le _ _ _
    _ = _ := by
      rfl

theorem probEvent_win_le_grouped_reserved_add_remaining
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
      (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
        Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run]))) := by
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  have hqMin := numChains_le_of_hasHashQueryBound adversary q hq parameter hparameter otsSecret
    hots ftsSecret hfts
  have hbad := probEvent_bad_gameAfterSecretsWithViewTrace_le adversary parameter otsSecret
    ftsSecret q hgameBound
  have hproper := probEvent_clean_properFewTimeLeak_le_nine_mul_inv adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts
  calc
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
            ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
          Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run])))) :=
      probEvent_win_le_grouped_terminal_cases adversary parameter otsSecret ftsSecret
    _ ≤ (((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) +
        (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
        (((2 * q + 1 : Nat) : ℝ≥0∞) * (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹) +
          Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run])))) := by
      gcongr
    _ = ((((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) +
          ((2 * q + 1 : Nat) : ℝ≥0∞) * (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹)) +
        (Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanEncodingEvent parameter otsSecret ftsSecret | run] +
        (Pr[cleanMessageEvent parameter otsSecret ftsSecret | run] +
          Pr[cleanUncoveredEvent parameter otsSecret ftsSecret | run]))) := by
      ac_rfl
    _ ≤ _ := by
      gcongr
      exact structural_add_properFewTime_le hqMin

noncomputable def groupedRemainingRisk (adversary : Adversary)
    (secrets : SampledSecrets) : ℝ≥0∞ :=
  let run := gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
    secrets.ftsSecret
  Pr[cleanOtsOpeningEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanEncodingEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
      Pr[cleanUncoveredEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run]))

theorem weighted_groupedRemainingRisk_eq (adversary : Adversary) :
    (∑' secrets : SampledSecrets,
      Pr[= secrets | sampleSecrets] * groupedRemainingRisk adversary secrets) =
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary])) := by
  simp only [groupedRemainingRisk, mul_add, ENNReal.tsum_add]
  rw [← probEvent_sampledViewedGame_eq_weighted adversary cleanOtsOpeningEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanEncodingEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanMessageEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanUncoveredEvent]

theorem forgeAdvantage_le_grouped_reserved_add_sampled_remaining
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120) :
    forgeAdvantage scheme adversary ≤
      ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame]
  calc
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        ∑' secrets : SampledSecrets,
          Pr[= secrets | sampleSecrets] * groupedRemainingRisk adversary secrets := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_const_add_weighted
        (oa := sampleSecrets)
        (run := fun secrets => (simulateQ romImpl
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret)).run' ∅)
        (event := fun verdict => verdict = true)
        (cost := ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹)
        (groupedRemainingRisk adversary)
      intro secrets hsecrets
      obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
      rw [probEvent_eq_eq_probOutput]
      exact probEvent_win_le_grouped_reserved_add_remaining adversary q hq hqMax
        secrets.parameter hparameter secrets.otsSecret hots secrets.ftsSecret hfts
    _ = _ := by rw [weighted_groupedRemainingRisk_eq]

theorem forgeAdvantage_le_of_sampled_grouped_remaining_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (hremaining :
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary])) ≤
      ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    forgeAdvantage scheme adversary ≤ q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
  calc
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        (Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) :=
      forgeAdvantage_le_grouped_reserved_add_sampled_remaining adversary q hq hqMax
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add_right hremaining _
    _ = (q : ℝ≥0∞) *
        (((24 : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
          ((64 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
      push_cast
      ring
    _ = (q : ℝ≥0∞) * ((2 ^ securityBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [show securityBits = 120 by rfl, terminal_budget_remainder]
    _ = q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
      rw [div_eq_mul_inv]

namespace OtsProbeSimulation

def WinningRetainedOtsOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        (SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature ∨
          SettledForgedBackwardChainOpening f cache secretKey log index leaves forgery.signature)

theorem probEvent_cleanOtsOpening_le_actualRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanOtsOpeningEvent parameter (tableOtsSecret table) ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] ≤
      Pr[WinningRetainedOtsOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
  calc
    _ ≤ Pr[fun result => result.1.2.2 = true ∧
        ViewedWinningTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret
          (fun f cache secretKey log forgery index leaves =>
            ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
              (SettledForgedFreshLayerOpening f cache secretKey log index leaves
                  forgery.signature ∨
                SettledForgedBackwardChainOpening f cache secretKey log index leaves
                  forgery.signature)) result |
          gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table)
            ftsSecret] := by
      apply probEvent_mono
      intro _ _ hevent
      rcases hevent with hfresh | hbackward
      · rcases hfresh with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
          hdigest, hadmissible, heval, hfresh⟩
        exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible,
          heval, hbad, Or.inl hfresh⟩
      · rcases hbackward with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
          hdigest, hadmissible, heval, hbackward⟩
        exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible,
          heval, hbad, Or.inr hbackward⟩
    _ ≤ _ := probEvent_viewedWinningWitness_le_actualRetained adversary parameter table ftsSecret
      (fun f cache secretKey log forgery index leaves =>
        ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
          (SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature ∨
            SettledForgedBackwardChainOpening f cache secretKey log index leaves
              forgery.signature))

theorem winningRetainedOtsOpening_imp_verifyProbe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : WinningRetainedOtsOpeningWitness parameter table ftsSecret result) :
    WinningRetainedVerifyProbeWitness parameter table ftsSecret result := by
  rcases hwitness with ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, heval, hbad, hfresh | hbackward⟩
  · exact winningRetainedFresh_imp_verifyProbe parameter table ftsSecret result
      ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
        hbad, hfresh⟩
  · exact winningRetainedBackward_imp_verifyProbe parameter table ftsSecret result
      ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
        hbad, hbackward⟩

theorem probEvent_cleanOtsOpening_le_verifyProbeAfterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanOtsOpeningEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      Pr[WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret |
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret] := by
  let table := tableOfOtsSecret otsSecret
  calc
    _ ≤ Pr[WinningRetainedOtsOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      simpa [table, tableOtsSecret_tableOfOtsSecret] using
        probEvent_cleanOtsOpening_le_actualRetained adversary parameter table ftsSecret
    _ ≤ Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
      probEvent_mono fun result _ =>
        winningRetainedOtsOpening_imp_verifyProbe parameter table ftsSecret result
    _ = _ := by
      rw [actualRetainedGameAfterTable_eq_afterOtsSecret]
      simp only [table, tableOtsSecret_tableOfOtsSecret]
      rfl

theorem probEvent_sampledViewedGame_cleanOtsOpening_le_of_sampled
    (adversary : Adversary) (bound : ℝ≥0∞)
    (hsampled : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound) :
    Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] ≤ bound := by
  have hrewrite :
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] =
        Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGameFtsFirst adversary] :=
    OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_sampledViewedGame_eq_ftsFirst adversary)
  rw [hrewrite]
  unfold sampledViewedGameFtsFirst
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret hfts
  calc
    _ = Pr[fun result => cleanOtsOpeningEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] := by
      change Pr[SampledViewedEvent cleanOtsOpeningEvent |
          (fun result =>
            (⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩ : SampledViewedResult)) <$>
            sampledViewedOtsSecrets adversary parameter ftsSecret] = _
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
      unfold sampledViewedOtsSecrets sampledActualRetainedOtsSecrets
      apply probEvent_bind_le_bind_of_forall_le
      intro otsSecret _hots
      simpa [probEvent_map, Function.comp_def] using
        probEvent_cleanOtsOpening_le_verifyProbeAfterOtsSecret adversary parameter otsSecret
          ftsSecret
    _ = Pr[fun result => WinningRetainedVerifyProbeWitness parameter
          (extendStartTable result.1) ftsSecret result.2 |
        sampledActualRetainedOtsHashTable adversary parameter ftsSecret] :=
      (probEvent_sampledWinningRetainedVerifyProbe_eq_secrets adversary parameter ftsSecret).symm
    _ ≤ bound := hsampled parameter hparameter ftsSecret hfts

theorem security_of_sampledWinningRetainedVerifyProbe_grouped_le_mul
    (c : Nat) (hc : c + 46 ≤ 64)
    (hprobe : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
          ((c * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    SphincsSecurityStatement := by
  intro q hqPos adversary hq
  by_cases hqMax : q ≤ 2 ^ securityBits
  · have hqMax120 : q ≤ 2 ^ 120 := by simpa only [securityBits] using hqMax
    let unitBound := (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
    let probeBound := ((c * q : Nat) : ℝ≥0∞) *
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
    have hsampled : ∀ parameter ∈ support sampleParameter,
        ∀ ftsSecret ∈ support sampleFtsSecrets,
          Pr[fun result => WinningRetainedVerifyProbeWitness parameter
              (extendStartTable result.1) ftsSecret result.2 |
            sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ probeBound := by
      intro parameter hparameter ftsSecret hfts
      exact hprobe q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
    have hopening :
        Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] ≤
          probeBound :=
      probEvent_sampledViewedGame_cleanOtsOpening_le_of_sampled adversary probeBound hsampled
    have hencoding :
        Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] ≤
          ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      probEvent_sampled_cleanEncoding_le adversary q hq
    have hmessage :
        Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] ≤ unitBound := by
      apply (probEvent_sampled_cleanMessage_le adversary q hqPos hq hqMax120).trans
      dsimp only [unitBound]
      rw [mul_comm (q : ℝ≥0∞), mul_comm (q : ℝ≥0∞)]
      apply mul_le_mul_left
      rw [show digestBits = 128 by rfl]
      norm_num
    have huncovered :
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
          unitBound :=
      FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le adversary q hq
    apply forgeAdvantage_le_of_sampled_grouped_remaining_le adversary q hq hqMax120
    calc
      _ ≤ probeBound +
          (((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
          (unitBound + unitBound)) :=
        add_le_add hopening (add_le_add hencoding (add_le_add hmessage huncovered))
      _ = (((c + 46) * q : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
        simp only [probeBound, unitBound]
        push_cast
        ring
      _ ≤ ((64 * q : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
        gcongr
  · exact forgeAdvantage_le_of_security_pow_le adversary q (by omega)

end OtsProbeSimulation

end SphincsSecurity.Concrete
