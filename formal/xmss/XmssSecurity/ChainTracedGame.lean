import XmssSecurity.AdaptiveRevealMonitor
import XmssSecurity.ChainRevealFiltering

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def actionTraceOutcome
    (publicKey : PublicKey) (secretKey : SecretKey)
    (result : (Forgery × Bool) × AttackerActionTrace) : GameOutcome :=
  ⟨publicKey, secretKey, result.1.1, result.2.toSigningLog, result.1.2⟩

noncomputable def detailedGameAfterKeygenWithActionTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp ((GameOutcome × QueryCache HashSpec) × AttackerActionTrace) :=
  (fun result => ((actionTraceOutcome publicKey secretKey result.1, result.2), result.1.2)) <$>
    (simulateQ xmssRomImpl
      (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey)).run initialCache

theorem detailedGameAfterKeygenWithActionTrace_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    Prod.fst <$> detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey initialCache =
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run initialCache := by
  have hsource := sourceActionTracedDetailedGameAfterKeygen_log_projection adversary
    publicKey secretKey
  have hsimulated := congrArg
    (fun computation => (simulateQ xmssRomImpl computation).run initialCache) hsource
  simpa [detailedGameAfterKeygenWithActionTrace, actionTraceOutcome,
    simulateQ_map, StateT.run_map, Functor.map_map, Function.comp_def] using hsimulated

theorem detailedGameAfterKeygenWithActionTrace_support_info
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : (GameOutcome × QueryCache HashSpec) × AttackerActionTrace)
    (hresult : result ∈ support
      (detailedGameAfterKeygenWithActionTrace adversary publicKey secretKey initialCache)) :
    result.1.1.publicKey = publicKey ∧
      result.1.1.secretKey = secretKey ∧
      result.1.1.signingLog = result.2.toSigningLog ∧
      (((result.1.1.forgery, result.1.1.verified), result.2), result.1.2) ∈ support
        ((simulateQ xmssRomImpl
          (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey)).run
            initialCache) ∧
      ((result.1.1.forgery, result.1.1.verified), result.2) ∈ support
        (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey) := by
  unfold detailedGameAfterKeygenWithActionTrace at hresult
  rw [support_map] at hresult
  obtain ⟨sourceResult, hsourceRun, rfl⟩ := hresult
  refine ⟨rfl, rfl, rfl, hsourceRun, ?_⟩
  apply support_simulateQ_run'_subset xmssRomImpl
    (sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey) initialCache
  rw [StateT.run'_eq, support_map]
  exact ⟨sourceResult, hsourceRun, rfl⟩

noncomputable def detailedGameWithKeygenCacheAndActionTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  let execution ← detailedGameAfterKeygenWithActionTrace adversary keyResult.1.1
    keyResult.1.2 keyResult.2
  pure ((keyResult, execution.1), execution.2)

theorem detailedGameWithKeygenCacheAndActionTrace_projection
    (adversary : Adversary Concrete.scheme) :
    Prod.fst <$> detailedGameWithKeygenCacheAndActionTrace adversary =
      detailedGameWithKeygenCache adversary := by
  unfold detailedGameWithKeygenCacheAndActionTrace detailedGameWithKeygenCache
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← detailedGameAfterKeygenWithActionTrace_projection adversary keyResult.1.1
    keyResult.1.2 keyResult.2]
  simp [Functor.map_map]

theorem detailedGameWithKeygenCacheAndActionTrace_support_info
    (adversary : Adversary Concrete.scheme)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary)) :
    result.1.1 ∈ support ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) ∧
      result.1.2.1.publicKey = result.1.1.1.1 ∧
      result.1.2.1.secretKey = result.1.1.1.2 ∧
      result.1.2.1.signingLog = result.2.toSigningLog ∧
      ((result.1.2.1.forgery, result.1.2.1.verified), result.2) ∈ support
        (sourceActionTracedDetailedGameAfterKeygen adversary result.1.1.1.1
          result.1.1.1.2) := by
  unfold detailedGameWithKeygenCacheAndActionTrace at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeyResult, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨execution, hexecution, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  obtain ⟨hpublic, hsecret, hlog, _hrun, hsource⟩ :=
    detailedGameAfterKeygenWithActionTrace_support_info adversary keyResult.1.1
      keyResult.1.2 keyResult.2 execution hexecution
  exact ⟨hkeyResult, hpublic, hsecret, hlog, hsource⟩

theorem detailedGameWithKeygenCacheAndActionTrace_unrevealedProbes_length_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary))
    (chain : ChainIndex) (encoding : Encoding) :
    (unrevealedChainValueProbes result.1.2.2 result.1.2.1.secretKey
      result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding).length ≤ q := by
  obtain ⟨hkeygen, _hpublic, hsecret, _hlog, hsource⟩ :=
    detailedGameWithKeygenCacheAndActionTrace_support_info adversary result hresult
  have hlength := traced_unrevealedChainValueProbes_length_le q adversary hbound
    result.1.1 hkeygen
    ((result.1.2.1.forgery, result.1.2.1.verified), result.2) hsource
    result.1.2.2 result.1.2.1.signingLog chain encoding
  simpa [hsecret] using hlength

theorem WinningOutcomeChainValueHasKeygenOrigin.readMany_of_mem_actionTracedGame
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hresult : result ∈ support (detailedGameWithKeygenCacheAndActionTrace adversary))
    (chain : ChainIndex)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin result.1.1.2 result.1.2.2
      result.1.1.1.2 result.1.2.1 chain) :
    ∃ encoding,
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash result.1.2.2 result.1.1.1.2.parameter
            result.1.2.1.forgery.epoch
            (result.1.2.1.forgery.message,
              result.1.2.1.forgery.signature.randomness)) = some encoding ∧
      (let probe : ChainValueIndex × Digest :=
          ((result.1.2.1.forgery.epoch, encoding chain),
            result.1.2.1.forgery.signature.chainValue chain)
        let probes := unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
          result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding
        IndexedHiddenValue.readMany
            (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain) q
            (IndexedHiddenValue.listStrategy probe probes) = true ∧
          IndexedHiddenValue.AvoidsReveals
            (returnedChainValueReveals result.1.1.2 result.1.2.2 result.1.1.1.2
              result.1.2.1.signingLog chain)
            (IndexedHiddenValue.listStrategy probe probes)) := by
  obtain ⟨_hkeygen, _hpublic, hsecret, _hlog, _hsource⟩ :=
    detailedGameWithKeygenCacheAndActionTrace_support_info adversary result hresult
  apply horigin.readMany_unrevealed_eq_true result.1.1.2 result.1.2.2
    result.1.1.1.2 result.1.2.1 chain result.2 q hsecret
  intro encoding
  have hlength := detailedGameWithKeygenCacheAndActionTrace_unrevealedProbes_length_le
    q adversary hbound result hresult chain encoding
  simpa [hsecret] using hlength

noncomputable def ActionTracedChainProbeHit
    (q : Nat) (chain : ChainIndex)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) : Prop :=
  ∃ encoding,
    TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.2 result.1.1.1.2.parameter
          result.1.2.1.forgery.epoch
          (result.1.2.1.forgery.message,
            result.1.2.1.forgery.signature.randomness)) = some encoding ∧
    (let probe : ChainValueIndex × Digest :=
        ((result.1.2.1.forgery.epoch, encoding chain),
          result.1.2.1.forgery.signature.chainValue chain)
      let probes := unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
        result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding
      IndexedHiddenValue.readMany
          (keygenChainValueTable result.1.1.2 result.1.1.1.2 chain) q
          (IndexedHiddenValue.listStrategy probe probes) = true ∧
        IndexedHiddenValue.AvoidsReveals
          (returnedChainValueReveals result.1.1.2 result.1.2.2 result.1.1.1.2
            result.1.2.1.signingLog chain)
          (IndexedHiddenValue.listStrategy probe probes))

noncomputable def actionTracedForgeryEncoding
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) : Encoding :=
  (TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash result.1.2.2 result.1.1.1.2.parameter
      result.1.2.1.forgery.epoch
      (result.1.2.1.forgery.message,
        result.1.2.1.forgery.signature.randomness))).getD
          (fun _ => ⟨0, by simp [chainLength]⟩)

noncomputable def actionTracedRevealProbeView
    (chain : ChainIndex)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    IndexedHiddenValue.RevealProbeView ChainValueIndex :=
  let encoding := actionTracedForgeryEncoding result
  let probe : ChainValueIndex × Digest :=
    ((result.1.2.1.forgery.epoch, encoding chain),
      result.1.2.1.forgery.signature.chainValue chain)
  let probes := unrevealedChainValueProbes result.1.2.2 result.1.1.1.2
    result.1.2.1.signingLog chain result.2 result.1.2.1.forgery encoding
  ⟨returnedChainValueReveals result.1.1.2 result.1.2.2 result.1.1.1.2
      result.1.2.1.signingLog chain,
    keygenChainValueTable result.1.1.2 result.1.1.1.2 chain,
    IndexedHiddenValue.listStrategy probe probes⟩

theorem actionTracedRevealProbeView_table_installs_reveals
    (chain : ChainIndex)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    IndexedHiddenValue.installReveals
        (actionTracedRevealProbeView chain result).table
        (actionTracedRevealProbeView chain result).reveals =
      (actionTracedRevealProbeView chain result).table := by
  simp only [actionTracedRevealProbeView]
  exact install_returnedChainValueReveals_eq_keygenTable result.1.1.2
    result.1.2.2 result.1.1.1.2 result.1.2.1.signingLog chain

theorem actionTracedChainProbeHit_implies_revealProbeView_hit
    (q : Nat) (chain : ChainIndex)
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hhit : ActionTracedChainProbeHit q chain result) :
    IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q
      (actionTracedRevealProbeView chain result) := by
  obtain ⟨encoding, hdecode, hhit⟩ := hhit
  have hencoding : actionTracedForgeryEncoding result = encoding := by
    simp [actionTracedForgeryEncoding, hdecode]
  simpa [IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals,
    actionTracedRevealProbeView, hencoding] using hhit

theorem actionTracedChainProbeHit_probability_le_revealProbeView
    (q : Nat) (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    Pr[ActionTracedChainProbeHit q chain |
      detailedGameWithKeygenCacheAndActionTrace adversary] ≤
    Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
      actionTracedRevealProbeView chain <$>
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
  rw [probEvent_map]
  apply probEvent_mono
  intro result _hresult hhit
  exact actionTracedChainProbeHit_implies_revealProbeView_hit q chain result hhit

noncomputable def HasActionTracedRevealCoupling
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) : Prop :=
  ∃ transcriptGenerator : ProbComp
      (List (ChainValueIndex × Digest) ×
        (List Bool → ChainValueIndex × Digest)),
    𝒟[actionTracedRevealProbeView chain <$>
        detailedGameWithKeygenCacheAndActionTrace adversary] =
      𝒟[IndexedHiddenValue.adaptiveRevealViewExperiment transcriptGenerator]

noncomputable def HasActionTracedRevealReduction
    (q : Nat) (adversary : Adversary Concrete.scheme) (chain : ChainIndex) : Prop :=
  ∃ transcriptGenerator : ProbComp
      (List (ChainValueIndex × Digest) ×
        (List Bool → ChainValueIndex × Digest)),
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] ≤
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals q |
        IndexedHiddenValue.adaptiveRevealViewExperiment transcriptGenerator]

noncomputable def HasActionTracedMonitorReduction
    (q : Nat) (adversary : Adversary Concrete.scheme) (chain : ChainIndex) : Prop :=
  ∃ (Control : Type)
      (controller : Control → ProbComp
        (AdaptiveRevealMonitor.ControllerAction Control ChainValueIndex))
      (steps : Nat) (initial : Control),
    Pr[ActionTracedChainProbeHit q chain |
        detailedGameWithKeygenCacheAndActionTrace adversary] ≤
      Pr[(fun hit : Bool => hit = true) |
        AdaptiveRevealMonitor.run controller AdaptiveRevealMonitor.State.empty
          steps q initial]

noncomputable def actionTracedRevealTranscriptGenerator
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    ProbComp (List (ChainValueIndex × Digest) ×
      (List Bool → ChainValueIndex × Digest)) :=
  (fun view : IndexedHiddenValue.RevealProbeView ChainValueIndex =>
    (view.reveals, view.strategy)) <$>
      (actionTracedRevealProbeView chain <$>
        detailedGameWithKeygenCacheAndActionTrace adversary)

theorem hasActionTracedRevealCoupling_of_canonical
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (hdist :
      𝒟[actionTracedRevealProbeView chain <$>
          detailedGameWithKeygenCacheAndActionTrace adversary] =
        𝒟[IndexedHiddenValue.adaptiveRevealViewExperiment
          (actionTracedRevealTranscriptGenerator adversary chain)]) :
    HasActionTracedRevealCoupling adversary chain :=
  ⟨actionTracedRevealTranscriptGenerator adversary chain, hdist⟩

theorem hasActionTracedRevealReduction_of_coupling
    (q : Nat) (adversary : Adversary Concrete.scheme) (chain : ChainIndex)
    (hcoupling : HasActionTracedRevealCoupling adversary chain) :
    HasActionTracedRevealReduction q adversary chain := by
  obtain ⟨transcriptGenerator, hdist⟩ := hcoupling
  refine ⟨transcriptGenerator,
    (actionTracedChainProbeHit_probability_le_revealProbeView
      q adversary chain).trans ?_⟩
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le

theorem winningChainOrigin_probability_le_actionTracedProbeHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (chain : ChainIndex) :
    Pr[fun result =>
      WinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 chain |
      detailedGameWithKeygenCache adversary] ≤
    Pr[ActionTracedChainProbeHit q chain |
      detailedGameWithKeygenCacheAndActionTrace adversary] := by
  rw [← detailedGameWithKeygenCacheAndActionTrace_projection, probEvent_map]
  apply probEvent_mono
  intro result hresult horigin
  exact horigin.readMany_of_mem_actionTracedGame q adversary hbound result hresult chain

theorem winningChainOrigin_probability_le_of_revealCoupling
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (chain : ChainIndex)
    (hcoupling : HasActionTracedRevealCoupling adversary chain) :
    Pr[fun result =>
      WinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 chain |
      detailedGameWithKeygenCache adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨transcriptGenerator, hdist⟩ := hcoupling
  exact (winningChainOrigin_probability_le_actionTracedProbeHit
    q adversary hbound chain).trans
      ((actionTracedChainProbeHit_probability_le_revealProbeView
        q adversary chain).trans
          (IndexedHiddenValue.reveal_view_coupling_hit_le
            (actionTracedRevealProbeView chain <$>
              detailedGameWithKeygenCacheAndActionTrace adversary)
            transcriptGenerator q hdist))

theorem winningChainOrigin_probability_le_of_revealReduction
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (chain : ChainIndex)
    (hreduction : HasActionTracedRevealReduction q adversary chain) :
    Pr[fun result =>
      WinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 chain |
      detailedGameWithKeygenCache adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨transcriptGenerator, hreduce⟩ := hreduction
  exact (winningChainOrigin_probability_le_actionTracedProbeHit
    q adversary hbound chain).trans
      (hreduce.trans
        (IndexedHiddenValue.adaptive_reveal_view_hit_le transcriptGenerator q))

theorem winningChainOrigin_probability_le_of_monitorReduction
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (chain : ChainIndex)
    (hreduction : HasActionTracedMonitorReduction q adversary chain) :
    Pr[fun result =>
      WinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 chain |
      detailedGameWithKeygenCache adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨Control, controller, steps, initial, hreduce⟩ := hreduction
  exact (winningChainOrigin_probability_le_actionTracedProbeHit
    q adversary hbound chain).trans
      (hreduce.trans
        (AdaptiveRevealMonitor.run_empty_true_probability_le controller
          steps q initial))

end XmssSecurity
