import SphincsSecurity.Proof.OtsProbeCanonicalRejectionProbability
import SphincsSecurity.Proof.EncodingPrehitViewedBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal TightEncoding

set_option backward.isDefEq.respectTransparency false

def retainedRestWithVerdict (result : RetainedRestResult) : RetainedRestResult :=
  (result.1, retainedRestVerdict result)

def viewedPrehitRetainedProjection
    (result : (Digest × Forgery × Bool) × (ViewedFullTraceState × Bool)) :
    (RetainedGameResult × QueryCache HashSpec) × Bool :=
  (((result.1.1, ((result.1.2.1, result.2.1.trace.signing.toSigningLog), result.1.2.2)), result.2.1.cache), result.2.2)

def tracePrehitRetainedProjection
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) :
    (RetainedGameResult × QueryCache HashSpec) × Bool :=
  (((result.1.1.1, retainedRestWithVerdict result.1.1.2), result.1.2.1.cache), result.1.2.2)

theorem simulateQ_expanded_retained_eq_logged
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey) :
    simulateQ (expandedAdversaryImpl secretKey) (retainedGameRestComputation adversary publicKey) = (do
      let (forgery, log) ← (simulateQ (forwardOracles + signingOracle scheme secretKey) (adversary.main publicKey)).run
      let verified ← scheme.verify publicKey forgery.message forgery.signature
      pure ((forgery, log), verified)) := by
  unfold retainedGameRestComputation
  rw [simulateQ_bind, ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend]
  apply bind_congr
  rintro ⟨forgery, log⟩
  rw [simulateQ_bind]
  have hlift : simulateQ (expandedAdversaryImpl secretKey)
      (liftOracleWorldLeft (scheme.verify publicKey forgery.message forgery.signature)) =
      scheme.verify publicKey forgery.message forgery.signature :=
    FtsProbeSimulation.simulateQ_expanded_liftOracleWorldLeft secretKey _
  rw [hlift]
  simp only [simulateQ_pure]

theorem gameRestWithEncodingPrehitView_retained_projection
    (adversary : Adversary) (accountingKey : SecretKey) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (hit : Bool) :
    (fun result => ((((result.1.1, result.2.1.trace.signing.toSigningLog), result.1.2), result.2.1.cache), result.2.2)) <$>
      gameRestWithEncodingPrehitView adversary accountingKey publicKey secretKey initialCache hit =
      (fun result => ((retainedRestWithVerdict result.1.1, result.1.2), result.2)) <$>
        runEncodingPrehitMonitor accountingKey
          (simulateQ (expandedAdversaryImpl secretKey) (retainedGameRestComputation adversary publicKey)) initialCache hit := by
  let finish : Forgery × ((QueryCache HashSpec × Bool) × QueryLog SigningSpec) →
      ProbComp ((RetainedRestResult × QueryCache HashSpec) × Bool) := fun result => do
    let verified ← runEncodingPrehitMonitor accountingKey
      (scheme.verify publicKey result.1.message result.1.signature) result.2.1.1 result.2.1.2
    pure ((((result.1, result.2.2), decide (SigningTranscript.Valid result.2.2 ∧
      ¬SigningTranscript.Contains result.2.2 result.1) && verified.1.1), verified.1.2), verified.2)
  let state : ViewedFullTraceState × Bool := (⟨initialCache, ⟨[], [], []⟩, [], none⟩, hit)
  calc
    _ = (Prod.map id encodingPrehitViewedLogState <$>
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
          (adversary.main publicKey)).run state) >>= finish := by
      simp [gameRestWithEncodingPrehitView, state, finish, encodingPrehitViewedLogState,
        runEncodingPrehitMonitor_verifyWithView_fst, map_bind, bind_map_left, Prod.map]
    _ = _ := by
      rw [encodingPrehitViewedAdversaryImpl_log_projection, simulateQ_expanded_retained_eq_logged]
      simp only [runEncodingPrehitMonitor_bind, runEncodingPrehitMonitor_pure]
      simp [finish, state, SigningCacheTrace.toSigningLog, bind_map_left,
        retainedRestWithVerdict, retainedRestVerdict, map_bind]

theorem prehitViewedGame_retainedTrace_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    viewedPrehitRetainedProjection <$> gameAfterSecretsWithEncodingPrehitView adversary parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret =
      tracePrehitRetainedProjection <$> prehitRetainedQueryTrace adversary parameter table ftsSecret := by
  unfold gameAfterSecretsWithEncodingPrehitView prehitRetainedQueryTrace
  simp only [map_bind, map_pure]
  apply bind_congr
  intro root
  have hview := gameRestWithEncodingPrehitView_retained_projection adversary
    (primitiveAccountingKey parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret)
    ⟨root.1.1, parameter⟩ ⟨parameter, root.1.1, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    root.1.2 root.2
  rw [← runPrehitQueryTrace_monitor_projection _ _ _ (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2),
    Functor.map_map] at hview
  have hroot := congrArg (fun run => (fun result : (RetainedRestResult × QueryCache HashSpec) × Bool =>
    (((root.1.1, result.1.1), result.1.2), result.2)) <$> run) hview
  simpa only [Functor.map_map, Function.comp_def, map_eq_bind_pure_comp,
    viewedPrehitRetainedProjection, tracePrehitRetainedProjection, bind_assoc, pure_bind] using hroot

theorem clean_viewed_opening_imp_retained_projection_probe
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (ViewedFullTraceState × Bool))
    (hclean : cleanOtsOpeningEvent parameter (tableOtsSecret (extendStartTable table)) ftsSecret (result.1, result.2.1)) :
    WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret
      (viewedPrehitRetainedProjection result).1 := by
  apply winningRetainedOtsOpening_imp_verifyProbe
  rcases hclean with hfresh | hbackward
  · rcases hfresh with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
      hdigest, hadmissible, heval, hfresh⟩
    exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hbad, Or.inl hfresh⟩
  · rcases hbackward with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
      hdigest, hadmissible, heval, hbackward⟩
    exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hbad, Or.inr hbackward⟩

theorem retained_projection_probe_imp_probe
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hwitness : WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret
      (tracePrehitRetainedProjection result).1) :
    WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret (result.1.1, result.1.2.1.cache) := by
  rcases hwitness with ⟨hverdict, hwitness⟩
  refine ⟨?_, hwitness⟩
  cases hverified : result.1.1.2.2 with
  | false => simp [tracePrehitRetainedProjection, retainedRestWithVerdict, retainedRestVerdict, hverified] at hverdict
  | true => rfl

def prehitFreeRetainedVerifyProbeEvent
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  result.1.2.2 = false ∧
    WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret (result.1.1, result.1.2.1.cache)

theorem probEvent_prehitFree_residual_le_retainedVerifyProbe
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => result.2.2 = false ∧
      residualOtsOpeningEvent parameter (tableOtsSecret (extendStartTable table)) ftsSecret (result.1, result.2.1) |
      gameAfterSecretsWithEncodingPrehitView adversary parameter (tableOtsSecret (extendStartTable table)) ftsSecret] ≤
      Pr[prehitFreeRetainedVerifyProbeEvent parameter table ftsSecret |
        prehitRetainedQueryTrace adversary parameter table ftsSecret] := by
  let event : (RetainedGameResult × QueryCache HashSpec) × Bool → Prop := fun result =>
    result.2 = false ∧ WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret result.1
  calc
    _ ≤ Pr[event ∘ viewedPrehitRetainedProjection | gameAfterSecretsWithEncodingPrehitView adversary parameter
        (tableOtsSecret (extendStartTable table)) ftsSecret] := by
      apply probEvent_mono
      intro result _hresult hevent
      exact ⟨hevent.1, clean_viewed_opening_imp_retained_projection_probe parameter table ftsSecret result hevent.2.2.2.2⟩
    _ = Pr[event ∘ tracePrehitRetainedProjection | prehitRetainedQueryTrace adversary parameter table ftsSecret] := by
      rw [← probEvent_map, ← probEvent_map]
      exact congrArg (fun run => Pr[event | run])
        (prehitViewedGame_retainedTrace_projection adversary parameter table ftsSecret)
    _ ≤ _ := by
      apply probEvent_mono
      intro result _hresult hevent
      exact ⟨hevent.1, retained_projection_probe_imp_probe parameter table ftsSecret result hevent.2⟩

noncomputable def sampledPrehitFreeRetainedVerifyProbeRisk (adversary : Adversary) : ℝ≥0∞ :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' table, Pr[= table | sampleOtsHashTable] *
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        Pr[prehitFreeRetainedVerifyProbeEvent parameter table ftsSecret |
          prehitRetainedQueryTrace adversary parameter table ftsSecret]

open OracleComp.ProgramLogic.Relational in
set_option maxRecDepth 100000 in
theorem probEvent_sampled_prehitFree_residual_le_retainedVerifyProbe
    (adversary : Adversary) :
    Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
      sampledPrehitFreeRetainedVerifyProbeRisk adversary := by
  unfold sampledEncodingPrehitViewedGame sampledPrehitFreeRetainedVerifyProbeRisk
  simp only [sampleSecrets, bind_assoc, pure_bind, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, prehitFreeResidualOtsOpeningEvent, SampledViewedEvent]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple (relTriple_symm relTriple_uniformOtsHashTable_sampleOtsSecrets)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[fun result => result.2.2 = false ∧ residualOtsOpeningEvent parameter otsSecret ftsSecret (result.1, result.2.1) |
        gameAfterSecretsWithEncodingPrehitView adversary parameter otsSecret ftsSecret])
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[prehitFreeRetainedVerifyProbeEvent parameter table ftsSecret |
        prehitRetainedQueryTrace adversary parameter table ftsSecret])
    (fun _ => 0) (by
      intro otsSecret table hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_prehitFree_residual_le_retainedVerifyProbe adversary parameter table ftsSecret))
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled

end SphincsSecurity.Concrete.OtsProbeSimulation
