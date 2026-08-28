import SphincsSecurity.Proof.OtsProbeOrigin

/-!
# Winning one-time probe witnesses

The fresh and backward terminal events both expose an uncovered correct probe whose exact input
belongs to the successful verifier's query trace under the retained answer function.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def WinningRetainedVerifyProbeWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery _ _ =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        VerifyProbeWitness f cache secretKey log forgery.message forgery.signature

theorem actualRetainedGameAfterTable_verify_support
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hresult : result ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret table))
    (hverified : result.1.2.2 = true) :
    ∃ adversaryCache : QueryCache HashSpec,
      (true, result.2) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (verify ⟨result.1.1, parameter⟩ result.1.2.1.1.message
            result.1.2.1.1.signature)).run adversaryCache) := by
  rw [actualRetainedGameAfterTable, mem_support_bind_iff] at hresult
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨restResult, finalCache⟩, hrest, hfinish⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinish
  rcases hfinish with ⟨hresultValue, hresultCache⟩
  rw [simulateQ_unloggedMapped_retainedGameRestComputation,
    StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, log⟩, adversaryCache⟩, _, hverify⟩ := hrest
  rw [StateT.run_bind, mem_support_bind_iff] at hverify
  obtain ⟨⟨verified, verifyCache⟩, hverify, hreturn⟩ := hverify
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  rcases hreturn with ⟨hrestResult, hfinalCache⟩
  subst restResult
  subst finalCache
  simp only at hverified
  subst verified
  refine ⟨adversaryCache, ?_⟩
  simpa only [scheme, simulateQ_romImpl_liftM] using hverify

def ExecutedVerifyProbeWitness (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  VerifyProbeWitness f cache secretKey signingLog forgery.message forgery.signature ∧
    CachedRun cache f
      (verify ⟨secretKey.root, secretKey.parameter⟩ forgery.message forgery.signature)

def WinningRetainedExecutedVerifyProbeWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery _ _ =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        ExecutedVerifyProbeWitness f cache secretKey log forgery

theorem winningRetainedVerifyProbe_imp_executed
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hresult : result ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret table))
    (hwitness : WinningRetainedVerifyProbeWitness parameter table ftsSecret result) :
    WinningRetainedExecutedVerifyProbeWitness parameter table ftsSecret result := by
  rcases hwitness with ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, heval, hbad, hprobe⟩
  obtain ⟨adversaryCache, hverify⟩ := actualRetainedGameAfterTable_verify_support adversary
    parameter ftsSecret table result hresult hverdict
  have hrun : CachedRun result.2 f
      (verify ⟨result.1.1, parameter⟩ result.1.2.1.1.message
        result.1.2.1.1.signature) :=
    (replay_of_mem_support
      (verify ⟨result.1.1, parameter⟩ result.1.2.1.1.message
        result.1.2.1.1.signature)
      adversaryCache true result.2 hverify f hf).2.2
  exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
    hbad, hprobe, hrun⟩

theorem probEvent_winningRetainedVerifyProbe_le_executed
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] ≤
      Pr[WinningRetainedExecutedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
  probEvent_mono fun result hresult hwitness =>
    winningRetainedVerifyProbe_imp_executed adversary parameter table ftsSecret result hresult
      hwitness

def RawCachesVerifierTrace (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (forgery : Forgery) (cache : SplitHashCache) : Prop :=
  ∀ input, input ∈ queriedInputs f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature) →
    cache (.ordinary input) ≠ none

theorem ChainInvariant.not_finalized_false_of_verifyProbe
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {rawState completedState : LazyRevealProbe.State Coordinate}
    {rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      rawState rawCache)
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hqueries : RawCachesVerifierTrace f parameter root forgery rawCache)
    (hprobe : VerifyProbeWitness f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨lay, digest, layerMessage, codeword, chainIdx, hdigit, probe, input,
    hinput, hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, hquery,
    _, hnotCovered, _hsourceSettled⟩ := hprobe
  exact hinvariant.not_finalized_false_of_uncovered_probe probe input hhits hmatches
    (hqueries input hquery) hnotCovered (hcompletedTable probe.coordinate) hrealizes hfinalize

theorem winningRetainedFresh_imp_verifyProbe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : WinningRetainedFreshLayerOpeningWitness parameter table ftsSecret result) :
    WinningRetainedVerifyProbeWitness parameter table ftsSecret result := by
  rcases hwitness with ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, heval, hbad, hfresh⟩
  exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
    hbad, SettledForgedFreshLayerOpening.toVerifyProbeWitness hdigest hadmissible hfresh⟩

theorem winningRetainedBackward_imp_verifyProbe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : WinningRetainedBackwardChainOpeningWitness parameter table ftsSecret result) :
    WinningRetainedVerifyProbeWitness parameter table ftsSecret result := by
  rcases hwitness with ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, heval, hbad, hbackward⟩
  exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
    hbad, SettledForgedBackwardChainOpening.toVerifyProbeWitness hdigest hadmissible hbackward⟩

theorem probEvent_winningRetainedFresh_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[WinningRetainedFreshLayerOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] ≤
      Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
  probEvent_mono fun result _ => winningRetainedFresh_imp_verifyProbe
    parameter table ftsSecret result

theorem probEvent_winningRetainedBackward_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[WinningRetainedBackwardChainOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] ≤
      Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
  probEvent_mono fun result _ => winningRetainedBackward_imp_verifyProbe
    parameter table ftsSecret result

end SphincsSecurity.Concrete.OtsProbeSimulation
