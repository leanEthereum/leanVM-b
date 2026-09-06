import SphincsSecurity.Proof.FtsProbeCachePotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingCachePotential (inputs : Finset HashInput) (cache : SplitHashCache) : ENNReal :=
  encodingExhaustionPotential inputs (ordinaryQueryCache cache)

theorem ordinaryQueryCache_update_ordinary (cache : SplitHashCache) (input : HashInput) (output : HashOutput) :
    ordinaryQueryCache (Function.update cache (.ordinary input) (some output)) =
      (ordinaryQueryCache cache).cacheQuery input output := by
  funext other
  by_cases heq : other = input <;> simp [ordinaryQueryCache, Function.update, QueryCache.cacheQuery, heq]

theorem encodingCachePotential_update_hidden
    (inputs : Finset HashInput) (cache : SplitHashCache) (coordinate : Coordinate) (output : HashOutput) :
    encodingCachePotential inputs (Function.update cache (.hiddenLeaf coordinate) (some output)) = encodingCachePotential inputs cache := by
  have heq : ordinaryQueryCache (Function.update cache (.hiddenLeaf coordinate) (some output)) = ordinaryQueryCache cache := by
    funext input
    simp [ordinaryQueryCache, Function.update]
  rw [encodingCachePotential, heq]
  rfl

theorem encodingCachePotential_update_ordinary
    (inputs : Finset HashInput) (cache : SplitHashCache) (input : HashInput) (output : HashOutput) (hnot : input ∉ inputs) :
    encodingCachePotential inputs (Function.update cache (.ordinary input) (some output)) = encodingCachePotential inputs cache := by
  rw [encodingCachePotential, ordinaryQueryCache_update_ordinary,
    encodingExhaustionPotential_cacheQuery_of_not_mem inputs _ input output hnot]
  rfl

theorem rawCachePotentialBound_splitHashQuery_encoding
    (inputs : Finset HashInput) (key : SplitHashKey) :
    RawCachePotentialBound (encodingCachePotential inputs) (splitHashQuery key) := by
  intro table state fuel cache
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp [AdaptiveRevealProbe.runRaw, rawCachePotential]
  | none =>
      simp only
      unfold AdaptiveRevealProbe.hashOutputQuery
      rw [AdaptiveRevealProbe.runRaw_hashOutput_query_bind, tsum_probOutput_bind_mul]
      simp only [AdaptiveRevealProbe.runRaw, construct_pure, tsum_probOutput_pure_mul, rawCachePotential]
      cases key with
      | hiddenLeaf coordinate =>
          simp only [encodingCachePotential_update_hidden]
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one
      | ordinary input =>
          simp only [encodingCachePotential, ordinaryQueryCache_update_ordinary]
          exact (expected_encodingExhaustionPotential_fresh inputs (ordinaryQueryCache cache) input hlookup).le

theorem ftsProbeInput_not_mem_encodingRetryInputs
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (probe : FtsSecretProbe) :
    probe.input parameter ∉ encodingRetryInputs encodingParameter position message := by
  intro hmem
  obtain ⟨counter, _, heq⟩ := Finset.mem_image.mp hmem
  exact OtsProbeSimulation.encodingRetryInput_ne_position_tweak encodingParameter parameter position message counter.val
    (.ftsLeaf probe.index probe.tree probe.leafIdx) (digestBytes probe.candidate) heq

attribute [local irreducible] RawCachePotentialBound

theorem rawCachePotentialBound_ordinaryHash_encoding
    (inputs : Finset HashInput) (computation : OracleComp HashSpec α) :
    RawCachePotentialBound (encodingCachePotential inputs) (simulateQ ordinaryHashImpl computation) :=
  rawCachePotentialBound_simulateQ _ _ (fun input => rawCachePotentialBound_splitHashQuery_encoding inputs (.ordinary input)) computation

theorem rawCachePotentialBound_ordinaryTweakableHash_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    RawCachePotentialBound (encodingCachePotential inputs) (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (rawCachePotentialBound_splitHashQuery_encoding inputs _).bind fun _ => RawCachePotentialBound.pure _ _

theorem rawCachePotentialBound_hiddenFtsLeafHash_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (coordinate : Coordinate) :
    RawCachePotentialBound (encodingCachePotential inputs) (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (rawCachePotentialBound_splitHashQuery_encoding inputs _).bind fun _ => RawCachePotentialBound.pure _ _

theorem rawCachePotentialBound_maskedFtsNode_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) (tree : FtsTree) (level nodeIdx : Nat) :
    RawCachePotentialBound (encodingCachePotential inputs) (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => exact rawCachePotentialBound_hiddenFtsLeafHash_encoding inputs parameter _
  | succ level ih =>
      unfold maskedFtsNode
      exact (ih _).bind fun _ => (ih _).bind fun _ => rawCachePotentialBound_ordinaryTweakableHash_encoding inputs parameter _ _

theorem rawCachePotentialBound_maskedFtsKey_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) :
    RawCachePotentialBound (encodingCachePotential inputs) (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  exact (rawCachePotentialBound_sequenceFin _ _ fun tree => rawCachePotentialBound_maskedFtsNode_encoding inputs parameter index tree _ _).bind
    fun _ => rawCachePotentialBound_ordinaryTweakableHash_encoding inputs parameter _ _

theorem rawCachePotentialBound_maskedFtsOpen_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RawCachePotentialBound (encodingCachePotential inputs) (maskedFtsOpen parameter index leaves) := by
  apply rawCachePotentialBound_sequenceFin
  intro tree
  apply rawCachePotentialBound_sequenceFin
  intro level
  exact rawCachePotentialBound_maskedFtsNode_encoding inputs parameter index tree _ _

theorem rawCachePotentialBound_revealFtsSecret_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (coordinate : Coordinate) :
    RawCachePotentialBound (encodingCachePotential (encodingRetryInputs encodingParameter position message)) (revealFtsSecret parameter coordinate) := by
  unfold revealFtsSecret
  apply (rawCachePotentialBound_lift _ _).bind
  intro value
  apply (rawCachePotentialBound_splitHashQuery_encoding _ _).bind
  intro output
  exact (rawCachePotentialBound_modify _ _ (fun cache =>
    (encodingCachePotential_update_ordinary _ cache _ output
      (ftsProbeInput_not_mem_encodingRetryInputs encodingParameter parameter position message _)).le)).bind
    fun _ => RawCachePotentialBound.pure _ _

theorem rawCachePotentialBound_revealSelectedFtsSecrets_encoding
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (index : Index) (leaves : DigestTree → FtsLeaf) :
    RawCachePotentialBound (encodingCachePotential (encodingRetryInputs encodingParameter position message))
      (revealSelectedFtsSecrets parameter index leaves) :=
  rawCachePotentialBound_sequenceFin _ _ fun _ =>
    rawCachePotentialBound_revealFtsSecret_encoding encodingParameter parameter position message _

theorem rawCachePotentialBound_probingHashQuery_encoding
    (inputs : Finset HashInput) (parameter : PublicParameter) (input : HashInput) :
    RawCachePotentialBound (encodingCachePotential inputs) (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | none => exact (RawCachePotentialBound.pure _ ()).bind fun _ => rawCachePotentialBound_splitHashQuery_encoding inputs _
  | some probe => exact (rawCachePotentialBound_lift _ _).bind fun _ => rawCachePotentialBound_splitHashQuery_encoding inputs _

end SphincsSecurity.Concrete.FtsProbeSimulation
