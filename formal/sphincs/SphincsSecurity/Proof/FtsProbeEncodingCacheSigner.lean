import SphincsSecurity.Proof.FtsProbeEncodingCacheSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] EncodingCacheMonotoneSupport
set_option backward.isDefEq.respectTransparency false

theorem encodingCacheMonotoneSupport_ordinaryHash (computation : OracleComp HashSpec α) :
    EncodingCacheMonotoneSupport (simulateQ ordinaryHashImpl computation) :=
  encodingCacheMonotoneSupport_simulateQ _ (fun input => encodingCacheMonotoneSupport_splitHashQuery (.ordinary input)) computation

theorem encodingCacheMonotoneSupport_ordinaryTweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    EncodingCacheMonotoneSupport (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (encodingCacheMonotoneSupport_splitHashQuery _).bind fun _ => EncodingCacheMonotoneSupport.pure _

theorem encodingCacheMonotoneSupport_hiddenFtsLeafHash (parameter : PublicParameter) (coordinate : Coordinate) :
    EncodingCacheMonotoneSupport (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (encodingCacheMonotoneSupport_splitHashQuery _).bind fun _ => EncodingCacheMonotoneSupport.pure _

theorem encodingCacheMonotoneSupport_maskedFtsNode
    (parameter : PublicParameter) (index : Index) (tree : FtsTree) (level nodeIdx : Nat) :
    EncodingCacheMonotoneSupport (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => exact encodingCacheMonotoneSupport_hiddenFtsLeafHash parameter _
  | succ level ih =>
      unfold maskedFtsNode
      exact (ih _).bind fun _ => (ih _).bind fun _ => encodingCacheMonotoneSupport_ordinaryTweakableHash parameter _ _

theorem encodingCacheMonotoneSupport_maskedFtsKey (parameter : PublicParameter) (index : Index) :
    EncodingCacheMonotoneSupport (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  exact (encodingCacheMonotoneSupport_sequenceFin _ fun tree => encodingCacheMonotoneSupport_maskedFtsNode parameter index tree _ _).bind
    fun _ => encodingCacheMonotoneSupport_ordinaryTweakableHash parameter _ _

theorem encodingCacheMonotoneSupport_maskedFtsOpen
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) :
    EncodingCacheMonotoneSupport (maskedFtsOpen parameter index leaves) := by
  apply encodingCacheMonotoneSupport_sequenceFin
  intro tree
  apply encodingCacheMonotoneSupport_sequenceFin
  intro level
  exact encodingCacheMonotoneSupport_maskedFtsNode parameter index tree _ _

theorem encodingCacheMonotoneSupport_revealFtsSecret (parameter : PublicParameter) (coordinate : Coordinate) :
    EncodingCacheMonotoneSupport (revealFtsSecret parameter coordinate) := by
  unfold revealFtsSecret
  apply (encodingCacheMonotoneSupport_lift _).bind
  intro value
  apply (encodingCacheMonotoneSupport_splitHashQuery _).bind
  intro output
  apply (encodingCacheMonotoneSupport_modify _ _).bind
  · intro _
    exact EncodingCacheMonotoneSupport.pure _
  · intro cache encodingParameter position message input hinput answer hcached
    have hne : input ≠ (FtsSecretProbe.mk coordinate.1 coordinate.2.1 coordinate.2.2 value).input parameter := by
      intro heq
      rw [heq] at hinput
      exact ftsProbeInput_not_mem_encodingRetryInputs encodingParameter parameter position message _ hinput
    simpa only [ordinaryQueryCache_update_ordinary, QueryCache.cacheQuery, Function.update_of_ne hne] using hcached

theorem encodingCacheMonotoneSupport_revealSelectedFtsSecrets
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) :
    EncodingCacheMonotoneSupport (revealSelectedFtsSecrets parameter index leaves) :=
  encodingCacheMonotoneSupport_sequenceFin _ fun _ => encodingCacheMonotoneSupport_revealFtsSecret parameter _

theorem encodingCacheMonotoneSupport_probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    EncodingCacheMonotoneSupport (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | none => exact (EncodingCacheMonotoneSupport.pure ()).bind fun _ => encodingCacheMonotoneSupport_splitHashQuery _
  | some probe => exact (encodingCacheMonotoneSupport_lift _).bind fun _ => encodingCacheMonotoneSupport_splitHashQuery _

end SphincsSecurity.Concrete.FtsProbeSimulation
