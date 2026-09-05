import SphincsSecurity.Proof.OtsProbeNativeStoredRootRecords

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_sampleNativeStoredRootRecords_hit_le_occurrence
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (hconsistent : context.ValuesConsistent)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (hcache : ∀ digest, digest ∉ initialHistory → NoEncodingRootGuessCached parameter target digest cache)
    (bound : Nat) (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (hbudget : initialHistory.card + bound ≤ 2 ^ 126)
    (candidate : ResolvedRunResult α × Finset Digest → Option Digest) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess
      (runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory) candidate] ≤
    Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess
      (runNativeStoredRootRecords parameter root target ftsSecret computation context fuel table cache initialHistory) candidate] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply probEvent_samplePrivateHistoryGuess_hit_le_of_supported_compatible _ candidate (fun record => initialHistory ∪ record.2)
  · exact probOutput_nativeStoredRootRecords_eq_of_compatible parameter root target hroot ftsSecret computation context fuel table cache
      initialHistory hconsistent hpending hcache
  · intro output record hhit
    exact probOutput_nativeStoredRootRecords_eq_zero_of_history_hit parameter root target ftsSecret computation context fuel table cache
      initialHistory output bound hbound record hhit
  · intro output record hrecord
    have hcard := (nativeStoredRootRecords_supported_history parameter root target ftsSecret computation context fuel table cache
      initialHistory output bound hbound record hrecord).2
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hcard initialHistory.card).trans hbudget)

end SphincsSecurity.Concrete.OtsProbeSimulation
