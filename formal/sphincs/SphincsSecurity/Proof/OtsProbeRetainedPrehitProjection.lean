import SphincsSecurity.Proof.OtsProbeRetainedPrehitTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.TightEncoding

set_option backward.isDefEq.respectTransparency false

theorem encodingPrehitViewedAdversaryImpl_cacheFlag_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => ((result.1, result.2.1.cache), result.2.2)) <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      runEncodingPrehitMonitor accountingKey (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache state.2 := by
  calc
    _ = (fun result : α × ((QueryCache HashSpec × Bool) × QueryLog SigningSpec) =>
        ((result.1, result.2.1.1), result.2.1.2)) <$>
        (Prod.map id encodingPrehitViewedLogState <$>
          (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state) := by
      rw [Functor.map_map]
      rfl
    _ = runEncodingPrehitMonitor accountingKey (Prod.fst <$>
        (simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2 := by
      rw [encodingPrehitViewedAdversaryImpl_log_projection, runEncodingPrehitMonitor_map, Functor.map_map]
    _ = _ := by
      rw [forwardOracles_add_signingOracle_eq_withTraceAppend, QueryImpl.fst_map_run_withTraceAppend]

theorem runPrehitQueryTrace_monitor_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => ((result.1.1, result.1.2.1.cache), result.1.2.2)) <$>
      runPrehitQueryTrace accountingKey secretKey computation state =
      runEncodingPrehitMonitor accountingKey (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache state.2 := by
  rw [← encodingPrehitViewedAdversaryImpl_cacheFlag_projection accountingKey secretKey computation state,
    ← runPrehitQueryTrace_projection, Functor.map_map]

def retainedRestVerdict (result : RetainedRestResult) : Bool :=
  decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2

def retainedPrehitVerdictProjection
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) :
    (Bool × QueryCache HashSpec) × Bool :=
  ((retainedRestVerdict result.1.1.2, result.1.2.1.cache), result.1.2.2)

theorem prehitRetainedQueryTrace_monitor_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    retainedPrehitVerdictProjection <$> prehitRetainedQueryTrace adversary parameter table ftsSecret =
      runEncodingPrehitMonitor (primitiveAccountingKey parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ false := by
  unfold prehitRetainedQueryTrace gameAfterSecrets
  rw [runEncodingPrehitMonitor_bind, map_bind]
  apply bind_congr
  intro root
  simp only [map_bind, map_pure, retainedPrehitVerdictProjection]
  rw [gameRest_eq_map_retained, runEncodingPrehitMonitor_map,
    ← runPrehitQueryTrace_monitor_projection _ _ _ (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2), Functor.map_map]
  rfl

theorem probEvent_prehitRetainedQueryTrace_jointBad_le_queryCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
    Pr[fun result => result.1.2.2 = true ∨
      SphincsSecurity.Bad parameter otsSecret ftsSecret result.1.2.1.cache ∨
      EncodingBad result.1.2.1.cache accountingKey |
        prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      expectedQueryCharge (refinedStructuralEncodingQueryCharge accountingKey) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  dsimp only
  have hbound := probEvent_prehit_or_bad_or_encodingBad_le_queryCharge
    (primitiveAccountingKey parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret)
    (gameAfterSecrets adversary parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret)
  rw [← prehitRetainedQueryTrace_monitor_projection, probEvent_map] at hbound
  exact hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
