import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootCache
import SphincsSecurity.Proof.OtsProbeNativeStoredRoot

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def RootEncodingStoredNativeSameRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      RootEncodingNativeSameRel parameter target leftRoot rightRoot (some left) (some right) ∧
        StoredNativeLayerRoot left.context target leftRoot
  | none, none => True
  | _, _ => False

def RootEncodingNativeRelatesStored
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table, StoredNativeLayerRoot state target leftRoot →
      RelTriple
        (runResolvedFromTable state fuel table (left.run leftCache))
        (runResolvedFromTable state fuel table (right.run rightCache))
        (RootEncodingStoredNativeSameRel parameter target leftRoot rightRoot)

theorem relTriple_native_rootEncoding_add_stored
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (leftCache rightCache : SplitHashCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hrelation : RelTriple
      (runResolvedFromTable state fuel table (left.run leftCache))
      (runResolvedFromTable state fuel table (right.run rightCache))
      (RootEncodingNativeSameRel parameter target leftRoot rightRoot))
    (hstored : StoredNativeLayerRoot state target leftRoot) :
    RelTriple
      (runResolvedFromTable state fuel table (left.run leftCache))
      (runResolvedFromTable state fuel table (right.run rightCache))
      (RootEncodingStoredNativeSameRel parameter target leftRoot rightRoot) := by
  let leftRun := runResolvedFromTable state fuel table (left.run leftCache)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrelation
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  apply relTriple_post_mono hsupported
  intro leftResult rightResult hresult
  rcases hresult with ⟨hrel, hleftSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => trivial
      | some rightResult => simp [RootEncodingNativeSameRel] at hrel
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingNativeSameRel] at hrel
      | some rightResult =>
          exact ⟨hrel, storedNativeLayerRoot_of_mem_runResolved (left.run leftCache)
            state fuel table leftResult target leftRoot hstored hleftSupport⟩

theorem RootEncodingNativeRelates.toStored
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hrel : RootEncodingNativeRelates parameter target leftRoot rightRoot left right) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot left right := by
  intro leftCache rightCache hcache state fuel table hstored
  exact relTriple_native_rootEncoding_add_stored parameter target leftRoot rightRoot left right
    leftCache rightCache state fuel table
      (hrel leftCache rightCache hcache state fuel table) hstored

theorem RootEncodingNativeRelatesStored.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingNativeRelatesStored parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
        (leftNext leftValue) (rightNext rightValue)) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftCache rightCache hcache state fuel table hstored
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind (hfirst leftCache rightCache hcache state fuel table hstored)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingStoredNativeSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingStoredNativeSameRel] at hresult
      | some rightResult =>
          rcases hresult with
            ⟨⟨hstate, hremaining, htable, hvalue, hnextCache⟩, hnextStored⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl leftResult.value.2
            rightResult.value.2 hnextCache leftResult.context leftResult.remaining
              leftResult.table hnextStored

theorem rootEncodingNativeRelatesStored_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
        (left index) (right index)) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact ((rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
        Fin.elim0).relates).toStored
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact ((rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)).relates).toStored

theorem rootEncodingNativeCouples_maskedSignLayer_of_layerMessagePosition_ne
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (rootEncodingNativeCouples_maskedLayerMessage parameter target leftRoot rightRoot
    ftsSecret index lay).bind
  intro message
  exact rootEncodingNativeCouples_maskedOtsLayerAfterMessage_of_not_positionNames parameter
    target leftRoot rightRoot index lay message
      (not_encodingPositionNamesRoot_of_layerMessagePosition_ne target index lay hne)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_native_maskedSignLayer_comparisonRoot_of_message
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hnotBottom : lay ≠ bottomLayer)
    (leftRoot rightRoot : Digest)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter (layerMessagePosition index lay)
      leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hmessageRoot : ∀ result,
      some result ∈ support (runResolvedFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
      result.value.1 = leftRoot) :
    RelTriple
      (runResolvedFromTable state fuel table
        ((maskedSignLayer parameter ftsSecret index lay).run leftCache))
      (runResolvedFromTable state fuel table
        ((maskedSignLayerWithComparisonRoot parameter ftsSecret index lay rightRoot).run
          rightCache))
      (RootEncodingNativeSameRel parameter (layerMessagePosition index lay)
        leftRoot rightRoot) := by
  unfold maskedSignLayer maskedSignLayerWithComparisonRoot
  change RelTriple
    (runResolvedFromTable state fuel table
      ((maskedLayerMessage parameter ftsSecret index lay >>= fun message =>
        maskedOtsLayerAfterMessage parameter index lay message).run leftCache))
    (runResolvedFromTable state fuel table
      ((maskedLayerMessage parameter ftsSecret index lay >>= fun _ =>
        maskedOtsLayerAfterMessage parameter index lay rightRoot).run rightCache)) _
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  let leftMessageRun := runResolvedFromTable state fuel table
    ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)
  have hmessages := rootEncodingNativeCouples_maskedLayerMessage parameter
    (layerMessagePosition index lay) leftRoot rightRoot ftsSecret index lay
      leftCache rightCache hcache state fuel table
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hmessages
      (fun result => result ∈ support leftMessageRun) (fun result hresult => hresult)
  apply relTriple_bind hsupported
  intro leftResult rightResult hresult
  rcases hresult with ⟨hrelation, hleftSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingNativeSameRel] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingNativeSameRel] at hrelation
      | some rightResult =>
          rcases hrelation with ⟨hstate, hremaining, htable, _hmessage, hnextCache⟩
          have hactual := hmessageRoot leftResult hleftSupport
          simp only
          rw [← hstate, ← hremaining, ← htable, hactual]
          exact rootEncodingNativeRelates_maskedOtsLayerAfterMessage parameter index lay
            hnotBottom leftRoot rightRoot leftResult.value.2 rightResult.value.2 hnextCache
              leftResult.context leftResult.remaining leftResult.table

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_native_maskedSignLayer_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hmessageRoot : layerMessagePosition index lay = target → ∀ result,
      some result ∈ support (runResolvedFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)) →
      result.value.1 = leftRoot) :
    RelTriple
      (runResolvedFromTable state fuel table
        ((maskedSignLayer parameter ftsSecret index lay).run leftCache))
      (runResolvedFromTable state fuel table
        ((maskedSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay).run
          rightCache))
      (RootEncodingNativeSameRel parameter target leftRoot rightRoot) := by
  by_cases htarget : layerMessagePosition index lay = target
  · rw [maskedSignLayerWithTargetComparison, if_pos htarget]
    rw [← htarget] at hcache ⊢
    exact relTriple_native_maskedSignLayer_comparisonRoot_of_message parameter ftsSecret index lay
      (layer_ne_bottom_of_layerMessagePosition_isLayerRoot htarget hroot) leftRoot rightRoot
      leftCache rightCache hcache state fuel table (hmessageRoot htarget)
  · rw [maskedSignLayerWithTargetComparison, if_neg htarget]
    exact (rootEncodingNativeCouples_maskedSignLayer_of_layerMessagePosition_ne parameter target
      leftRoot rightRoot ftsSecret index lay htarget).relates leftCache rightCache hcache
        state fuel table

theorem rootEncodingNativeRelatesStored_maskedSignLayer_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay) := by
  intro leftCache rightCache hcache state fuel table hstored
  have hbase := relTriple_native_maskedSignLayer_targetComparison parameter target hroot leftRoot
    rightRoot ftsSecret index lay leftCache rightCache hcache state fuel table
      (fun htarget result hresult =>
        maskedLayerMessage_value_eq_of_stored_native parameter ftsSecret target hroot leftRoot
          index lay state leftCache fuel table result hstored htarget hresult)
  exact relTriple_native_rootEncoding_add_stored parameter target leftRoot rightRoot
    (maskedSignLayer parameter ftsSecret index lay)
    (maskedSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay)
    leftCache rightCache state fuel table hbase hstored

end SphincsSecurity.Concrete.OtsProbeSimulation
