import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveNativeReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def directOtsQueryCharge (parameter : PublicParameter) (_cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  otsHashInputCharge parameter input * (4 / 3)

noncomputable def remainingOtsQueryReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  otsOpeningRefinedQueryReserve secretKey cache input - directOtsQueryCharge secretKey.parameter cache input

theorem directOtsQueryCharge_le_refinedReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  exact weightedOtsOuterQueryCharge_le_refinedReserve secretKey (.inl (.inr input)) cache

theorem direct_add_remaining_otsQueryReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input + remainingOtsQueryReserve secretKey cache input =
      otsOpeningRefinedQueryReserve secretKey cache input := by
  unfold remainingOtsQueryReserve
  exact add_tsub_cancel_of_le (directOtsQueryCharge_le_refinedReserve secretKey cache input)

theorem remainingOtsQueryReserve_eq_refined_of_not_ots
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hnot : ¬∃ position : Position, IsOtsPosition position ∧ AtPosition secretKey.parameter input position) :
    remainingOtsQueryReserve secretKey cache input = otsOpeningRefinedQueryReserve secretKey cache input := by
  simp [remainingOtsQueryReserve, directOtsQueryCharge, otsHashInputCharge, hnot]

theorem otsOuterQueryCharge_hash (parameter : PublicParameter) (input : HashInput) :
    otsOuterQueryCharge parameter (.inl (.inr input)) = otsHashInputCharge parameter input := rfl

theorem outerHashQueryCharge_hash (charge : QueryCache HashSpec → HashInput → ENNReal)
    (input : HashInput) (cache : QueryCache HashSpec) :
    outerHashQueryCharge charge (.inl (.inr input)) cache = charge cache input := rfl

theorem directOtsQueryCharge_eq (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge parameter cache input = otsHashInputCharge parameter input * (4 / 3 : ENNReal) := rfl

theorem weightedOtsOuterQueryCharge_le_directCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    otsOuterQueryCharge parameter input * (4 / 3 : ENNReal) ≤
      outerHashQueryCharge (directOtsQueryCharge parameter) input cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact (zero_mul (4 / 3 : ENNReal)).le
      | inr input => rw [otsOuterQueryCharge_hash, outerHashQueryCharge_hash, directOtsQueryCharge_eq]
  | inr message => exact (zero_mul (4 / 3 : ENNReal)).le

theorem expectedLiveChronologicalOtsCharge_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal)) computation context fuel table cache ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  let secretKey : SecretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hbound : expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal)) computation context fuel table cache ≤
      expectedOuterQueryCharge secretKey (directOtsQueryCharge parameter) computation actualCache := by
    exact expectedLiveNativeOuterCharge_le_actualOuterCharge parameter root table ftsSecret
      (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal))
      (directOtsQueryCharge parameter)
      (reachableResolvedCouples_chronologicalNative_concrete parameter root table ftsSecret)
      (weightedOtsOuterQueryCharge_le_directCharge parameter)
      computation context fuel cache actualCache hinvariant hvisible hpublished
  exact hbound.trans (expectedOuterQueryCharge_le_expanded secretKey (directOtsQueryCharge parameter) computation actualCache)

theorem expectedLiveChronologicalOtsCount_mul_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (otsOuterQueryCharge parameter) computation context fuel table cache * (4 / 3 : ENNReal) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  rw [← expectedLiveNativeOuterCharge_mul]
  exact expectedLiveChronologicalOtsCharge_le_directCharge parameter root table ftsSecret computation context fuel cache actualCache
    hinvariant hvisible hpublished

end SphincsSecurity.Concrete.OtsProbeSimulation
