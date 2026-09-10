import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveContextCharge
import SphincsSecurity.Proof.OtsProbeNativeRootQueryCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def KnownHiddenEncodingRootQuery (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : Prop :=
  ∃ (candidate : Probe) (target : Position) (output : HashOutput),
    EncodingLayerRootCandidateAt parameter input candidate ∧ candidate.coordinate = .position target ∧
      context.positionValue target = some output ∧ .position target ∉ context.state.revealed

noncomputable def knownEncodingRootOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => if KnownHiddenEncodingRootQuery parameter input context then 4 / 3 else 0
  | _ => 0

theorem knownEncodingRootOuterCharge_le_actualRootCharge
    (secretKey : SecretKey) (table : OtsSecretIndex → HashOutput)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context (ordinaryQueryCache cache) actualCache)
    (hcomputed : DeferredComputationsClosed context) :
    knownEncodingRootOuterCharge secretKey.parameter input context fuel cache ≤
      outerHashQueryCharge (rootEncodingQueryCharge secretKey) input actualCache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => simp [knownEncodingRootOuterCharge, outerHashQueryCharge, hashQueryCharge]
      | inr input =>
          rw [outerHashQueryCharge_hash]
          simp only [knownEncodingRootOuterCharge]
          split_ifs with hknown
          · obtain ⟨candidate, target, output, hcandidate, hposition, hvalue, _hhidden⟩ := hknown
            rw [hcomputed.rootEncodingQueryCharge_eq_four_thirds hinvariant hsecrets hcandidate hposition hvalue]
          · exact zero_le
  | inr message => simp [knownEncodingRootOuterCharge, outerHashQueryCharge]

theorem expectedLiveKnownRootCharge_le_actualRootCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (knownEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedQueryCharge
        (rootEncodingQueryCharge
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hbound : expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (knownEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedOuterQueryCharge secretKey (rootEncodingQueryCharge secretKey) computation actualCache :=
    expectedLiveNativeContextCharge_le_actualOuterCharge parameter root table ftsSecret
      (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (knownEncodingRootOuterCharge parameter)
      (rootEncodingQueryCharge secretKey)
      (reachableResolvedCouples_chronologicalNative_concrete parameter root table ftsSecret)
      (knownEncodingRootOuterCharge_le_actualRootCharge secretKey table rfl)
      computation context fuel cache actualCache hinvariant hvisible hpublished hcomputed
  exact hbound.trans (expectedOuterQueryCharge_le_expanded secretKey (rootEncodingQueryCharge secretKey) computation actualCache)

end SphincsSecurity.Concrete.OtsProbeSimulation
