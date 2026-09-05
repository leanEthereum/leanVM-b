import SphincsSecurity.Proof.OtsProbeNativeRootReserve

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal

theorem expectedQueryCharge_mono
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (hle : ∀ cache input, left cache input ≤ right cache input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedQueryCharge left computation cache ≤ expectedQueryCharge right computation cache := by
  calc
    _ ≤ expectedQueryCharge left computation cache +
        expectedQueryCharge (fun cache input => right cache input - left cache input) computation cache := le_self_add
    _ = expectedQueryCharge (fun cache input => left cache input + (right cache input - left cache input)) computation cache :=
      (expectedQueryCharge_add _ _ computation cache).symm
    _ = _ := by
      congr 1
      funext cache input
      exact add_tsub_cancel_of_le (hle cache input)

namespace Concrete

theorem sampledQueryCharge_mono
    (left right : SecretKey → QueryCache HashSpec → HashInput → ENNReal)
    (hle : ∀ secretKey cache input, left secretKey cache input ≤ right secretKey cache input)
    (adversary : Adversary) :
    sampledQueryCharge left adversary ≤ sampledQueryCharge right adversary := by
  unfold sampledQueryCharge
  apply ENNReal.tsum_le_tsum
  intro secrets
  exact mul_le_mul' le_rfl (expectedQueryCharge_mono _ _ (hle _) _ _)

namespace OtsProbeSimulation

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def rootEncodingQueryCharge (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if (∃ candidate, EncodingLayerRootCandidateAt secretKey.parameter input candidate) ∧
      (4 / 3 : ENNReal) ≤ remainingOtsQueryReserve secretKey cache input then 4 / 3 else 0

theorem rootEncodingQueryCharge_le_remainingReserve
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    rootEncodingQueryCharge secretKey cache input ≤ remainingOtsQueryReserve secretKey cache input := by
  unfold rootEncodingQueryCharge
  split_ifs with hcharge
  · exact hcharge.2
  · exact zero_le

theorem rootEncodingQueryCharge_eq_four_thirds
    {secretKey : SecretKey} (cache : QueryCache HashSpec) {input : HashInput} {candidate : Probe}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hreserve : (4 / 3 : ENNReal) ≤ remainingOtsQueryReserve secretKey cache input) :
    rootEncodingQueryCharge secretKey cache input = 4 / 3 := by
  unfold rootEncodingQueryCharge
  exact if_pos ⟨⟨candidate, hcandidate⟩, hreserve⟩

theorem rootEncodingQueryCharge_eq_zero_iff_insufficient
    {secretKey : SecretKey} (cache : QueryCache HashSpec) {input : HashInput} {candidate : Probe}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate) :
    rootEncodingQueryCharge secretKey cache input = 0 ↔ remainingOtsQueryReserve secretKey cache input < (4 / 3 : ENNReal) := by
  by_cases hreserve : (4 / 3 : ENNReal) ≤ remainingOtsQueryReserve secretKey cache input
  · rw [rootEncodingQueryCharge_eq_four_thirds cache hcandidate hreserve]
    simp only [not_lt_of_ge hreserve, iff_false]
    norm_num
  · have hlt := lt_of_not_ge hreserve
    simp [rootEncodingQueryCharge, hreserve, hlt]

theorem DeferredComputationsClosed.rootEncodingQueryCharge_eq_four_thirds
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target) (hvalue : context.positionValue target = some output) :
    rootEncodingQueryCharge secretKey actualCache input = 4 / 3 :=
  SphincsSecurity.Concrete.OtsProbeSimulation.rootEncodingQueryCharge_eq_four_thirds actualCache hcandidate
    (hclosed.remainingReserve_of_encoding_candidate hinvariant hsecrets hcandidate hposition hvalue)

theorem rootEncodingQueryCharge_eq_four_thirds_of_native_matching_query
    (secretKey : SecretKey) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (ordinaryCache : QueryCache HashSpec)
    (initialState finalState : ViewedFullTraceState)
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache finalState.cache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) (value : α)
    (hrun : (value, (finalState, false)) ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey)
        ((OracleWorld + SigningSpec).query (.inl (.inr input)) >>= next)).run (initialState, false))) :
    rootEncodingQueryCharge secretKey initialState.cache input = 4 / 3 := by
  have hroot := hclosed.root_settled_value hinvariant secretKey.ftsSecret lay tree output hvalue
  have hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalState.cache (layerRootPosition lay tree) := by
    simpa only [hsecrets] using hroot.1
  have hrootValue : honestValue (fromCache finalState.cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (layerRootPosition lay tree) = truncateHash output := by
    simpa only [hsecrets] using hroot.2
  apply rootEncodingQueryCharge_eq_four_thirds initialState.cache hcandidate
  rw [hcandidate.remainingReserve_eq_refined (secretKey := secretKey) initialState.cache]
  exact hcandidate.refinedReserve_of_prehitFree_viewed_matching_query secretKey
    hposition hsettled (hmatch.trans hrootValue.symm) next value hrun

theorem direct_add_rootEncodingQueryCharge_le_refinedReserve
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input + rootEncodingQueryCharge secretKey cache input ≤
      otsOpeningRefinedQueryReserve secretKey cache input :=
  (add_le_add le_rfl (rootEncodingQueryCharge_le_remainingReserve secretKey cache input)).trans_eq
    (direct_add_remaining_otsQueryReserve secretKey cache input)

theorem sampled_direct_add_rootEncodingQueryCharge_le_refinedReserve (adversary : Adversary) :
    sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary +
      sampledQueryCharge rootEncodingQueryCharge adversary ≤ sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  rw [← sampledQueryCharge_add]
  exact sampledQueryCharge_mono _ _ direct_add_rootEncodingQueryCharge_le_refinedReserve adversary

theorem sampledInitializedNativeDirectRisk_add_rootEncodingCharge_le_refinedReserve
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q +
      sampledQueryCharge rootEncodingQueryCharge adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add le_rfl (mul_le_mul' (sampledQueryCharge_mono _ _ rootEncodingQueryCharge_le_remainingReserve adversary) le_rfl)).trans
  exact sampledInitializedNativeDirectRisk_add_remaining_le_refinedReserve targets adversary fuel q hq

end OtsProbeSimulation
end Concrete
end SphincsSecurity
