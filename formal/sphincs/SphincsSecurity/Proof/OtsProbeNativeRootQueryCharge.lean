import SphincsSecurity.Proof.Prelude
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

theorem direct_add_rootEncodingQueryCharge_le_refinedReserve
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input + rootEncodingQueryCharge secretKey cache input ≤
      otsOpeningRefinedQueryReserve secretKey cache input :=
  (add_le_add le_rfl (rootEncodingQueryCharge_le_remainingReserve secretKey cache input)).trans_eq
    (direct_add_remaining_otsQueryReserve secretKey cache input)

end OtsProbeSimulation
end Concrete
end SphincsSecurity
