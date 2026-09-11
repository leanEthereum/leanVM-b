import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SignerAdmissibleMessage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_new_payload_eq_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message randomness := by
  obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
  have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
  exact hpayload.trans (congrArg _ hrandomness.symm)

end SphincsSecurity.Concrete
