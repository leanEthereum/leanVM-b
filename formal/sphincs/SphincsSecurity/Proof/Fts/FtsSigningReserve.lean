import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Bytes

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem tweakableHashInput_tag_eq (parameter : PublicParameter) (first second : HashDomain)
    (firstPayload secondPayload : HashInput)
    (heq : tweakableHashInput parameter first firstPayload = tweakableHashInput parameter second secondPayload) :
    (hashDomainFields first).tag = (hashDomainFields second).tag := by
  simp only [tweakableHashInput] at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact congrArg TweakFields.tag (tweakBytes_eq_iff.mp htweak)

end SphincsSecurity.Concrete.FtsProbeSimulation
