import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.InterleavedCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ValidSigningStep (log : QueryLog SigningSpec) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl _ => log.length ≤ signatureLimit
  | .inr _ => log.length < signatureLimit

noncomputable def validInterleavedCoverStepCharge (key : SecretKey) (q : Nat)
    (state : CoverLogState) (input : (OracleWorld + SigningSpec).Domain) : ENNReal :=
  if ValidSigningStep state.2 input then interleavedCoverStepCharge key q state input else 0

noncomputable def expectedValidInterleavedCoverCharge {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => validInterleavedCoverStepCharge key q state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedValidInterleavedCoverCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (value : α) (state : CoverLogState) : expectedValidInterleavedCoverCharge key q (pure value) state = 0 := rfl

end SphincsSecurity.Concrete
