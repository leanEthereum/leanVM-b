import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.NormalizedTargetCacheQuery
import SphincsSecurity.Proof.TargetMixedGrowthPolynomial
import SphincsSecurity.Proof.TargetSigningMatchFactors

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetMixedSigningGrowth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  (normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups -
    normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups) *
      normalizedTargetLogProduct key after log payload target required

noncomputable def newTargetMixedGrowthWeight (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (source : FewTimeView) : ENNReal :=
  targetMixedGrowthPolynomial
    (fun slot => normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot))
    (normalizedTargetLogMatch key before log payload target) groups required target source

end SphincsSecurity.Concrete
