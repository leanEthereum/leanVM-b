import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.NormalizedTargetCacheQuery
import SphincsSecurity.Proof.Fts.TargetSigningMatchFactors
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetMixedMoment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    normalizedTargetLogProduct key cache log payload target required

end SphincsSecurity.Concrete
