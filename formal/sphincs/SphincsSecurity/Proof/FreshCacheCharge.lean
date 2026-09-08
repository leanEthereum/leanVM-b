import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity.Concrete

open OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def freshCacheCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then 1 else 0

end SphincsSecurity.Concrete
