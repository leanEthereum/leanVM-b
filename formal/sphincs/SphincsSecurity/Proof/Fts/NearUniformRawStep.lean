import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageDeficitConcentration

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def nearUniformDigestReuseWeight : ENNReal :=
  (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹

theorem exactDigestReuseWeight_le_near_uniform_of_clean_cache (key : SecretKey) (cache : QueryCache HashSpec)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ cap)
    (hclean : ¬ MessageDeficitExceptional key cache) (message : Message) :
    exactDigestReuseWeight key message cache ≤ nearUniformDigestReuseWeight :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message cache cap hcap hcache
    (le_of_not_gt (fun h => hclean ⟨message, h⟩))

end SphincsSecurity.Concrete
