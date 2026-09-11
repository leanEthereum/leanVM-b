import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def authenticationHashCost (lay : Layer) : Nat :=
  ∑ level : Fin maxLayerHeight, if level.val < layerHeight lay then 296 * 2 ^ level.val - 1 else 0

def layerMessageHashCost (lay : Layer) : Nat :=
  if hbelow : lay.val + 1 < numLayers then
    296 * 2 ^ layerHeight ⟨lay.val + 1, hbelow⟩ - 1
  else 28659

end SphincsSecurity.Concrete
