import SphincsSecurity.Proof.Charge

/-!
# Extraction hits are bad

The extraction lemmas state collisions in the notation of the concrete hash computation. These
adapters identify their structural position and turn a cached hit at a settled position into `Bad`.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

theorem bad_of_chainHit (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (position : Nat)
    (hposition : position < chainLength - 1) (payload : Digest)
    (hhit : ChainHit f parameter lay tree leafIdx chainIdx
      (otsSecret lay tree leafIdx chainIdx) position hposition payload)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩))
    (hcached : cache (tweakableHashInput parameter
      (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩) (digestBytes payload)) ≠ none) :
    Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hsettled
    (hcached := hcached)
  · simpa only [honestPayload] using fun h => hhit.1 (digestBytes_injective h)
  · simpa only [Position.domain, honestValue_chain] using hhit.2

theorem bad_of_leafHit (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (payload : HashInput)
    (hhit : LeafHit f parameter lay tree (otsSecret lay tree) leafIdx payload)
    (hsettled : Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx))
    (hcached : cache (tweakableHashInput parameter (.leaf lay tree leafIdx) payload) ≠ none) :
    Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hsettled
    (hcached := hcached)
  · exact hhit.1
  · simpa only [Position.domain, honestValue_leaf] using hhit.2

theorem bad_of_nodeHit (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hnodeIdx : nodeIdx < 2 ^ maxLayerHeight) (payload : HashInput)
    (hhit : NodeHit f parameter lay tree (otsSecret lay tree) level nodeIdx payload)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩))
    (hcached : cache (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload)
      ≠ none) : Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hsettled
    (hcached := hcached)
  · exact hhit.1
  · simpa only [Position.domain, honestValue_node] using hhit.2

theorem bad_of_ftsLeafHit (hf : cache.AgreesWithFn f) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (candidate : Digest)
    (hhit : FtsLeafHit f parameter index tree (ftsSecret index tree) leafIdx candidate)
    (hsettled : Settled parameter otsSecret ftsSecret cache (.ftsLeaf index tree leafIdx))
    (hcached : cache (tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
      (digestBytes candidate)) ≠ none) : Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hsettled
    (hcached := hcached)
  · simpa only [honestPayload] using fun h => hhit.1 (digestBytes_injective h)
  · simpa only [Position.domain, honestValue_ftsLeaf] using hhit.2

theorem bad_of_ftsNodeHit (hf : cache.AgreesWithFn f) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) (hlevel : level < ftsTreeHeight)
    (hnodeIdx : nodeIdx < 2 ^ ftsTreeHeight) (payload : HashInput)
    (hhit : FtsNodeHit f parameter index tree (ftsSecret index tree) level nodeIdx payload)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩))
    (hcached : cache (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
      payload) ≠ none) : Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hsettled
    (hcached := hcached)
  · exact hhit.1
  · simpa only [Position.domain, honestValue_ftsNode] using hhit.2

end Concrete

end SphincsSecurity
