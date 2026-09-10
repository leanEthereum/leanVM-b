import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingTarget
import SphincsSecurity.Proof.TerminalView

/-!
# Encoding chronology in the viewed terminal game

The generic final-continuation classifier is instantiated with the exact adversary state and verifier run retained by the observational game.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem ViewedEncodingCollisionWitness.encodingBad
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result) :
    EncodingBad result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ := by
  obtain ⟨f, digest, hf, hvalid, hnovel, hdigest, hadmissible, hcollision⟩ := hwitness
  exact hcollision.encodingBad hf

theorem encodingBad_mk_root_iff
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (cache : QueryCache HashSpec) (leftRoot rightRoot : Digest) :
    EncodingBad cache ⟨parameter, leftRoot, otsSecret, ftsSecret⟩ ↔
      EncodingBad cache ⟨parameter, rightRoot, otsSecret, ftsSecret⟩ := by
  rfl

end Concrete

end SphincsSecurity
