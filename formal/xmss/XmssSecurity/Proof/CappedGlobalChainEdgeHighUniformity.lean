import XmssSecurity.Proof.CappedGlobalChainPresampling
import XmssSecurity.Proof.HashOutputHigh

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def globalChainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  match cache (globalChainTableEdgeInput parameter table edge) with
  | none => 0
  | some output => XmssSecurity.hashOutputHigh output

def globalChainEdgeOutputFromHigh
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashOutput :=
  Rom.hashOutputEquivDigestPair.symm
    (high edge, globalChainTableEdgeTarget table edge)

theorem globalChainEdgeOutputFromHigh_eq_cached
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (output : HashOutput)
    (hcache : cache (globalChainTableEdgeInput parameter table edge) =
      some output)
    (htarget : truncateHash output = globalChainTableEdgeTarget table edge) :
    globalChainEdgeOutputFromHigh
        (globalChainEdgeHighTableOfCache cache parameter table) table edge =
      output := by
  simp [globalChainEdgeOutputFromHigh, globalChainEdgeHighTableOfCache,
    hcache, XmssSecurity.hashOutputHigh, ← htarget]
  exact Rom.hashOutputEquivDigestPair.symm_apply_apply output

theorem globalChainEdgeHighTableOfCache_mono
    (cache larger : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    globalChainEdgeHighTableOfCache cache parameter table =
      globalChainEdgeHighTableOfCache larger parameter table := by
  funext edge
  obtain ⟨output, hcache, _htarget⟩ := hmatches edge
  have hlarger := hle hcache
  simp [globalChainEdgeHighTableOfCache, hcache, hlarger]

end XmssSecurity.CappedChain
