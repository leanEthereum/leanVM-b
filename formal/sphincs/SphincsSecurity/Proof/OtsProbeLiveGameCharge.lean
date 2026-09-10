import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveJointCharge
import SphincsSecurity.Proof.OtsProbeLiveNativeComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeChronologicalRetainedComputation
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate) (RetainedRestResult × SplitHashCache) := do
  let (root, cache) ← maskedPublishedTreeRoot.run emptySplitHashCache
  (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (retainedGameRestComputation adversary ⟨root, parameter⟩)).run cache

theorem expectedLiveNativeProbeCharge_root_eq_zero
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge (maskedPublishedTreeRoot.run cache) context fuel table = 0 := by
  have hraw : expectedResolvedQueryCharge nativeProbeQueryCharge (maskedPublishedTreeRoot.run cache) context fuel table ≤ (0 : ENNReal) := by
    simpa only [Nat.cast_zero] using expectedResolvedProbeCharge_le_probeBound _ 0 context fuel table (maskedPublishedTreeRoot_probeFree cache)
  exact le_antisymm ((expectedLiveResolvedQueryCharge_le_raw nativeProbeQueryCharge _ context fuel table).trans hraw) zero_le

end SphincsSecurity.Concrete.OtsProbeSimulation
