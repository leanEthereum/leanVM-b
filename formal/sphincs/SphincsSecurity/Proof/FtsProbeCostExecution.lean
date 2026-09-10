import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeCostSigning
import SphincsSecurity.Proof.FtsProbeSampling

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem probeCostInvariant_probingRomImpl (parameter : PublicParameter) (input : OracleWorld.Domain) :
    ProbeCostInvariant parameter (probingRomImpl parameter input) := by
  cases input with
  | inl n => exact probeCostInvariant_splitUniformImpl parameter n
  | inr input => exact probeCostInvariant_probingHashQuery parameter input

theorem probeCostInvariant_maskedExpandedAdversaryImpl (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) :
    ProbeCostInvariant secretKey.parameter
      (maskedExpandedAdversaryImpl secretKey.parameter secretKey input) := by
  cases input with
  | inl input => exact probeCostInvariant_probingRomImpl secretKey.parameter input
  | inr request => exact probeCostInvariant_maskedSigningImpl secretKey request

theorem probeCostInvariant_simulateQ_maskedExpandedAdversaryImpl {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbeCostInvariant secretKey.parameter
      (simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact ProbeCostInvariant.pure secretKey.parameter value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      exact (probeCostInvariant_maskedExpandedAdversaryImpl secretKey input).bind ih

theorem probeCostInvariant_maskedRetainedGameAfterSecrets (adversary : Adversary)
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    ProbeCostInvariant parameter (maskedRetainedGameAfterSecrets adversary parameter otsSecret) := by
  unfold maskedRetainedGameAfterSecrets
  apply (probeCostInvariant_simulateQ_ordinaryHashImpl parameter _ fun table =>
    ordinaryOnly_treeRoot parameter table topLayer rootTree (otsSecret topLayer rootTree)).bind
  intro root
  exact (probeCostInvariant_simulateQ_maskedExpandedAdversaryImpl
    (⟨parameter, root, otsSecret, fun _ _ _ => 0⟩ : SecretKey) _).bind fun result =>
      ProbeCostInvariant.pure parameter (root, result)

theorem runCharged_maskedRetainedGameAfterSecrets_cost_le_cache (adversary : Adversary)
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) (hit : Bool) (state : AdaptiveRevealProbe.State Coordinate)
    (value : RetainedGameResult) (cache : SplitHashCache) (cost : Nat)
    (hresult : (.done hit state (value, cache), cost) ∈ support
      (AdaptiveRevealProbe.runCharged table AdaptiveRevealProbe.State.empty q
        ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache))) :
    ProbeCacheCovered parameter state cache ∧ (splitProbeInputs parameter cache).Finite ∧
      cost ≤ (splitProbeInputs parameter cache).ncard := by
  have hempty : splitProbeInputs parameter emptySplitHashCache = ∅ := by
    ext input
    simp [splitProbeInputs, probeCachedInputs, emptySplitHashCache]
  have hbound := probeCostInvariant_maskedRetainedGameAfterSecrets adversary parameter otsSecret
    table AdaptiveRevealProbe.State.empty emptySplitHashCache q (probeCacheCovered_empty parameter)
    (by rw [hempty]; exact Set.finite_empty) hit state value cache cost hresult
  simpa only [hempty, Set.ncard_empty, Nat.zero_add] using hbound

end SphincsSecurity.Concrete.FtsProbeSimulation
