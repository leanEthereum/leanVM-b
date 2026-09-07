import SphincsSecurity.Proof.FewTimeCoverageGrowth
import SphincsSecurity.Proof.CachedSignerCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedFewTimeCoverageGrowth (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) (source : FewTimeView) : ENNReal :=
  newlyCoveredFewTimeTargetCount (cachedAdmissibleMessageInputs parameter cache hfinite)
    (fixedSigningViews parameter cache root log) (cachedFewTimeView cache) source

theorem cachedCoveredFewTimeTargetCount_eq_zero (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hclean : ¬ SigningCacheCovered parameter root cache log) :
    coveredFewTimeTargetCount (cachedAdmissibleMessageInputs parameter cache hfinite)
      (fixedSigningViews parameter cache root log) (cachedFewTimeView cache) = 0 := by
  apply Finset.sum_eq_zero
  intro target htarget
  apply if_neg
  intro hcovered
  obtain ⟨hdomain, output, houtput, hadmissible⟩ := (Finset.mem_filter.mp htarget).2
  have hview : cachedFewTimeView cache target = hashOutputFewTimeView output := by
    simp only [cachedFewTimeView, houtput, Option.getD_some]
  rw [hview] at hcovered
  exact hclean ⟨target, output, hdomain, houtput, hadmissible, hcovered⟩

theorem expected_cachedFewTimeCoverageGrowth_eq (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * cachedFewTimeCoverageGrowth parameter root cache hfinite log source) =
      ∑ target ∈ cachedAdmissibleMessageInputs parameter cache hfinite,
        completionProbability (fixedSigningViews parameter cache root log target) (cachedFewTimeView cache target) :=
  expected_newlyCoveredFewTimeTargetCount_eq _ _ _

theorem expected_cachedCoveredFewTimeTargetCount_insert_eq (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hclean : ¬ SigningCacheCovered parameter root cache log) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      coveredFewTimeTargetCount (cachedAdmissibleMessageInputs parameter cache hfinite)
        (fun target => insertFewTimeView (fixedSigningViews parameter cache root log target) source) (cachedFewTimeView cache)) =
      ∑ target ∈ cachedAdmissibleMessageInputs parameter cache hfinite,
        completionProbability (fixedSigningViews parameter cache root log target) (cachedFewTimeView cache target) := by
  rw [expected_coveredFewTimeTargetCount_insert_eq, cachedCoveredFewTimeTargetCount_eq_zero parameter root cache hfinite log hclean, zero_add]

theorem observedSignerCoverCharge_eq_expectedGrowth (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) (q : Nat) :
    observedSignerCoverCharge key message cache hfinite log q =
      expectedQueryCharge (freshCoverageCharge key.parameter (fixedSigningViews key.parameter cache key.root log))
        (signWithView key message) cache * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * cachedFewTimeCoverageGrowth key.parameter key.root cache hfinite log source) +
      cachedMessageEntryCountWhere cache key.parameter key.root message
        (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
          (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) * digestReuseWeight q := by
  rw [expected_cachedFewTimeCoverageGrowth_eq]
  rfl

theorem probEvent_signerCacheCover_le_expectedGrowth (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ SigningCacheCovered key.parameter key.root cache log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SignerCacheCover key message log | (simulateQ romImpl (signWithView key message)).run cache] ≤
      expectedQueryCharge (freshCoverageCharge key.parameter (fixedSigningViews key.parameter cache key.root log))
        (signWithView key message) cache * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * cachedFewTimeCoverageGrowth key.parameter key.root cache hfinite log source) +
      cachedMessageEntryCountWhere cache key.parameter key.root message
        (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
          (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) * digestReuseWeight q := by
  rw [← observedSignerCoverCharge_eq_expectedGrowth]
  exact probEvent_signerCacheCover_le_charge key message cache hfinite log hsigned hclean q hq hcache

end SphincsSecurity.Concrete
