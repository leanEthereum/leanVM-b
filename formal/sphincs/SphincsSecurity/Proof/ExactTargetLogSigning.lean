import SphincsSecurity.Proof.DigestCompletionLogGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expected_signWithView_normalizedTargetLogProduct_le_of_exactReuse (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
        (Fintype.card Index : ENNReal)⁻¹ * (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * reuse := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log payload target required hsigned reuse hreuse

end SphincsSecurity.Concrete
