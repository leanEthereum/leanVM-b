import SphincsSecurity.Proof.ParentReserveQueryConservation
import SphincsSecurity.Proof.StoppedPotentialConservation

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition parentReserve freshParentReserveCharge releasedParentQueryCharge exceptionDiscardCharge
set_option backward.isDefEq.respectTransparency false

theorem expected_stoppedParentReserve_add_discard_releases_eq_funding
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (eligible : Position → Prop)
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] *
      (if result.2 then 0 else (parentReserve parameter otsSecret ftsSecret eligible result.1.2 : ENNReal))) +
      expectedPreExceptionCharge exception (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache hit +
      expectedPreExceptionCharge exception (exceptionDiscardCharge exception
        (fun current => (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal))) computation cache hit =
      (if hit then 0 else (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal)) +
        expectedPreExceptionCharge exception (freshParentReserveCharge parameter otsSecret ftsSecret eligible) computation cache hit := by
  rw [add_assoc, ← expectedPreExceptionCharge_add]
  apply expected_runExceptionMonitor_potential_add_preCharge_eq
    exception (fun current stopped => if stopped then 0 else (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal))
    _ _ _ computation cache hfinite hit
  intro query current hcurrent stopped
  exact expected_stoppedPotential_add_discard_release_step exception
    (fun current => (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal))
    (releasedParentQueryCharge parameter otsSecret ftsSecret eligible)
    (freshParentReserveCharge parameter otsSecret ftsSecret eligible) current query stopped
    (romImpl_parentReserve_add_released parameter otsSecret ftsSecret eligible current hcurrent query)

end SphincsSecurity
