import SphincsSecurity.Proof.SelectedSigningReserve
import SphincsSecurity.Proof.FreshSignerCacheView
import SphincsSecurity.Proof.ExceptionWitness
import SphincsSecurity.Proof.JointProbeOriginalParentFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_signingReserve_ge_newAdmissible_survival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hit : Bool) (P : FewTimeView → Prop) :
    (28504 : ENNReal) * Pr[fun result => NewAdmissibleSignerView cache key P result.1 ∧ result.2 = false |
      runExceptionMonitor exception (signWithView key message) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  apply le_trans ?_ (expected_signingReserve_ge_selected_survival exception key message cache hit)
  apply mul_le_mul' le_rfl
  apply probEvent_mono
  intro result hresult hevent
  obtain ⟨payload, output, hbefore, hafter, hadmissible, _⟩ := hevent.1
  obtain ⟨randomness, index, leaves, loopCache, hloop, hpayload, hview, hselected⟩ :=
    signWithView_new_admissible_selected key message cache result.1.2 result.1.1.1 result.1.1.2
      (runExceptionMonitor_support_project exception (signWithView key message) cache hit hresult)
      payload output hbefore hafter hadmissible
  exact ⟨by simp [hview], hevent.2⟩

theorem expected_signingReserve_ge_newTarget_survival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hit : Bool) (P : FewTimeView → Prop) :
    (28504 : ENNReal) * Pr[fun result =>
      (∃ payload output, cache (tweakableHashInput key.parameter .message payload) = none ∧
        result.1.2 (tweakableHashInput key.parameter .message payload) = some output ∧
        Admissible (truncateMessageDigest output) ∧ P (hashOutputFewTimeView output)) ∧ result.2 = false |
      runExceptionMonitor exception (sign key message) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  have hcost := expected_signingReserve_ge_newAdmissible_survival exception key message cache hit P
  conv_lhs => rw [← signWithView_fst key message, runExceptionMonitor_map, probEvent_map]
  simpa only [Function.comp_def, NewAdmissibleSignerView] using hcost

end SphincsSecurity.Concrete.FtsProbeSimulation
