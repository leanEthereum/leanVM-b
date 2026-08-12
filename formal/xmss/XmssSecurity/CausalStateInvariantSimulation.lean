import XmssSecurity.CausalStateInvariantSteps
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def eagerCausalXmssRomImpl
    (table : ChainValueIndex → Digest) :
    QueryImpl OracleWorld (StateT CausalHashState ProbComp) :=
  fun input state =>
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalXmssRomImpl input).run state)

theorem simulate_eagerImpl_causalUniformImpl_support_revealsAgree
    (table : ChainValueIndex → Digest) (n : Nat)
    (state : CausalHashState) (result : Fin (n + 1) × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalUniformImpl n).run state))) :
    CausalRevealsAgree table result.2 := by
  unfold causalUniformImpl at hresult
  rw [OracleComp.liftM_run_StateT, simulateQ_bind] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨value, _hvalue, hpure⟩ := hresult
  simp only [simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact hagrees

theorem eagerCausalXmssRomImpl_preservesRevealsAgree
    (table : ChainValueIndex → Digest) :
    QueryImpl.PreservesInv (eagerCausalXmssRomImpl table)
      (CausalRevealsAgree table) := by
  intro input state hagrees result hresult
  cases input with
  | inl n =>
      exact simulate_eagerImpl_causalUniformImpl_support_revealsAgree
        table n state result hagrees hresult
  | inr input =>
      exact simulate_eagerImpl_causalHashQuery_support_revealsAgree
        table input state result hagrees hresult

theorem simulate_eagerImpl_simulate_causalXmssRomImpl_support_revealsAgree
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α) (state : CausalHashState)
    (result : α × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ causalXmssRomImpl computation).run state))) :
    CausalRevealsAgree table result.2 := by
  have hcollapse := simulateQ_StateT_compose
    causalXmssRomImpl (RevealProbeOracleSimulation.eagerImpl table)
    (eagerCausalXmssRomImpl table) (fun _ _ => rfl) computation state
  rw [hcollapse] at hresult
  exact OracleComp.simulateQ_run_preservesInv
    (eagerCausalXmssRomImpl table) (CausalRevealsAgree table)
    (eagerCausalXmssRomImpl_preservesRevealsAgree table)
    computation state hagrees result hresult

end XmssSecurity
