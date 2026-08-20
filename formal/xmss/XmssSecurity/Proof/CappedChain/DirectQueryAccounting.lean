import XmssSecurity.Proof.CappedChain.SourceDirectTrace

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def directHashActionCost :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inr _) => 1
  | _ => 0

@[simp]
theorem attackerActionFragment_hashInputs_length
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs.length =
      directHashActionCost input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput <;> rfl
  · rfl

def verifierHashQueryCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

theorem sourceDirectTracedMappedAdversaryImpl_support_info
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support
      ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        state)) :
    result.1 ∈ support
        (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) ∧
      result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hprojected : baseResult.1 ∈ support
      ((sourceDirectMappedAdversaryImpl publicKey secretKey input).run'
        state.1) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨baseResult, hbaseResult, rfl⟩
  have hsource : baseResult.1 ∈ support
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) := by
    rw [sourceDirectMappedAdversaryImpl_eq_compose] at hprojected
    exact OracleComp.support_simulateQ_run'_subset romImpl
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) state.1
        hprojected
  exact ⟨hsource, rfl⟩

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedMappedAdversary_residual_hashQueryBound
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β) (queries : Nat)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation >>=
        finish).IsQueryBoundP (· matches .inr _) queries)
    (cache : QueryCache HashSpec)
    (result : α × SourceTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (cache, []))) :
    result.2.2.hashInputs.length ≤ queries ∧
      (finish result.1).IsQueryBoundP (· matches .inr _)
        (queries - result.2.2.hashInputs.length) := by
  rw [sourceDirectTracedMappedAdversaryImpl_run_eq] at hresult
  rw [support_map] at hresult
  obtain ⟨rawResult, hrawResult, heq⟩ := hresult
  have hprojected : rawResult.1 ∈ support
      ((simulateQ romImpl
        ((simulateQ
          (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
            computation).run)).run' cache) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨rawResult, hrawResult, rfl⟩
  have hsource : rawResult.1 ∈ support
      ((simulateQ
        (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run) :=
    OracleComp.support_simulateQ_run'_subset romImpl
      ((simulateQ
        (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run) cache hprojected
  have hresidual := sourceActionTracedMappedAdversary_residual_hashQueryBound
    publicKey secretKey computation finish queries hbound rawResult.1 hsource
  have hresultValue : result.1 = rawResult.1.1 := by
    simpa using congrArg Prod.fst heq.symm
  have hresultTrace : result.2.2 = rawResult.1.2 := by
    simpa using congrArg (fun candidate => candidate.2.2) heq.symm
  rw [hresultValue, hresultTrace]
  exact hresidual

end XmssSecurity.CappedChain
