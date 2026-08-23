import XmssSecurity.Proof.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.ChainInputTrace
import XmssSecurity.Proof.QueryBoundSupport

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev AttackerAction := XmssSecurity.AttackerAction

abbrev AttackerActionTrace := XmssSecurity.AttackerActionTrace

def AttackerAction.hashInput? : AttackerAction → Option HashInput
  | .hash input => some input
  | .sign _request _signature => none

def AttackerAction.signingEntry? :
    AttackerAction → Option ((_request : SignRequest) × Option Signature)
  | .hash _ => none
  | .sign request signature => some ⟨request, signature⟩

def AttackerActionTrace.hashInputs (trace : AttackerActionTrace) : List HashInput :=
  trace.filterMap AttackerAction.hashInput?

@[simp]
theorem AttackerActionTrace.hashInputs_append
    (left right : AttackerActionTrace) :
    (left ++ right).hashInputs = left.hashInputs ++ right.hashInputs := by
  simp [AttackerActionTrace.hashInputs]

def AttackerActionTrace.toSigningLog
    (trace : AttackerActionTrace) : QueryLog SigningSpec :=
  trace.filterMap AttackerAction.signingEntry?

@[simp]
theorem AttackerActionTrace.toSigningLog_append
    (left right : AttackerActionTrace) :
    (left ++ right).toSigningLog = left.toSigningLog ++ right.toSigningLog := by
  simp [AttackerActionTrace.toSigningLog]

def attackerActionFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : AttackerActionTrace :=
  match input with
  | .inl (.inl _) => []
  | .inl (.inr hashInput) => [.hash hashInput]
  | .inr request => [.sign request output]

@[simp]
theorem attackerActionFragment_uniform
    (index : unifSpec.Domain) (output : unifSpec.Range index) :
    attackerActionFragment (.inl (.inl index)) output = [] := rfl

@[simp]
theorem attackerActionFragment_hash (input : HashInput) (output : HashOutput) :
    attackerActionFragment (.inl (.inr input)) output = [.hash input] := rfl

@[simp]
theorem attackerActionFragment_sign
    (request : SignRequest) (signature : Option Signature) :
    attackerActionFragment (.inr request) signature = [.sign request signature] := rfl

@[simp]
theorem attackerActionFragment_hashInputs
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs =
      match input with
      | .inl (.inr hashInput) => [hashInput]
      | _ => [] := by
  cases input with
  | inl worldInput => cases worldInput <;> rfl
  | inr request => rfl

@[simp]
theorem attackerActionFragment_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).toSigningLog = signingLogFragment input output := by
  cases input with
  | inl worldInput => cases worldInput <;> rfl
  | inr request => rfl

noncomputable def sourceActionTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace (OracleComp OracleWorld)) :=
  (sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
    attackerActionFragment

theorem sourceActionTracedMappedAdversaryImpl_query_support
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (result : (OracleWorld + SigningSpec).Range input × AttackerActionTrace)
    (hmem : result ∈ support
      (sourceActionTracedMappedAdversaryImpl publicKey secretKey input).run) :
    result.1 ∈ support
        (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) ∧
      result.2 = attackerActionFragment input result.1 := by
  have hrun :
      (sourceActionTracedMappedAdversaryImpl publicKey secretKey input).run =
        (fun output => (output, attackerActionFragment input output)) <$>
          sourceUnloggedMappedAdversaryImpl publicKey secretKey input := by
    unfold sourceActionTracedMappedAdversaryImpl
    rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind']
    simp [WriterT.run_tell]
  rw [hrun, support_map] at hmem
  obtain ⟨output, houtput, heq⟩ := hmem
  subst result
  exact ⟨houtput, rfl⟩

theorem sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp OracleWorld α)
    (q : Nat)
    (hbound : (liftM
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) >>= next)
      |>.IsQueryBoundP (· matches .inr _) q)
    (output : (OracleWorld + SigningSpec).Range input)
    (houtput : output ∈ support
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input)) :
    (attackerActionFragment input output).hashInputs.length ≤ q ∧
      (next output).IsQueryBoundP (· matches .inr _)
        (q - (attackerActionFragment input output).hashInputs.length) := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          change unifSpec.Range uniformInput at output
          change unifSpec.Range uniformInput → OracleComp OracleWorld α at next
          change (liftM (OracleWorld.query (.inl uniformInput)) >>= next)
            |>.IsQueryBoundP (· matches .inr _) q at hbound
          rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
          constructor
          · simp [AttackerActionTrace.hashInputs]
          · simpa [AttackerActionTrace.hashInputs] using hbound.2 output
      | inr hashInput =>
          change HashOutput at output
          change HashOutput → OracleComp OracleWorld α at next
          change (liftM (OracleWorld.query (.inr hashInput)) >>= next)
            |>.IsQueryBoundP (· matches .inr _) q at hbound
          rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
          have hpositive : 0 < q := hbound.1.resolve_left (by simp)
          have hcost :
              (attackerActionFragment (.inl (.inr hashInput)) output).hashInputs.length = 1 :=
            rfl
          rw [hcost]
          constructor
          · omega
          · exact hbound.2 output
  | inr request =>
      have hcost :
          (attackerActionFragment (.inr request) output).hashInputs.length = 0 := rfl
      rw [hcost, Nat.sub_zero]
      exact ⟨Nat.zero_le q,
        OracleComp.IsQueryBoundP.bind_right_of_mem_support hbound output houtput⟩

theorem sourceActionTracedMappedAdversary_residual_hashQueryBound
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β) (q : Nat)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation >>= finish)
        |>.IsQueryBoundP (· matches .inr _) q)
    (result : α × AttackerActionTrace)
    (hmem : result ∈ support
      (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
        computation).run) :
    result.2.hashInputs.length ≤ q ∧
      (finish result.1).IsQueryBoundP (· matches .inr _)
        (q - result.2.hashInputs.length) := by
  induction computation using OracleComp.inductionOn generalizing q result finish with
  | pure value =>
      simp only [simulateQ_pure, pure_bind] at hbound
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      simpa [AttackerActionTrace.hashInputs] using And.intro (Nat.zero_le q) hbound
  | query_bind input next ih =>
      rw [simulateQ_query_bind, bind_assoc] at hbound
      rw [simulateQ_query_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨output, firstTrace⟩, hfirst, hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      simp only [OracleQuery.input_query] at hbound hfirst hrest
      have hfirstInfo := sourceActionTracedMappedAdversaryImpl_query_support
        publicKey secretKey input (output, firstTrace) hfirst
      have hfirstTrace : firstTrace = attackerActionFragment input output :=
        hfirstInfo.2
      let continuation := fun response =>
        simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
          (next ((OracleSpec.query input).cont response)) >>= finish
      have hstepBound :
          (liftM (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) >>=
            continuation).IsQueryBoundP (· matches .inr _) q := by
        exact hbound
      have hrestBound := sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
        publicKey secretKey input continuation q hstepBound output hfirstInfo.1
      rw [← hfirstTrace] at hrestBound
      have hrec := ih ((OracleSpec.query input).cont output) finish
        (q - firstTrace.hashInputs.length)
        hrestBound.2 restResult hrest
      change (restResult.1, firstTrace ++ restResult.2) = result at heq
      subst result
      rw [AttackerActionTrace.hashInputs_append, List.length_append]
      constructor
      · omega
      · simpa only [Nat.sub_sub] using hrec.2

end XmssSecurity.CappedChain
