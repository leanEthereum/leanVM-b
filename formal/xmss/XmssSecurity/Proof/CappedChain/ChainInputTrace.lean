import XmssSecurity.Proof.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.ChainInputTrace
import XmssSecurity.Proof.PublicRootUniformity
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

@[simp]
theorem sourceUnloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) :
    sourceUnloggedMappedAdversaryImpl publicKey secretKey (.inl input) =
      liftM (OracleWorld.query input) := by
  cases input <;> rfl

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

theorem sourceActionTracedMappedAdversary_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Prod.fst <$>
        (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run =
      simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation := by
  exact QueryImpl.fst_map_run_withTraceAppend
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
    attackerActionFragment computation

theorem sourceActionTracedMappedAdversary_log_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (fun result => (result.1, result.2.toSigningLog)) <$>
        (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run =
      (simulateQ
        ((sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
          signingLogFragment) computation).run := by
  let project : {γ : Type} →
      WriterT AttackerActionTrace (OracleComp OracleWorld) γ →
        WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) γ :=
    fun {_γ} traced => WriterT.mk
      ((fun result => (result.1, result.2.toSigningLog)) <$> traced.run)
  have hpure : ∀ {γ : Type} (value : γ),
      project (pure value) = pure value := by
    intro γ value
    apply WriterT.ext
    simp [project, AttackerActionTrace.toSigningLog]
  have hbind : ∀ {γ δ : Type}
      (first : WriterT AttackerActionTrace (OracleComp OracleWorld) γ)
      (next : γ → WriterT AttackerActionTrace (OracleComp OracleWorld) δ),
      project (first >>= next) = project first >>= fun value => project (next value) := by
    intro γ δ first next
    apply WriterT.ext
    change (fun result => (result.1, result.2.toSigningLog)) <$> (first >>= next).run =
      (project first >>= fun value => project (next value)).run
    rw [WriterT.run_bind', WriterT.run_bind']
    simp only [project, WriterT.run_mk, map_bind]
    rw [bind_map_left]
    apply bind_congr
    rintro ⟨value, trace⟩
    simp [map_eq_bind_pure_comp, bind_assoc,
      AttackerActionTrace.toSigningLog_append]
  have happly : ∀ input,
      project (sourceActionTracedMappedAdversaryImpl publicKey secretKey input) =
        (sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
          signingLogFragment input := by
    intro input
    apply WriterT.ext
    simp [project, sourceActionTracedMappedAdversaryImpl,
      attackerActionFragment_toSigningLog]
  have hsimulation :
      project (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
        computation) =
      simulateQ
        ((sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
          signingLogFragment) computation := by
    induction computation using OracleComp.inductionOn with
    | pure value => exact hpure value
    | query_bind input next ih =>
        rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query,
          simulateQ_spec_query, hbind, happly]
        exact bind_congr ih
  simpa [project] using congrArg WriterT.run hsimulation

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

theorem sourceActionTracedMappedAdversary_hashInputs_length_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation)
        |>.IsQueryBoundP (· matches .inr _) q)
    (result : α × AttackerActionTrace)
    (hmem : result ∈ support
      (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
        computation).run) :
    result.2.hashInputs.length ≤ q := by
  induction computation using OracleComp.inductionOn generalizing q result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      simp [AttackerActionTrace.hashInputs]
  | query_bind input next ih =>
      rw [simulateQ_query_bind] at hbound
      rw [simulateQ_query_bind, WriterT.run_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨output, firstTrace⟩, hfirst, hrestMapped⟩ := hmem
      rw [support_map] at hrestMapped
      obtain ⟨restResult, hrest, heq⟩ := hrestMapped
      simp only [OracleQuery.input_query] at hbound hfirst hrest
      simp only [monadLift_self] at hbound
      have hfirstInfo := sourceActionTracedMappedAdversaryImpl_query_support
        publicKey secretKey input (output, firstTrace) hfirst
      have hfirstTrace : firstTrace = attackerActionFragment input output :=
        hfirstInfo.2
      have htrace : result.2 = firstTrace ++ restResult.2 := by
        simpa using congrArg Prod.snd heq.symm
      let continuation := fun response =>
        simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
          (next ((OracleSpec.query input).cont response))
      have hstepBound :
          (liftM (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) >>=
            continuation)
            |>.IsQueryBoundP (· matches .inr _) q := by
        exact hbound
      have hrestBound := sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
        publicKey secretKey input continuation q hstepBound output hfirstInfo.1
      have hlength := ih ((OracleSpec.query input).cont output)
        (q - (attackerActionFragment input output).hashInputs.length)
        hrestBound.2 restResult hrest
      rw [htrace, hfirstTrace, AttackerActionTrace.hashInputs_append,
        List.length_append]
      omega

noncomputable def sourceActionTracedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    OracleComp OracleWorld ((Forgery × Bool) × AttackerActionTrace) := do
  let result ←
    (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run
  let verified ← Concrete.scheme.verify publicKey result.1.epoch result.1.message
    result.1.signature
  return ((result.1, verified), result.2)

theorem sourceActionTracedDetailedGameAfterKeygen_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    Prod.fst <$>
        sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey =
      sourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey := by
  let tracedAdversary :=
    (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run
  let unloggedAdversary :=
    simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) := fun forgery => do
    let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
      forgery.signature
    return (forgery, verified)
  have hprojection : Prod.fst <$> tracedAdversary = unloggedAdversary :=
    sourceActionTracedMappedAdversary_projection publicKey secretKey
      (adversary.main publicKey)
  have hbridge := congrArg (fun computation => computation >>= finish) hprojection
  simpa [sourceActionTracedDetailedGameAfterKeygen,
    sourceUnloggedDetailedGameAfterKeygen, tracedAdversary, unloggedAdversary,
    finish, bind_map_left, map_bind, bind_assoc] using hbridge

theorem sourceActionTracedDetailedGameAfterKeygen_log_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (fun result =>
      ⟨publicKey, secretKey, result.1.1, result.2.toSigningLog, result.1.2⟩) <$>
        sourceActionTracedDetailedGameAfterKeygen adversary publicKey secretKey =
      detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey := by
  let tracedAdversary :=
    (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run
  let loggedAdversary :=
    (simulateQ
      ((sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment) (adversary.main publicKey)).run
  let finishLogged : Forgery × QueryLog SigningSpec → OracleComp OracleWorld GameOutcome :=
    fun result => do
      let verified ← Concrete.scheme.verify publicKey result.1.epoch result.1.message
        result.1.signature
      pure ⟨publicKey, secretKey, result.1, result.2, verified⟩
  have hprojection :
      (fun result => (result.1, result.2.toSigningLog)) <$> tracedAdversary =
        loggedAdversary :=
    sourceActionTracedMappedAdversary_log_projection publicKey secretKey
      (adversary.main publicKey)
  have hbridge := congrArg (fun computation => computation >>= finishLogged) hprojection
  rw [detailedGameAfterKeygen, ←
    sourceUnloggedMappedAdversaryImpl_withTraceAppend_eq]
  simpa [sourceActionTracedDetailedGameAfterKeygen, tracedAdversary,
    loggedAdversary, finishLogged, bind_map_left, map_bind, bind_assoc] using hbridge

theorem Concrete.verify_hashQueryBound_positive
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) (q : Nat)
    (hbound : (Concrete.scheme.verify publicKey epoch message signature)
      |>.IsQueryBoundP (· matches .inr _) q) :
    0 < q := by
  change (liftM (Concrete.verify publicKey epoch message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool)
      |>.IsQueryBoundP (· matches .inr _) q at hbound
  simp only [Concrete.verify, Concrete.encodingHash, Concrete.tweakableHash,
    Concrete.oracleHash, HasQuery.instOfMonadLift_query] at hbound
  exact hbound.1.resolve_left (by simp)

theorem sourceActionTracedDetailedGameAfterKeygen_hashInputs_length_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (result : ((Forgery × Bool) × AttackerActionTrace))
    (hresult : result ∈ support
      (sourceActionTracedDetailedGameAfterKeygen adversary keyResult.1.1
        keyResult.1.2)) :
    result.2.hashInputs.length ≤ q := by
  have hsource := sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    q adversary hbound keyResult hkeyResult
  unfold sourceUnloggedDetailedGameAfterKeygen at hsource
  have hadversaryBound :
      (simulateQ (sourceUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        (adversary.main keyResult.1.1)).IsQueryBoundP (· matches .inr _) q :=
    OracleComp.IsQueryBoundP.of_bind_left hsource
  unfold sourceActionTracedDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨adversaryResult, hadversaryResult, hfinish⟩ := hresult
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨verified, _hverified, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact sourceActionTracedMappedAdversary_hashInputs_length_le
    keyResult.1.1 keyResult.1.2 (adversary.main keyResult.1.1) q
    hadversaryBound adversaryResult hadversaryResult

/-- A completed post-keygen execution reserves at least one hash query for verification. -/
theorem sourceActionTracedDetailedGameAfterKeygen_hashInputs_length_lt
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (result : ((Forgery × Bool) × AttackerActionTrace))
    (hresult : result ∈ support
      (sourceActionTracedDetailedGameAfterKeygen adversary keyResult.1.1
        keyResult.1.2)) :
    result.2.hashInputs.length < q := by
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) := fun forgery =>
    Prod.mk forgery <$> Concrete.scheme.verify keyResult.1.1 forgery.epoch
      forgery.message forgery.signature
  have hsource := sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    q adversary hbound keyResult hkeyResult
  have hfull :
      (simulateQ (sourceUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        (adversary.main keyResult.1.1) >>= finish)
          |>.IsQueryBoundP (· matches .inr _) q := by
    unfold sourceUnloggedDetailedGameAfterKeygen at hsource
    change (simulateQ
      (sourceUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        (adversary.main keyResult.1.1) >>= finish)
          |>.IsQueryBoundP (· matches .inr _) q at hsource
    exact hsource
  unfold sourceActionTracedDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨adversaryResult, hadversaryResult, _hfinish⟩ := hresult
  have hresidual := sourceActionTracedMappedAdversary_residual_hashQueryBound
    keyResult.1.1 keyResult.1.2 (adversary.main keyResult.1.1) finish q
    hfull adversaryResult hadversaryResult
  have hverifyBound :
      (Concrete.scheme.verify keyResult.1.1 adversaryResult.1.epoch
        adversaryResult.1.message adversaryResult.1.signature)
          |>.IsQueryBoundP (· matches .inr _)
            (q - adversaryResult.2.hashInputs.length) := by
    unfold finish at hresidual
    exact OracleComp.IsQueryBoundP.of_bind_left hresidual.2
  have hpositive := Concrete.verify_hashQueryBound_positive keyResult.1.1
    adversaryResult.1.epoch adversaryResult.1.message adversaryResult.1.signature
    (q - adversaryResult.2.hashInputs.length) hverifyBound
  have htrace : result.2 = adversaryResult.2 := by
    rw [mem_support_bind_iff] at _hfinish
    obtain ⟨verified, _hverified, hpure⟩ := _hfinish
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    exact congrArg Prod.snd hpure
  rw [htrace]
  omega

end XmssSecurity.CappedChain
