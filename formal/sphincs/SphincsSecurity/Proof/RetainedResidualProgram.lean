import SphincsSecurity.Proof.RetainedResidualExecution

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def currentRouting (inputs : Finset HashInput) : OracleComp (World inputs) Routing :=
  liftM ((World inputs).query (.inl .routing))

def signingTranscript (inputs : Finset HashInput) : OracleComp (World inputs) (QueryLog SigningSpec) :=
  liftM ((World inputs).query (.inl .transcript))

def recordSigning (inputs : Finset HashInput) (message : Message) (result : SigningRecord) : OracleComp (World inputs) Unit :=
  liftM ((World inputs).query (.inl (.record message result)))

noncomputable def externalProgram {Result : Type} (inputs : Finset HashInput) (parameter : PublicParameter)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (computation : OracleComp OracleWorld Result) :
    OracleComp (World inputs) Result := do
  let routing ← currentRouting inputs
  simulateQ (embed inputs routing) (simulateQ (ResidualByteFrontend.checkedTranslate inputs
    (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)) computation)

noncomputable def signingProgram (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) : OracleComp (World inputs) (Option Signature) := do
  let routing ← currentRouting inputs
  let result ← simulateQ (embed inputs routing)
    (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)
  let _ ← recordSigning inputs message result
  pure result.1.1

noncomputable def adversaryImpl (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp (World inputs))
  | .inl input => externalProgram inputs parameter words selections (liftM (OracleWorld.query input))
  | .inr message => signingProgram inputs parameter root words selections message

noncomputable def restProgram (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (adversary : Adversary) : OracleComp (World inputs) Bool := do
  let forgery ← simulateQ (adversaryImpl inputs parameter root words selections) (adversary.main ⟨root, parameter⟩)
  let log ← signingTranscript inputs
  let checked ← externalProgram inputs parameter words selections
    (liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature : OracleComp HashSpec Bool))
  pure (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && checked)

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem observedRun_routing_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (next : Routing → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (currentRouting inputs >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next state.memory.routing) state := by
  rw [currentRouting, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun]

theorem observedRun_record_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (message : Message) (result : SigningRecord) (next : Unit → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (recordSigning inputs message result >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next ()) { state with memory := state.memory.recordSigning message result } := by
  rw [recordSigning, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun]

theorem observedRun_signingProgram (actual : Labels) (seed : inputs → HashOutput)
    (root : Digest) (message : Message) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (signingProgram inputs parameter root words selections message) state =
      (observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs parameter root state.memory.routing.known words selections message)) state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun record =>
          pure (some record.1.1, { result.2 with memory := result.2.memory.recordSigning message record }))) := by
  rw [signingProgram, observedRun_routing_bind, observedRun_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨record, after⟩
  cases record with
  | none => rfl
  | some record =>
      rw [Option.elim_some, observedRun_record_bind]
      exact runWith_pure _ _ _

theorem observedRun_signingProgram_project (actual : Labels) (seed : inputs → HashOutput)
    (root : Digest) (message : Message) (state : State inputs) :
    projectResult <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (signingProgram inputs parameter root words selections message) state =
      (fun result => (result.1.map (fun record : SigningRecord => record.1.1), result.2)) <$>
        observedRun (ResidualByteFrontend.prefixEnvironment parameter inputs hencoding words state.memory.routing.disclosed
          state.memory.routing.known publicReplies selections rows) actual seed
          (ResidualByteFrontend.jointSigningProgram inputs parameter root state.memory.routing.known words selections message) (project state) := by
  rw [observedRun_signingProgram, map_bind,
    ← observedRun_embed parameter inputs hencoding words publicReplies selections rows state.memory.routing actual seed]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨record, after⟩
  cases record <;> simp only [Option.elim_none, Option.elim_some, pure_bind, projectResult, project,
    Option.map_none, Option.map_some, Memory.recordSigning]

theorem restProgram_posterior (root : Digest) (adversary : Adversary) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (UniformTableCompletion.complete state.candidates >>= fun actual =>
      ResidualTableCompletion.completeRows state.rows >>= fun seed =>
        retain actual seed <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows)
          actual seed (restProgram inputs parameter root words selections adversary) state) =
      (lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (restProgram inputs parameter root words selections adversary) state >>= finish) :=
  AdaptiveResidualLabels.run_posterior _ _ state ha

theorem restProgram_erasure (root : Digest) (adversary : Adversary) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (UniformTableCompletion.complete state.candidates >>= fun actual =>
      ResidualTableCompletion.completeRows state.rows >>= fun seed =>
        observedRun (environment parameter inputs hencoding words publicReplies selections rows)
          actual seed (restProgram inputs parameter root words selections adversary) state) =
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (restProgram inputs parameter root words selections adversary) state :=
  AdaptiveResidualLabels.run_erasure _ _ state ha

end SphincsSecurity.Concrete.RetainedResidual
