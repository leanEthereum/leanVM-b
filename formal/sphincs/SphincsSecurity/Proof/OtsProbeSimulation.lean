import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.ForgeryClassify
import SphincsSecurity.Proof.Honest
import SphincsSecurity.Proof.SecretProbe
import SphincsSecurity.Proof.SigningTrace

/-!
# Opaque one-time chain values

The lazy one-time simulation gives a separate opaque cell to every chain start and every structural
oracle answer. An ordinary chain query probes the value at its starting digit. A leaf query probes
chain zero's endpoint, which is the only endpoint needed by the fresh-opening extraction; a backward
opening always starts strictly before the endpoint and is therefore caught by a chain query.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

inductive Coordinate where
  | chainStart (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (chainIdx : ChainIndex)
  | position (position : Position)

structure Probe where
  coordinate : Coordinate
  candidate : Digest

noncomputable def Probe.target (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : Probe) : Digest :=
  match probe.coordinate with
  | .chainStart lay tree leafIdx chainIdx => otsSecret lay tree leafIdx chainIdx
  | .position position => honestValue f parameter otsSecret ftsSecret position

theorem chainProbeInput_eq_iff (parameter : PublicParameter)
    (leftLay rightLay : Layer) (leftTree rightTree : TreeIndex)
    (leftLeaf rightLeaf : LeafIndex) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftCandidate rightCandidate : Digest) :
    tweakableHashInput parameter
        (.chain leftLay leftTree leftLeaf leftChain leftStep) (digestBytes leftCandidate) =
      tweakableHashInput parameter
        (.chain rightLay rightTree rightLeaf rightChain rightStep) (digestBytes rightCandidate) ↔
      leftLay = rightLay ∧ leftTree = rightTree ∧ leftLeaf = rightLeaf ∧
        leftChain = rightChain ∧ leftStep = rightStep ∧ leftCandidate = rightCandidate := by
  constructor
  · intro heq
    have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
    simp only [HashDomain.chain.injEq] at hparts
    exact ⟨hparts.1.1, hparts.1.2.1, hparts.1.2.2.1, hparts.1.2.2.2.1,
      hparts.1.2.2.2.2, digestBytes_injective hparts.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem chainProbeInput_ne_leafInput (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) (candidate : Digest)
    (leafLay : Layer) (leafTree : TreeIndex) (leaf : LeafIndex) (payload : HashInput) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step)
        (digestBytes candidate) ≠
      tweakableHashInput parameter (.leaf leafLay leafTree leaf) payload := by
  intro heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simp at hdomain

theorem leafInput_domain_eq (parameter : PublicParameter)
    (leftLay rightLay : Layer) (leftTree rightTree : TreeIndex)
    (leftLeaf rightLeaf : LeafIndex) (leftPayload rightPayload : HashInput)
    (heq : tweakableHashInput parameter (.leaf leftLay leftTree leftLeaf) leftPayload =
      tweakableHashInput parameter (.leaf rightLay rightTree rightLeaf) rightPayload) :
    leftLay = rightLay ∧ leftTree = rightTree ∧ leftLeaf = rightLeaf := by
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simpa only [HashDomain.leaf.injEq] using hdomain

noncomputable def decodePosition? (parameter : PublicParameter) (input : HashInput) :
    Option Position := by
  classical
  exact if hexists : ∃ position : Position, AtPosition parameter input position then
    some hexists.choose
  else none

inductive SplitHashKey where
  | ordinary (input : HashInput)
  | hidden (coordinate : Coordinate)

abbrev SplitHashCache := SplitHashKey → Option HashOutput

def emptySplitHashCache : SplitHashCache := fun _ => none

noncomputable def tableValue (table : Coordinate → HashOutput)
    (position : Position) : Digest :=
  truncateHash (table (.position position))

noncomputable def tableOtsSecret (table : Coordinate → HashOutput) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leafIdx chainIdx =>
    truncateHash (table (.chainStart lay tree leafIdx chainIdx))

noncomputable def tablePayload (table : Coordinate → HashOutput) :
    Position → HashInput
  | position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        digestBytes (truncateHash (table (.chainStart lay tree leafIdx chainIdx)))
      else
        (position.children.map (tableValue table)).flatMap digestBytes
  | position => (position.children.map (tableValue table)).flatMap digestBytes

noncomputable def tableInput (parameter : PublicParameter)
    (table : Coordinate → HashOutput) : Coordinate → HashInput
  | .chainStart _ _ _ _ => []
  | .position position =>
      tweakableHashInput parameter position.domain (tablePayload table position)

noncomputable def completedSplitHashCache (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) : SplitHashCache
  | .ordinary input => cache (.ordinary input)
  | .hidden coordinate =>
      match cache (.hidden coordinate) with
      | some output => some output
      | none => if coordinate ∈ ensured then some (table coordinate) else none

noncomputable def mergeDecodedPosition (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) (input : HashInput) : Option Position → Option HashOutput
  | some position@(.chain _ _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | some position@(.leaf _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | some position@(.node _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | _ => cache (.ordinary input)

noncomputable def mergedCache (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) : QueryCache HashSpec :=
  fun input => mergeDecodedPosition parameter table ensured cache input
    (decodePosition? parameter input)

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

def signingTraceComputation
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    OracleComp (OracleWorld + SigningSpec) (alpha × QueryLog SigningSpec) :=
  OracleComp.construct
    (C := fun _ => OracleComp (OracleWorld + SigningSpec)
      (alpha × QueryLog SigningSpec))
    (fun value => pure (value, []))
    (fun input _next recursivelyTrace => do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      let result ← recursivelyTrace output
      pure (result.1, signingLogFragment input output ++ result.2))
    computation

theorem simulateQ_withTraceAppend_run_eq_signingTraceComputation
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (OracleWorld + SigningSpec) m)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    (simulateQ (QueryImpl.withTraceAppend handler signingLogFragment)
        computation).run =
      simulateQ handler (signingTraceComputation computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih => simp [signingTraceComputation, ih]

noncomputable def liftOracleWorldLeft
    (computation : OracleComp OracleWorld alpha) :
    OracleComp (OracleWorld + SigningSpec) alpha := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  exact liftM computation

theorem simulateQ_liftOracleWorldLeft
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (left : QueryImpl OracleWorld m) (right : QueryImpl SigningSpec m)
    (computation : OracleComp OracleWorld alpha) :
    simulateQ (left + right) (liftOracleWorldLeft computation) =
      simulateQ left computation := by
  unfold liftOracleWorldLeft
  exact QueryImpl.simulateQ_add_liftM_left left right computation

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

end SphincsSecurity.Concrete.OtsProbeSimulation
