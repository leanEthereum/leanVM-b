import SphincsSecurity.Proof.AdaptiveChainEndpoint
import SphincsSecurity.Proof.ReferenceFamilyGame

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] chainWalk
noncomputable local instance : DecidableEq (QueryImpl HashSpec Id) := Classical.decEq _

noncomputable def otsChainFunctions (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin steps → Digest → Digest :=
  fun step value => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + step.val) 1 value)

theorem otsChainFunctions_tail (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin.tail (otsChainFunctions parameter lay tree leaf chainIdx start (steps + 1) f) =
      otsChainFunctions parameter lay tree leaf chainIdx (start + 1) steps f := by
  funext step value
  simp only [Fin.tail, otsChainFunctions, Fin.val_succ, Nat.add_right_comm start 1 step.val,
    Nat.add_assoc]

theorem otsChainFunctions_apply (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id)
    (step : Fin steps) (hstep : start + step.val < chainLength - 1) (value : Digest) :
    otsChainFunctions parameter lay tree leaf chainIdx start steps f step value =
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx ⟨start + step.val, hstep⟩)
        (digestBytes value))) := by
  simp only [otsChainFunctions, chainWalk, Nat.add_zero, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    dif_pos hstep, eval_tweakableHash]

theorem otsChainFunctions_evaluate (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) (value : Digest) :
    PartialChainEndpoint.evaluate (otsChainFunctions parameter lay tree leaf chainIdx start steps f) value =
      evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps generalizing start value with
  | zero => simp only [PartialChainEndpoint.evaluate, chainWalk, evalWithAnswerFn_pure]
  | succ steps ih =>
      rw [PartialChainEndpoint.evaluate, otsChainFunctions_tail, ih]
      change evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + 1) steps
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start 1 value))) = _
      simpa only [Nat.add_comm 1 steps] using
        (eval_chainWalk_add f parameter lay tree leaf chainIdx start 1 steps value).symm

noncomputable def otsPrefixPreimages (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (f : QueryImpl HashSpec Id) (endpoint : Digest) : Nat :=
  EndpointPreimageDensity.preimages
    (fun oracle value => PartialChainEndpoint.evaluate (otsChainFunctions parameter lay tree leaf chainIdx 0 digit.val oracle) value)
    f endpoint

theorem otsPrefixPreimages_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (f : QueryImpl HashSpec Id) (endpoint : Digest) :
    otsPrefixPreimages parameter lay tree leaf chainIdx digit f endpoint =
      (Finset.univ.filter (fun value =>
        evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value) = endpoint)).card := by
  simp only [otsPrefixPreimages, EndpointPreimageDensity.preimages, otsChainFunctions_evaluate]

theorem otsPrefix_endpoint_density (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (prior : PMF (QueryImpl HashSpec Id))
    (f : QueryImpl HashSpec Id) (endpoint : Digest) :
    EndpointPreimageDensity.real prior
        (fun oracle value => evalWithAnswerFn oracle (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)) (f, endpoint) =
      (otsPrefixPreimages parameter lay tree leaf chainIdx digit f endpoint : ENNReal) *
        EndpointPreimageDensity.ideal prior (f, endpoint) := by
  classical
  rw [EndpointPreimageDensity.real_density, otsPrefixPreimages_eq]
  rfl

theorem otsPrefix_partial_likelihood_lower (digit : Digit)
    (observed : Fin digit.val → Digest → Option Digest) (endpoint : Digest) (budget : Nat)
    (hbudget : PartialChainEndpoint.queryCount observed ≤ budget) :
    1 - (budget : ENNReal) / (2 ^ 128 : Nat) ≤ PartialChainEndpoint.meanPreimages observed endpoint := by
  simpa only [show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using
    PartialChainEndpoint.meanPreimages_ge_budget observed endpoint budget hbudget

theorem otsPrefix_adaptive_cost_lower {AuxIndex Result : Type} {auxSpec : OracleSpec AuxIndex} (digit : Digit)
    (auxiliary : Digest → QueryImpl auxSpec PMF)
    (computation : Digest → OracleComp (auxSpec + PartialChainEndpoint.PrefixSpec digit.val Digest) Result)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery budget)
    (payoff : Digest × (Result × (Fin digit.val → Digest → Option Digest)) → ENNReal) :
    (1 - (budget : ENNReal) / (2 ^ 128 : Nat)) *
        (∑' result, PartialChainEndpoint.idealRun auxiliary computation (fun _ _ => none) result * payoff result) ≤
      ∑' result, PartialChainEndpoint.realRun auxiliary computation (fun _ _ => none) result * payoff result := by
  simpa only [show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using
    PartialChainEndpoint.realRun_empty_cost_lower auxiliary computation budget hbound payoff

end SphincsSecurity.Concrete
