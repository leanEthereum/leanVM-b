import SphincsSecurity.Proof.OtsProbeResolvedPrivateCommutation

/-!
# Private structural samples through recursive resolution

Private position resolution commutes through the recursive structural resolvers while retaining
the resolver's observable output and exact failure behavior.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def resolvePositionThenChainPrefix
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (steps : Nat) (hsteps : steps ≤ chainLength - 1) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let targetResolved ← resolveDeferredPositionValue target context
  match targetResolved with
  | none => pure none
  | some targetResolved => do
      let prefixResolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        steps hsteps targetResolved.toDeferredContext
      match prefixResolved with
      | none => pure none
      | some prefixResolved =>
          pure (some ⟨prefixResolved.toDeferredContext, prefixResolved.output⟩)

noncomputable def resolveChainPrefixThenPosition
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (steps : Nat) (hsteps : steps ≤ chainLength - 1) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let prefixResolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
    steps hsteps context
  match prefixResolved with
  | none => pure none
  | some prefixResolved => do
      let targetResolved ←
        resolveDeferredPositionValue target prefixResolved.toDeferredContext
      match targetResolved with
      | none => pure none
      | some targetResolved =>
          pure (some ⟨targetResolved.toDeferredContext, prefixResolved.output⟩)

theorem evalDist_bind_eq_of_evalDist_eq
    {oa ob : ProbComp α} (h : evalDist oa = evalDist ob) (next : α → ProbComp β) :
    evalDist (oa >>= next) = evalDist (ob >>= next) := by
  rw [evalDist_bind, evalDist_bind, h]

noncomputable def resolveAfterRevealedPosition (position : Position) :
    Option RevealedResolution → ProbComp (Option RevealedResolution)
  | none => pure none
  | some previous => do
      let resolved ← resolveDeferredPositionValue position previous.context
      match resolved with
      | none => pure none
      | some resolved => pure (some ⟨resolved.toDeferredContext, resolved.output⟩)

set_option maxRecDepth 100000 in
theorem evalDist_resolvePosition_chainPrefix_comm
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context,
      context.Valid → DeferredCompletable table context →
      evalDist (resolvePositionThenChainPrefix target table lay tree leafIdx chainIdx
        steps hsteps context) =
      evalDist (resolveChainPrefixThenPosition target table lay tree leafIdx chainIdx
        steps hsteps context)
  | 0, hsteps, context, _hvalid, hcompletable => by
      change evalDist (resolvePositionThenChainStart target table
          ⟨lay, tree, leafIdx, chainIdx⟩ context) =
        evalDist (resolveChainStartThenPosition target table
          ⟨lay, tree, leafIdx, chainIdx⟩ context)
      exact evalDist_resolvePosition_chainStart_comm target table
        ⟨lay, tree, leafIdx, chainIdx⟩ context hcompletable
  | steps + 1, hsteps, context, hvalid, hcompletable => by
      let current : Position :=
        .chain lay tree leafIdx chainIdx ⟨steps, by omega⟩
      calc
        _ = evalDist (resolvePositionThenChainPrefix target table lay tree leafIdx chainIdx
              steps (by omega) context >>= resolveAfterRevealedPosition current) := by
          unfold resolvePositionThenChainPrefix
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro targetResolved _htargetResolved
          cases targetResolved with
          | none => simp [resolveAfterRevealedPosition]
          | some targetResolved =>
              simp only [resolveDeferredChainPrefix, bind_assoc]
              apply evalDist_bind_congr
              intro previous _hprevious
              cases previous <;> rfl
        _ = evalDist (resolveChainPrefixThenPosition target table lay tree leafIdx chainIdx
              steps (by omega) context >>= resolveAfterRevealedPosition current) :=
          evalDist_bind_eq_of_evalDist_eq
            (evalDist_resolvePosition_chainPrefix_comm target table lay tree leafIdx chainIdx
              steps (by omega) context hvalid hcompletable)
            (resolveAfterRevealedPosition current)
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps
              (by omega) context >>= fun previous =>
                match previous with
                | none => pure none
                | some previous =>
                    resolvePositionValuesInOrder target current previous.toDeferredContext) := by
          unfold resolveChainPrefixThenPosition
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro previous _hprevious
          cases previous with
          | none => rfl
          | some previous =>
              unfold resolveAfterRevealedPosition resolvePositionValuesInOrder
              simp only [bind_assoc]
              apply evalDist_bind_congr
              intro targetResolved _htargetResolved
              cases targetResolved <;> rfl
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps
              (by omega) context >>= fun previous =>
                match previous with
                | none => pure none
                | some previous =>
                    resolvePositionValuesSwapped target current previous.toDeferredContext) := by
          apply evalDist_bind_congr
          intro previous _hprevious
          cases previous with
          | none => rfl
          | some previous =>
              by_cases heq : target = current
              · simpa [heq] using
                  (evalDist_resolvePositionValues_comm_self current
                    previous.toDeferredContext)
              · exact evalDist_resolvePositionValues_comm_of_ne target current
                  previous.toDeferredContext heq
        _ = _ := by
          unfold resolveChainPrefixThenPosition
          simp only [resolveDeferredChainPrefix, bind_assoc]
          apply evalDist_bind_congr
          intro previous _hprevious
          cases previous with
          | none => rfl
          | some previous =>
              unfold resolvePositionValuesSwapped
              apply evalDist_bind_congr
              intro currentResolved _hcurrentResolved
              cases currentResolved <;> rfl

noncomputable def resolvePositionThenChains
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chains : List ChainIndex) (context : DeferredContext) :
    ProbComp (Option DeferredContext) := do
  let targetResolved ← resolveDeferredPositionValue target context
  match targetResolved with
  | none => pure none
  | some targetResolved =>
      resolveDeferredChains table lay tree leafIdx chains targetResolved.toDeferredContext

noncomputable def resolveChainsThenPosition
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chains : List ChainIndex) (context : DeferredContext) :
    ProbComp (Option DeferredContext) := do
  let chainsResolved ← resolveDeferredChains table lay tree leafIdx chains context
  match chainsResolved with
  | none => pure none
  | some chainsResolved => do
      let targetResolved ← resolveDeferredPositionValue target chainsResolved
      pure (targetResolved.map DeferredResolution.toDeferredContext)

noncomputable def continueChainsAfterRevealed
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chains : List ChainIndex) :
    Option RevealedResolution → ProbComp (Option DeferredContext)
  | none => pure none
  | some resolved =>
      resolveDeferredChains table lay tree leafIdx chains resolved.context

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_resolvePosition_chains_comm
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains context,
      context.Valid → DeferredCompletable table context →
      evalDist (resolvePositionThenChains target table lay tree leafIdx chains context) =
      evalDist (resolveChainsThenPosition target table lay tree leafIdx chains context)
  | [], context, _hvalid, _hcompletable => by
      unfold resolvePositionThenChains resolveChainsThenPosition
      simp only [resolveDeferredChains, pure_bind]
      apply evalDist_bind_congr
      intro targetResolved _htargetResolved
      cases targetResolved <;> rfl
  | chainIdx :: remaining, context, hvalid, hcompletable => by
      calc
        _ = evalDist (resolvePositionThenChainPrefix target table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>=
                continueChainsAfterRevealed table lay tree leafIdx remaining) := by
          unfold resolvePositionThenChains resolvePositionThenChainPrefix
            continueChainsAfterRevealed
          simp only [resolveDeferredChains, bind_assoc]
          apply evalDist_bind_congr
          intro targetResolved _htargetResolved
          cases targetResolved with
          | none => rfl
          | some targetResolved =>
              simp only
              rw [bind_assoc]
              apply evalDist_bind_congr
              intro prefixResolved _hprefixResolved
              cases prefixResolved <;> rfl
        _ = evalDist (resolveChainPrefixThenPosition target table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>=
                continueChainsAfterRevealed table lay tree leafIdx remaining) :=
          evalDist_bind_eq_of_evalDist_eq
            (evalDist_resolvePosition_chainPrefix_comm target table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context hvalid hcompletable)
            (continueChainsAfterRevealed table lay tree leafIdx remaining)
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>= fun prefixResolved =>
                match prefixResolved with
                | none => pure none
                | some prefixResolved =>
                    resolvePositionThenChains target table lay tree leafIdx remaining
                      prefixResolved.toDeferredContext) := by
          unfold resolveChainPrefixThenPosition continueChainsAfterRevealed
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro prefixResolved _hprefixResolved
          cases prefixResolved with
          | none => rfl
          | some prefixResolved =>
              simp only
              unfold resolvePositionThenChains
              simp only [bind_assoc]
              apply evalDist_bind_congr
              intro targetResolved _htargetResolved
              cases targetResolved <;> rfl
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>= fun prefixResolved =>
                match prefixResolved with
                | none => pure none
                | some prefixResolved =>
                    resolveChainsThenPosition target table lay tree leafIdx remaining
                      prefixResolved.toDeferredContext) := by
          apply evalDist_bind_congr
          intro prefixResolved hprefixResolved
          cases prefixResolved with
          | none => rfl
          | some prefixResolved =>
              exact evalDist_resolvePosition_chains_comm target table lay tree leafIdx remaining
                prefixResolved.toDeferredContext
                (hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
                  (chainLength - 1) (by omega) prefixResolved hprefixResolved)
                (hcompletable.of_resolveDeferredChainPrefix hvalid hprefixResolved)
        _ = _ := by
          unfold resolveChainsThenPosition
          simp only [resolveDeferredChains, bind_assoc]
          apply evalDist_bind_congr
          intro prefixResolved _hprefixResolved
          cases prefixResolved <;> rfl

noncomputable def resolveRevealedPositionAfterContext (position : Position) :
    Option DeferredContext → ProbComp (Option RevealedResolution)
  | none => pure none
  | some context => do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure none
      | some resolved => pure (some ⟨resolved.toDeferredContext, resolved.output⟩)

noncomputable def resolvePositionThenOtsLeaf
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) : ProbComp (Option RevealedResolution) := do
  let targetResolved ← resolveDeferredPositionValue target context
  match targetResolved with
  | none => pure none
  | some targetResolved => do
      let leafResolved ←
        resolveDeferredOtsLeaf table lay tree leafIdx targetResolved.toDeferredContext
      match leafResolved with
      | none => pure none
      | some leafResolved =>
          pure (some ⟨leafResolved.toDeferredContext, leafResolved.output⟩)

noncomputable def resolveOtsLeafThenPosition
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) : ProbComp (Option RevealedResolution) := do
  let leafResolved ← resolveDeferredOtsLeaf table lay tree leafIdx context
  match leafResolved with
  | none => pure none
  | some leafResolved => do
      let targetResolved ←
        resolveDeferredPositionValue target leafResolved.toDeferredContext
      match targetResolved with
      | none => pure none
      | some targetResolved =>
          pure (some ⟨targetResolved.toDeferredContext, leafResolved.output⟩)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_resolvePosition_otsLeaf_comm
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context) :
    evalDist (resolvePositionThenOtsLeaf target table lay tree leafIdx context) =
      evalDist (resolveOtsLeafThenPosition target table lay tree leafIdx context) := by
  let chains := List.ofFn fun chainIdx : ChainIndex => chainIdx
  let leaf : Position := .leaf lay tree leafIdx
  calc
    _ = evalDist (resolvePositionThenChains target table lay tree leafIdx chains context >>=
          resolveRevealedPositionAfterContext leaf) := by
      unfold resolvePositionThenOtsLeaf resolvePositionThenChains
        resolveRevealedPositionAfterContext
      simp only [resolveDeferredOtsLeaf, bind_assoc]
      apply evalDist_bind_congr
      intro targetResolved _htargetResolved
      cases targetResolved with
      | none => rfl
      | some targetResolved =>
          simp only
          dsimp only [chains, leaf]
          apply evalDist_bind_congr
          intro chainsResolved _hchainsResolved
          cases chainsResolved <;> rfl
    _ = evalDist (resolveChainsThenPosition target table lay tree leafIdx chains context >>=
          resolveRevealedPositionAfterContext leaf) :=
      evalDist_bind_eq_of_evalDist_eq
        (evalDist_resolvePosition_chains_comm target table lay tree leafIdx chains context
          hvalid hcompletable)
        (resolveRevealedPositionAfterContext leaf)
    _ = evalDist (resolveDeferredChains table lay tree leafIdx chains context >>=
          fun chainsResolved =>
            match chainsResolved with
            | none => pure none
            | some chainsResolved =>
                resolvePositionValuesInOrder target leaf chainsResolved) := by
      unfold resolveChainsThenPosition resolveRevealedPositionAfterContext
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro chainsResolved _hchainsResolved
      cases chainsResolved with
      | none => rfl
      | some chainsResolved =>
          simp only
          rw [bind_assoc]
          apply evalDist_bind_congr
          intro targetResolved _htargetResolved
          cases targetResolved <;> rfl
    _ = evalDist (resolveDeferredChains table lay tree leafIdx chains context >>=
          fun chainsResolved =>
            match chainsResolved with
            | none => pure none
            | some chainsResolved =>
                resolvePositionValuesSwapped target leaf chainsResolved) := by
      apply evalDist_bind_congr
      intro chainsResolved _hchainsResolved
      cases chainsResolved with
      | none => rfl
      | some chainsResolved =>
          by_cases heq : target = leaf
          · simpa [heq] using
              (evalDist_resolvePositionValues_comm_self leaf chainsResolved)
          · exact evalDist_resolvePositionValues_comm_of_ne target leaf chainsResolved heq
    _ = _ := by
      unfold resolveOtsLeafThenPosition resolvePositionValuesSwapped
      simp only [resolveDeferredOtsLeaf, bind_assoc]
      apply evalDist_bind_congr
      intro chainsResolved _hchainsResolved
      cases chainsResolved with
      | none => rfl
      | some chainsResolved =>
          apply evalDist_bind_congr
          intro leafResolved _hleafResolved
          cases leafResolved <;> rfl

abbrev PrivateResolver := DeferredContext → ProbComp (Option DeferredResolution)

noncomputable def composePrivateResolvers
    (first second : PrivateResolver) : PrivateResolver := fun context => do
  let firstResolved ← first context
  match firstResolved with
  | none => pure none
  | some firstResolved => second firstResolved.toDeferredContext

noncomputable def resolvePositionThenResolver
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let targetResolved ← resolveDeferredPositionValue target context
  match targetResolved with
  | none => pure none
  | some targetResolved => do
      let resolved ← resolver targetResolved.toDeferredContext
      match resolved with
      | none => pure none
      | some resolved => pure (some ⟨resolved.toDeferredContext, resolved.output⟩)

noncomputable def resolveResolverThenPosition
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let resolved ← resolver context
  match resolved with
  | none => pure none
  | some resolved => do
      let targetResolved ← resolveDeferredPositionValue target resolved.toDeferredContext
      match targetResolved with
      | none => pure none
      | some targetResolved =>
          pure (some ⟨targetResolved.toDeferredContext, resolved.output⟩)

def PositionResolutionCommutes
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) : Prop :=
  evalDist (resolvePositionThenResolver target resolver context) =
    evalDist (resolveResolverThenPosition target resolver context)

noncomputable def continueResolverAfterRevealed (resolver : PrivateResolver) :
    Option RevealedResolution → ProbComp (Option RevealedResolution)
  | none => pure none
  | some previous => do
      let resolved ← resolver previous.context
      match resolved with
      | none => pure none
      | some resolved => pure (some ⟨resolved.toDeferredContext, resolved.output⟩)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem positionResolutionCommutes_compose
    (target : Position) (first second : PrivateResolver) (context : DeferredContext)
    (hfirst : PositionResolutionCommutes target first context)
    (hsecond : ∀ firstResolved,
      some firstResolved ∈ support (first context) →
      PositionResolutionCommutes target second firstResolved.toDeferredContext) :
    PositionResolutionCommutes target (composePrivateResolvers first second) context := by
  unfold PositionResolutionCommutes
  calc
    _ = evalDist (resolvePositionThenResolver target first context >>=
          continueResolverAfterRevealed second) := by
      unfold resolvePositionThenResolver composePrivateResolvers
        continueResolverAfterRevealed
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro targetResolved _htargetResolved
      cases targetResolved with
      | none => rfl
      | some targetResolved =>
          simp only
          rw [bind_assoc]
          apply evalDist_bind_congr
          intro firstResolved _hfirstResolved
          cases firstResolved <;> rfl
    _ = evalDist (resolveResolverThenPosition target first context >>=
          continueResolverAfterRevealed second) :=
      evalDist_bind_eq_of_evalDist_eq hfirst (continueResolverAfterRevealed second)
    _ = evalDist (first context >>= fun firstResolved =>
          match firstResolved with
          | none => pure none
          | some firstResolved =>
              resolvePositionThenResolver target second firstResolved.toDeferredContext) := by
      unfold resolveResolverThenPosition continueResolverAfterRevealed
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro firstResolved _hfirstResolved
      cases firstResolved with
      | none => rfl
      | some firstResolved =>
          simp only
          rw [bind_assoc]
          apply evalDist_bind_congr
          intro targetResolved _htargetResolved
          cases targetResolved <;> rfl
    _ = evalDist (first context >>= fun firstResolved =>
          match firstResolved with
          | none => pure none
          | some firstResolved =>
              resolveResolverThenPosition target second firstResolved.toDeferredContext) := by
      apply evalDist_bind_congr
      intro firstResolved hfirstResolved
      cases firstResolved with
      | none => rfl
      | some firstResolved => exact hsecond firstResolved hfirstResolved
    _ = _ := by
      unfold resolveResolverThenPosition composePrivateResolvers
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro firstResolved _hfirstResolved
      cases firstResolved with
      | none => rfl
      | some firstResolved =>
          apply evalDist_bind_congr
          intro secondResolved _hsecondResolved
          cases secondResolved <;> rfl

theorem positionResolutionCommutes_value
    (target position : Position) (context : DeferredContext) :
    PositionResolutionCommutes target
      (fun context => resolveDeferredPositionValue position context) context := by
  change evalDist (resolvePositionValuesInOrder target position context) =
    evalDist (resolvePositionValuesSwapped target position context)
  by_cases heq : target = position
  · simpa [heq] using evalDist_resolvePositionValues_comm_self position context
  · exact evalDist_resolvePositionValues_comm_of_ne target position context heq

theorem positionResolutionCommutes_chainPrefix
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (steps : Nat) (hsteps : steps ≤ chainLength - 1) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    PositionResolutionCommutes target
      (fun context => resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        steps hsteps context) context := by
  change evalDist (resolvePositionThenChainPrefix target table lay tree leafIdx chainIdx
      steps hsteps context) =
    evalDist (resolveChainPrefixThenPosition target table lay tree leafIdx chainIdx
      steps hsteps context)
  exact evalDist_resolvePosition_chainPrefix_comm target table lay tree leafIdx chainIdx
    steps hsteps context hvalid hcompletable

theorem positionResolutionCommutes_otsLeaf
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context) :
    PositionResolutionCommutes target
      (fun context => resolveDeferredOtsLeaf table lay tree leafIdx context) context := by
  change evalDist (resolvePositionThenOtsLeaf target table lay tree leafIdx context) =
    evalDist (resolveOtsLeafThenPosition target table lay tree leafIdx context)
  exact evalDist_resolvePosition_otsLeaf_comm target table lay tree leafIdx context hvalid
    hcompletable

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem positionResolutionCommutes_treeNode
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context,
      context.Valid → DeferredCompletable table context →
      PositionResolutionCommutes target
        (fun context => resolveDeferredTreeNode table lay tree level nodeIdx hlevel context)
        context
  | 0, nodeIdx, hlevel, context, hvalid, hcompletable => by
      simpa only [resolveDeferredTreeNode] using
        positionResolutionCommutes_otsLeaf target table lay tree (leafOfNat nodeIdx)
          context hvalid hcompletable
  | level + 1, nodeIdx, hlevel, context, hvalid, hcompletable => by
      let left : PrivateResolver := fun context =>
        resolveDeferredTreeNode table lay tree level (2 * nodeIdx) (by omega) context
      let right : PrivateResolver := fun context =>
        resolveDeferredTreeNode table lay tree level (2 * nodeIdx + 1) (by omega) context
      let node : PrivateResolver := fun context =>
        resolveDeferredPositionValue
          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) context
      have hleft : PositionResolutionCommutes target left context :=
        positionResolutionCommutes_treeNode target table lay tree level (2 * nodeIdx)
          (by omega) context hvalid hcompletable
      have hrest : ∀ leftResolved,
          some leftResolved ∈ support (left context) →
          PositionResolutionCommutes target (composePrivateResolvers right node)
            leftResolved.toDeferredContext := by
        intro leftResolved hleftResolved
        have hleftValid : leftResolved.toDeferredContext.Valid :=
          hvalid.of_resolveDeferredTreeNode table lay tree level (2 * nodeIdx)
            (by omega) leftResolved hleftResolved
        have hleftCompletable : DeferredCompletable table leftResolved.toDeferredContext :=
          hcompletable.of_resolveDeferredTreeNode hvalid hleftResolved
        have hright : PositionResolutionCommutes target right
            leftResolved.toDeferredContext :=
          positionResolutionCommutes_treeNode target table lay tree level
            (2 * nodeIdx + 1) (by omega) leftResolved.toDeferredContext hleftValid
              hleftCompletable
        apply positionResolutionCommutes_compose target right node
          leftResolved.toDeferredContext hright
        intro rightResolved _hrightResolved
        exact positionResolutionCommutes_value target
          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
          rightResolved.toDeferredContext
      have hresolver :
          (fun nextContext =>
            resolveDeferredTreeNode table lay tree (level + 1) nodeIdx hlevel nextContext) =
          composePrivateResolvers left (composePrivateResolvers right node) := by
        funext nextContext
        unfold left right node composePrivateResolvers
        rw [resolveDeferredTreeNode]
        apply bind_congr
        intro leftResolved
        cases leftResolved with
        | none => rfl
        | some leftResolved =>
            apply bind_congr
            intro rightResolved
            cases rightResolved <;> rfl
      have hcomposed := positionResolutionCommutes_compose target left
        (composePrivateResolvers right node) context hleft hrest
      rw [hresolver]
      exact hcomposed

theorem positionResolutionCommutes_position
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context) :
    PositionResolutionCommutes target
      (fun context => resolveDeferredPosition table position context) context := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact positionResolutionCommutes_chainPrefix target table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) context hvalid hcompletable
  | leaf lay tree leafIdx =>
      exact positionResolutionCommutes_otsLeaf target table lay tree leafIdx context hvalid
        hcompletable
  | node lay tree level nodeIdx =>
      exact positionResolutionCommutes_treeNode target table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) context hvalid hcompletable
  | ftsLeaf index tree leafIdx =>
      exact positionResolutionCommutes_value target (.ftsLeaf index tree leafIdx) context
  | ftsNode index tree level nodeIdx =>
      exact positionResolutionCommutes_value target (.ftsNode index tree level nodeIdx) context
  | ftsRoots index =>
      exact positionResolutionCommutes_value target (.ftsRoots index) context

theorem positionResolutionCommutes_reveal
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context) :
    PositionResolutionCommutes target
      (fun context => resolveDeferredReveal table position context) context := by
  classical
  unfold resolveDeferredReveal
  by_cases hresolvable : ResolvableOtsPosition position
  · simp only [hresolvable, if_pos]
    exact positionResolutionCommutes_position target table position context hvalid hcompletable
  · simp only [hresolvable]
    exact positionResolutionCommutes_value target position context

end SphincsSecurity.Concrete.OtsProbeSimulation
