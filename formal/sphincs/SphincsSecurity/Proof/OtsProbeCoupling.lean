import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeOrigin

/-!
# Retained one-time game coupling

The ordinary side of the split probing oracle is exactly the real lazy random oracle. This module
packages that distributional identity as the relational kernel used by the retained-game lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def AnswersAgreeOnRun (f g : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f computation → f input = g input

theorem AnswersAgreeOnRun.eval_eq_and_queriedInputs_eq
    {f g : QueryImpl HashSpec Id} {computation : OracleComp HashSpec alpha}
    (hagrees : AnswersAgreeOnRun f g computation) :
    evalWithAnswerFn f computation = evalWithAnswerFn g computation ∧
      queriedInputs f computation = queriedInputs g computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      have hinput : f input = g input := by
        apply hagrees input
        rw [queriedInputs_query_bind]
        exact List.mem_cons_self
      have htail : AnswersAgreeOnRun f g (next (f input)) := by
        intro query hquery
        apply hagrees query
        rw [queriedInputs_query_bind]
        exact List.mem_cons_of_mem input hquery
      obtain ⟨heval, hqueries⟩ := ih (f input) htail
      constructor
      · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind,
          show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
            simulateQ_spec_query f input,
          show evalWithAnswerFn g (liftM (HashSpec.query input)) = g input from
            simulateQ_spec_query g input,
          ← hinput]
        exact heval
      · rw [queriedInputs_query_bind, queriedInputs_query_bind, ← hinput, hqueries]

theorem AnswersAgreeOnRun.eval_eq
    {f g : QueryImpl HashSpec Id} {computation : OracleComp HashSpec alpha}
    (hagrees : AnswersAgreeOnRun f g computation) :
    evalWithAnswerFn f computation = evalWithAnswerFn g computation :=
  hagrees.eval_eq_and_queriedInputs_eq.1

theorem messageDigest_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {input : HashInput}
    (hquery : input ∈ queriedInputs f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness)) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  rw [verify_eq, queriedInputs_bind]
  exact List.mem_append_left _ hquery

theorem ftsRecover_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hquery : input ∈ queriedInputs f
      (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
        signature.ftsSecret signature.ftsPath)) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  rw [verify_eq, queriedInputs_bind]
  apply List.mem_append_right
  rw [hdigest]
  simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
  exact List.mem_append_left _ hquery

theorem verifyLayers_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hquery : input ∈ queriedInputs f
      (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath)))) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  rw [verify_eq, queriedInputs_bind]
  apply List.mem_append_right
  rw [hdigest]
  simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
  apply List.mem_append_right
  exact List.mem_append_left _ hquery

theorem bottomOts_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hquery : input ∈ queriedInputs f
      (otsLeaf publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer) (signature.chainValue bottomLayer))) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  apply verifyLayers_query_mem_verify hdigest hadmissible
  rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
    dif_pos bottomLayer.isLt]
  exact queriedInputs_mono_bind_left f _ _ hquery

theorem bottomFold_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {bottomLeaf : Digest}
    {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hbottom : evalWithAnswerFn f
      (otsLeaf publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer) (signature.chainValue bottomLayer)) = some bottomLeaf)
    (hquery : input ∈ queriedInputs f
      (treeFold publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (signaturePath signature bottomLayer) (layerHeight bottomLayer) bottomLeaf)) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  apply verifyLayers_query_mem_verify hdigest hadmissible
  rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
    dif_pos bottomLayer.isLt]
  apply queriedInputs_mono_bind_right
  rw [hbottom]
  exact queriedInputs_mono_bind_left f _ _ hquery

theorem middleOts_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {bottomLeaf : Digest}
    {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hbottom : evalWithAnswerFn f
      (otsLeaf publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer) (signature.chainValue bottomLayer)) = some bottomLeaf)
    (hquery : input ∈ queriedInputs f
      (otsLeaf publicKey.parameter middleLayer
        (treeIndexAt (digestIndex digest) middleLayer)
        (leafIndexAt (digestIndex digest) middleLayer)
        (foldValue f publicKey.parameter bottomLayer
          (treeIndexAt (digestIndex digest) bottomLayer)
          (leafIndexAt (digestIndex digest) bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer))
        (signature.counter middleLayer) (signature.chainValue middleLayer))) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  apply verifyLayers_query_mem_verify hdigest hadmissible
  rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
    dif_pos bottomLayer.isLt]
  apply queriedInputs_mono_bind_right
  rw [hbottom]
  apply queriedInputs_mono_bind_right
  change input ∈ queriedInputs f
    (verifyLayers publicKey.parameter (digestIndex digest) signature
      (middleLayer.val + 1)
      (foldValue f publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)))
  rw [verifyLayers_succ_eq, dif_pos middleLayer.isLt]
  simp only [show (⟨middleLayer.val, by exact middleLayer.isLt⟩ : Layer) = middleLayer by
    exact Fin.ext rfl]
  exact queriedInputs_mono_bind_left f _ _ hquery

theorem middleFold_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {bottomLeaf middleLeaf : Digest}
    {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hbottom : evalWithAnswerFn f
      (otsLeaf publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (evalWithAnswerFn f
          (ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest)
            signature.ftsSecret signature.ftsPath))
        (signature.counter bottomLayer) (signature.chainValue bottomLayer)) = some bottomLeaf)
    (hmiddle : evalWithAnswerFn f
      (otsLeaf publicKey.parameter middleLayer
        (treeIndexAt (digestIndex digest) middleLayer)
        (leafIndexAt (digestIndex digest) middleLayer)
        (foldValue f publicKey.parameter bottomLayer
          (treeIndexAt (digestIndex digest) bottomLayer)
          (leafIndexAt (digestIndex digest) bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer))
        (signature.counter middleLayer) (signature.chainValue middleLayer)) = some middleLeaf)
    (hquery : input ∈ queriedInputs f
      (treeFold publicKey.parameter middleLayer
        (treeIndexAt (digestIndex digest) middleLayer)
        (leafIndexAt (digestIndex digest) middleLayer)
        (signaturePath signature middleLayer) (layerHeight middleLayer) middleLeaf)) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  apply verifyLayers_query_mem_verify hdigest hadmissible
  rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
    dif_pos bottomLayer.isLt]
  apply queriedInputs_mono_bind_right
  rw [hbottom]
  apply queriedInputs_mono_bind_right
  change input ∈ queriedInputs f
    (verifyLayers publicKey.parameter (digestIndex digest) signature
      (middleLayer.val + 1)
      (foldValue f publicKey.parameter bottomLayer
        (treeIndexAt (digestIndex digest) bottomLayer)
        (leafIndexAt (digestIndex digest) bottomLayer)
        (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)))
  rw [verifyLayers_succ_eq, dif_pos middleLayer.isLt]
  simp only [show (⟨middleLayer.val, by exact middleLayer.isLt⟩ : Layer) = middleLayer by
    exact Fin.ext rfl]
  apply queriedInputs_mono_bind_right
  rw [hmiddle]
  exact queriedInputs_mono_bind_left f _ _ hquery

theorem probingHashQuery_eq_splitHashQuery_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashQuery parameter input = splitHashQuery (.ordinary input) := by
  unfold probingHashQuery
  rw [hstable.1]
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | leaf lay tree leafIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | node lay tree level nodeIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots => rfl

theorem tableAnswer_realizes_otsPositions
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) :
    ∀ position : Position, IsOtsPosition position →
      tableAnswer parameter table fallback
          (tableInput parameter table (.position position)) =
        table (.position position) := by
  intro position hposition
  exact tableAnswer_tableInput parameter table fallback position hposition

theorem positionValues_or_first_missing
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (positions : List Position)
    (htable : ∀ position output,
      state.values (.position position) = some output →
        output = table (.position position)) :
    (∀ position, position ∈ positions →
      state.values (.position position) = some (table (.position position))) ∨
      ∃ prior position remaining,
        positions = prior ++ position :: remaining ∧
        (∀ other, other ∈ prior →
          state.values (.position other) = some (table (.position other))) ∧
        state.values (.position position) = none := by
  induction positions with
  | nil =>
      left
      simp
  | cons head tail ih =>
      cases hvalue : state.values (.position head) with
      | none =>
          right
          exact ⟨[], head, tail, by simp, by simp, hvalue⟩
      | some output =>
          have hhead : state.values (.position head) =
              some (table (.position head)) := by
            rw [hvalue, htable head output hvalue]
          rcases ih with htail | ⟨prior, position, remaining, htail, hprior, hmissing⟩
          · left
            intro position hposition
            simp only [List.mem_cons] at hposition
            rcases hposition with rfl | hposition
            · exact hhead
            · exact htail position hposition
          · right
            exact ⟨head :: prior, position, remaining, by simp [htail],
              fun other hother => by
                simp only [List.mem_cons] at hother
                rcases hother with rfl | hother
                · exact hhead
                · exact hprior other hother,
              hmissing⟩

def TableInputAvailable (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) : Coordinate → Prop
  | .chainStart _ _ _ _ => False
  | .position position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        state.values (.chainStart lay tree leafIdx chainIdx) =
          some (table (.chainStart lay tree leafIdx chainIdx))
      else
        ∀ child, child ∈ position.children →
          state.values (.position child) = some (table (.position child))
  | .position position =>
      ∀ child, child ∈ position.children →
        state.values (.position child) = some (table (.position child))

theorem slotDigest_tableInput_node_getElem
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (slot : Nat)
    (hslot : slot < (Position.node lay tree level nodeIdx).children.length) :
    slotDigest slot
        (tableInput parameter table
          (.position (.node lay tree level nodeIdx))) =
      truncateHash (table (.position
        (Position.node lay tree level nodeIdx).children[slot])) := by
  change slotDigest slot
      (tweakableHashInput parameter (Position.node lay tree level nodeIdx).domain
        ((((Position.node lay tree level nodeIdx).children.map
          (tableValue table))).flatMap digestBytes)) = _
  rw [slotDigest_flatMap parameter (Position.node lay tree level nodeIdx).domain
    ((Position.node lay tree level nodeIdx).children.map (tableValue table)) slot
      (by simpa using hslot)]
  simp [tableValue]

theorem slotDigest_tableInput_leaf_getElem
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (slot : Nat)
    (hslot : slot < (Position.leaf lay tree leafIdx).children.length) :
    slotDigest slot (tableInput parameter table (.position (.leaf lay tree leafIdx))) =
      truncateHash (table (.position (Position.leaf lay tree leafIdx).children[slot])) := by
  change slotDigest slot
      (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
        (((Position.leaf lay tree leafIdx).children.map
          (tableValue table)).flatMap digestBytes)) = _
  rw [slotDigest_flatMap parameter (Position.leaf lay tree leafIdx).domain
    ((Position.leaf lay tree leafIdx).children.map (tableValue table)) slot
      (by simpa using hslot)]
  simp [tableValue]

theorem leaf_children_getElem_zero
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hzero : 0 < (Position.leaf lay tree leafIdx).children.length) :
    (Position.leaf lay tree leafIdx).children[0]'hzero =
      .chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩ Position.lastChainStep := by
  simp [Position.children]

set_option maxRecDepth 10000 in
theorem decodeProbe?_tableInput_leaf_eq
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (candidate : Probe)
    (hdecode : decodeProbe? parameter
      (tableInput parameter table (.position (.leaf lay tree leafIdx))) = some candidate) :
    candidate =
      ⟨.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
        Position.lastChainStep),
        slotDigest 0 (tableInput parameter table (.position (.leaf lay tree leafIdx)))⟩ := by
  apply Probe.matchesInput_unique parameter
    (tableInput parameter table (.position (.leaf lay tree leafIdx)))
  · exact (decodeProbe?_eq_some_iff parameter _ candidate).1 hdecode
  · simp only [Probe.MatchesInput]
    rw [dif_neg (by simp [Position.lastChainStep, chainLength, winternitzBits])]
    exact ⟨trivial, tablePayload table (.leaf lay tree leafIdx), rfl, trivial⟩

theorem mem_runRaw_revealCoordinate_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealCoordinate coordinate).run cache))) :
    ∃ output : HashOutput,
      value = truncateHash output ∧ finalState.values coordinate = some output := by
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some output =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨output, rfl, hvalue⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨output, rfl, by
          simp [LazyRevealProbe.State.materialize, Function.update]⟩

theorem mem_runRaw_revealPublishedCoordinate_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealPublishedCoordinate coordinate).run cache))) :
    ∃ output : HashOutput,
      value = truncateHash output ∧ finalState.values coordinate = some output := by
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hrevealed := mem_runRaw_revealCoordinate_value coordinate state revealState cache
        revealCache fuel revealRemaining revealed hreveal
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((publishCoordinate coordinate >>= fun _ => pure revealed).run revealCache)
        revealState finalState revealRemaining remaining (value, finalCache) hrest
      simp [publishCoordinate, LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw] at hrest
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hrevealed.choose, hrevealed.choose_spec.1,
        hvaluesLE coordinate hrevealed.choose hrevealed.choose_spec.2⟩

theorem revealLayerValues_eq_table
    (table : Coordinate → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (values : (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealLayerValues index lay encoding).run cache))) :
    values.1 = (fun chainIdx => truncateHash (table
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (encoding chainIdx)))) ∧
      values.2 = (fun level =>
        if level.val < layerHeight lay then
          match level.val with
          | 0 => truncateHash (table (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))))
          | current + 1 =>
              if hlevel : current < maxLayerHeight then
                truncateHash (table (.position (.node lay (treeIndexAt index lay)
                  ⟨current, hlevel⟩ (leafOfNat
                    (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)))))
              else 0
        else 0) := by
  unfold revealLayerValues at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨chainRaw, hchains, hafterChains⟩ := hresult
  cases chainRaw with
  | stopped hit => simp at hafterChains
  | done chainState chainRemaining chainResult =>
      rcases chainResult with ⟨chainValues, chainCache⟩
      simp only at hafterChains
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterChains
      obtain ⟨pathRaw, hpaths, hfinish⟩ := hafterChains
      cases pathRaw with
      | stopped hit => simp at hfinish
      | done pathState pathRemaining pathResult =>
          rcases pathResult with ⟨pathValues, pathCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨hfinalState, hremaining, hvalues, hfinalCache⟩
          subst finalState
          subst remaining
          subst values
          subst finalCache
          have hchainValuesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((sequenceFin fun level : Fin maxLayerHeight =>
              if level.val < layerHeight lay then
                match level.val with
                | 0 => revealPublishedCoordinate (.position (.leaf lay
                    (treeIndexAt index lay)
                    (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
                | current + 1 =>
                    if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay
                        (treeIndexAt index lay) ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0
              else pure 0).run chainCache)
            chainState pathState chainRemaining pathRemaining (pathValues, pathCache) hpaths
          constructor
          · funext chainIdx
            change chainValues chainIdx = _
            obtain ⟨componentState, componentFinalState, componentCache,
                componentFinalCache, componentFuel, componentRemaining, componentValue,
                hcomponent, hselected, hcomponentLE, _, _⟩ :=
              sequenceFin_component_run_of_done
                (fun chainIdx : ChainIndex => revealPublishedCoordinate
                  (chainValueCoordinate lay (treeIndexAt index lay)
                    (leafIndexAt index lay) chainIdx (encoding chainIdx)))
                (fun chainIdx => ordinaryCacheIncreasing_revealPublishedCoordinate _)
                state chainState cache chainCache fuel chainRemaining chainValues hchains chainIdx
            obtain ⟨output, hvalue, hstateValue⟩ :=
              mem_runRaw_revealPublishedCoordinate_value
                (chainValueCoordinate lay (treeIndexAt index lay)
                  (leafIndexAt index lay) chainIdx (encoding chainIdx))
                componentState componentFinalState componentCache componentFinalCache
                  componentFuel componentRemaining componentValue hcomponent
            rw [hselected, hvalue, htable _ output
              (hchainValuesLE _ _ (hcomponentLE _ _ hstateValue))]
          · funext level
            change pathValues level = _
            obtain ⟨componentState, componentFinalState, componentCache,
                componentFinalCache, componentFuel, componentRemaining, componentValue,
                hcomponent, hselected, hcomponentLE, _, _⟩ :=
              sequenceFin_component_run_of_done
                (fun level : Fin maxLayerHeight =>
                  if level.val < layerHeight lay then
                    match level.val with
                    | 0 => revealPublishedCoordinate (.position (.leaf lay
                        (treeIndexAt index lay)
                        (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
                    | current + 1 =>
                        if hlevel : current < maxLayerHeight then
                          revealPublishedCoordinate (.position (.node lay
                            (treeIndexAt index lay) ⟨current, hlevel⟩ (leafOfNat
                              (Nat.xor ((leafIndexAt index lay).val /
                                2 ^ (current + 1)) 1))))
                        else pure 0
                  else pure 0)
                (fun level => by
                  split
                  · split
                    · exact ordinaryCacheIncreasing_revealPublishedCoordinate _
                    · split
                      · exact ordinaryCacheIncreasing_revealPublishedCoordinate _
                      · exact OrdinaryCacheIncreasing.pure 0
                  · exact OrdinaryCacheIncreasing.pure 0)
                chainState pathState chainCache pathCache chainRemaining pathRemaining
                  pathValues hpaths level
            rw [hselected]
            by_cases hinLayer : level.val < layerHeight lay
            · rw [if_pos hinLayer]
              cases hlevelValue : level.val with
              | zero =>
                  have hpositive : 0 < layerHeight lay := by omega
                  obtain ⟨output, hvalue, hstateValue⟩ :=
                    mem_runRaw_revealPublishedCoordinate_value _ componentState
                      componentFinalState componentCache componentFinalCache componentFuel
                        componentRemaining componentValue (by
                          simpa [hinLayer, hlevelValue, hpositive] using hcomponent)
                  rw [hvalue, htable _ output (hcomponentLE _ _ hstateValue)]
                  simp
              | succ current =>
                  have hcurrent : current < maxLayerHeight := by omega
                  have hcurrentLayer : current + 1 < layerHeight lay := by omega
                  let coordinate : Coordinate := .position (.node lay
                    (treeIndexAt index lay) ⟨current, hcurrent⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)))
                  obtain ⟨output, hvalue, hstateValue⟩ :=
                    mem_runRaw_revealPublishedCoordinate_value coordinate componentState
                      componentFinalState componentCache componentFinalCache componentFuel
                        componentRemaining componentValue (by
                          simpa [coordinate, hlevelValue, hcurrent, hcurrentLayer] using hcomponent)
                  rw [hvalue, htable coordinate output (hcomponentLE _ _ hstateValue)]
                  simp [coordinate, hcurrent]
            · rw [if_neg hinLayer]
              simp [hinLayer, LazyRevealProbe.runRaw] at hcomponent
              exact hcomponent.2.2.1

attribute [local irreducible] ensureFullChain ensureOtsLeaf

theorem Probe.outputCoordinate_eq_position_of_matchesInput
    (parameter : PublicParameter) (probe : Probe) (input : HashInput)
    (position : Position) (hmatches : probe.MatchesInput parameter input)
    (hposition : AtPosition parameter input position) :
    probe.outputCoordinate = .position position := by
  have hat : ∃ outputPosition,
      probe.outputCoordinate = .position outputPosition ∧
        AtPosition parameter input outputPosition := by
    rcases probe with ⟨coordinate, candidate⟩
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        obtain ⟨step, hzero, hinput⟩ := hmatches
        let first : ChainStep := ⟨0, by norm_num [chainLength, winternitzBits]⟩
        have hstep : step = first := Fin.ext hzero
        subst step
        exact ⟨.chain lay tree leafIdx chainIdx first, rfl,
          ⟨digestBytes candidate, hinput⟩⟩
    | position source =>
        cases source with
        | chain lay tree leafIdx chainIdx step =>
            simp only [Probe.MatchesInput] at hmatches
            by_cases hnext : step.val + 1 < chainLength - 1
            · rw [dif_pos hnext] at hmatches
              obtain ⟨nextStep, hnextValue, hinput⟩ := hmatches
              have hstep : nextStep = ⟨step.val + 1, hnext⟩ := Fin.ext hnextValue
              subst nextStep
              exact ⟨.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩,
                by simp [Probe.outputCoordinate, hnext], ⟨digestBytes candidate, hinput⟩⟩
            · rw [dif_neg hnext] at hmatches
              obtain ⟨_, payload, hinput, _⟩ := hmatches
              exact ⟨.leaf lay tree leafIdx,
                by simp [Probe.outputCoordinate, hnext], ⟨payload, hinput⟩⟩
        | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
            simp [Probe.MatchesInput] at hmatches
  obtain ⟨outputPosition, houtput, hatOutput⟩ := hat
  rw [houtput]
  exact congrArg Coordinate.position (atPosition_unique parameter hatOutput hposition)

def PreservesCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      finalState.values coordinate = state.values coordinate ∧
        (coordinate ∈ finalState.revealed ↔ coordinate ∈ state.revealed)

def PublishedValues (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate, coordinate ∈ state.revealed → state.values coordinate ≠ none

def PreservesPublishedValues
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    PublishedValues state →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    PublishedValues finalState

theorem PreservesPublishedValues.of_preservesCoordinate
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : ∀ coordinate, PreservesCoordinate coordinate computation) :
    PreservesPublishedValues computation := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult coordinate
    hrevealed
  have hcoordinate := hpreserves coordinate state cache fuel finalState remaining value finalCache
    hresult
  rw [hcoordinate.1]
  exact hpublished coordinate (hcoordinate.2.1 hrevealed)

theorem decodeProbe?_outputCoordinate_eq_position
    (parameter : PublicParameter) (input : HashInput) (probe : Probe)
    (position : Position) (hprobe : decodeProbe? parameter input = some probe)
    (hposition : decodePosition? parameter input = some position) :
    probe.outputCoordinate = .position position := by
  exact probe.outputCoordinate_eq_position_of_matchesInput parameter input position
    ((decodeProbe?_eq_some_iff parameter input probe).1 hprobe)
    ((decodePosition?_eq_some_iff parameter input position).1 hposition)

noncomputable def chainInputSource (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) : Coordinate :=
  if hzero : step.val = 0 then
    .chainStart lay tree leafIdx chainIdx
  else
    .position (.chain lay tree leafIdx chainIdx
      ⟨step.val - 1, by have := step.isLt; omega⟩)

noncomputable def chainInputProbe (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) : Probe :=
  ⟨chainInputSource lay tree leafIdx chainIdx step,
    truncateHash (table (chainInputSource lay tree leafIdx chainIdx step))⟩

theorem chainInputProbe_matchesInput
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    (chainInputProbe table lay tree leafIdx chainIdx step).MatchesInput parameter
      (tableInput parameter table
        (.position (.chain lay tree leafIdx chainIdx step))) := by
  by_cases hzero : step.val = 0
  · simp only [chainInputProbe, chainInputSource, hzero, ↓reduceDIte, Probe.MatchesInput]
    refine ⟨step, hzero, ?_⟩
    simp [tableInput, tablePayload, hzero, Position.domain]
  · have hpositive : 0 < step.val := Nat.pos_of_ne_zero hzero
    let previous : ChainStep := ⟨step.val - 1, by have := step.isLt; omega⟩
    have hnext : previous.val + 1 < chainLength - 1 := by
      simp only [previous]
      have := step.isLt
      omega
    simp only [chainInputProbe, chainInputSource, hzero, ↓reduceDIte, Probe.MatchesInput]
    rw [dif_pos hnext]
    refine ⟨step, ?_, ?_⟩
    · omega
    · simp [tableInput, tablePayload, hzero, Position.children, hpositive, tableValue,
        Position.domain]

@[simp] theorem chainInputProbe_candidate
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) :
    (chainInputProbe table lay tree leafIdx chainIdx step).candidate =
      truncateHash (table (chainInputSource lay tree leafIdx chainIdx step)) := rfl

def ProbeFree
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ cache, (computation.run cache).IsQueryBoundP
    (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0

theorem ProbeFree.pure (value : alpha) :
    ProbeFree (pure value : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro cache
  simp

theorem ProbeFree.modify (update : SplitHashCache → SplitHashCache) :
    ProbeFree (modify update : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro cache
  simp

theorem ProbeFree.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : ProbeFree left) (hnext : ∀ value, ProbeFree (next value)) :
    ProbeFree (left >>= next) := by
  intro cache
  rw [StateT.run_bind]
  have hbound := OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (hleft cache)
    (fun result _ => hnext result.1 result.2)
  simpa using hbound

theorem splitHashQuery_run_isProbeBound (key : SplitHashKey)
    (cache : SplitHashCache) (fuel : Nat) :
    ((splitHashQuery key).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) fuel := by
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp
  | none =>
      change (LazyRevealProbe.hashOutputQuery (Coordinate := Coordinate) >>= fun output =>
        pure (output, Function.update cache key (some output))).IsQueryBoundP
          (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) fuel
      exact OracleComp.isQueryBoundP_bind (n := fuel) (m := 0)
        (LazyRevealProbe.hashOutputQuery_isProbeBound fuel) (fun _ _ => by simp)

theorem splitHashQuery_probeFree (key : SplitHashKey) :
    ProbeFree (splitHashQuery key) :=
  fun cache => splitHashQuery_run_isProbeBound key cache 0

theorem splitUniformImpl_probeFree (n : unifSpec.Domain) :
    ProbeFree (splitUniformImpl n) := by
  intro cache
  change (((fun output : Fin (n + 1) => (output, cache)) <$>
    LazyRevealProbe.uniformQuery (Coordinate := Coordinate) n).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
  rw [OracleComp.isQueryBoundP_map_iff, LazyRevealProbe.uniformQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [LazyRevealProbe.IsProbe]

theorem peekCoordinate_probeFree (coordinate : Coordinate) :
    ProbeFree (peekCoordinate coordinate) := by
  intro cache
  unfold peekCoordinate
  rw [StateT.run_bind]
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (by
      change (LazyRevealProbe.peekQuery coordinate).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0
      exact LazyRevealProbe.peekQuery_isProbeBound coordinate 0)
    (fun _ _ => by simp)

theorem peekPositionValues_probeFree : ∀ positions,
    ProbeFree (peekPositionValues positions)
  | [] => ProbeFree.pure (some [])
  | position :: remaining => by
      rw [peekPositionValues]
      exact (peekCoordinate_probeFree (.position position)).bind fun value => by
        cases value with
        | none => exact ProbeFree.pure none
        | some value =>
            exact (peekPositionValues_probeFree remaining).bind fun values => by
              cases values with
              | none => exact ProbeFree.pure none
              | some values => exact ProbeFree.pure (some (value :: values))

theorem peekTableInput_probeFree (parameter : PublicParameter) : ∀ coordinate,
    ProbeFree (peekTableInput parameter coordinate)
  | .chainStart _ _ _ _ => ProbeFree.pure none
  | .position position => by
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          split
          · exact (peekCoordinate_probeFree (.chainStart lay tree leafIdx chainIdx)).bind
              fun value => by
                cases value with
                | none => exact ProbeFree.pure none
                | some value => exact ProbeFree.pure _
          · exact (peekPositionValues_probeFree
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values => by
                cases values with
                | none => exact ProbeFree.pure none
                | some values => exact ProbeFree.pure _
      | leaf lay tree leafIdx =>
          rw [peekTableInput]
          exact (peekPositionValues_probeFree
            (Position.leaf lay tree leafIdx).children).bind fun values => by
            cases values with
            | none => exact ProbeFree.pure none
            | some values => exact ProbeFree.pure _
          all_goals simp
      | node lay tree level nodeIdx =>
          rw [peekTableInput]
          exact (peekPositionValues_probeFree
            (Position.node lay tree level nodeIdx).children).bind fun values => by
              cases values with
              | none => exact ProbeFree.pure none
              | some values => exact ProbeFree.pure _
          all_goals simp
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput]
          exact (peekPositionValues_probeFree
            (Position.ftsLeaf index tree leafIdx).children).bind fun values => by
              cases values with
              | none => exact ProbeFree.pure none
              | some values => exact ProbeFree.pure _
          all_goals simp
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput]
          exact (peekPositionValues_probeFree
            (Position.ftsNode index tree level nodeIdx).children).bind fun values => by
              cases values with
              | none => exact ProbeFree.pure none
              | some values => exact ProbeFree.pure _
          all_goals simp
      | ftsRoots index =>
          rw [peekTableInput]
          exact (peekPositionValues_probeFree
            (Position.ftsRoots index).children).bind fun values => by
              cases values with
              | none => exact ProbeFree.pure none
              | some values => exact ProbeFree.pure _
          all_goals simp

theorem revealCoordinateOutput_probeFree (coordinate : Coordinate) :
    ProbeFree (revealCoordinateOutput coordinate) := by
  intro cache
  change (LazyRevealProbe.revealQuery coordinate >>= fun output =>
    pure (output, Function.update cache (.hidden coordinate) (some output))).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (LazyRevealProbe.revealQuery_isProbeBound coordinate 0) (fun _ _ => by simp)

theorem publishCoordinate_probeFree (coordinate : Coordinate) :
    ProbeFree (publishCoordinate coordinate) := by
  intro cache
  unfold publishCoordinate
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.publishQuery coordinate).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  exact LazyRevealProbe.publishQuery_isProbeBound coordinate 0

theorem resolveKnownInput_probeFree (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput) :
    ProbeFree (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  exact (peekTableInput_probeFree parameter coordinate).bind fun knownInput => by
    cases knownInput with
    | none => exact splitHashQuery_probeFree (.ordinary input)
    | some knownInput =>
        change ProbeFree (if knownInput = input then do
          let output ← revealCoordinateOutput coordinate
          publishCoordinate coordinate
          modify fun cache : SplitHashCache =>
            Function.update cache (.ordinary input) (some output)
          pure output
        else splitHashQuery (.ordinary input))
        by_cases hknown : knownInput = input
        · rw [if_pos hknown]
          exact (revealCoordinateOutput_probeFree coordinate).bind fun output =>
            (publishCoordinate_probeFree coordinate).bind fun _ => by
              exact (ProbeFree.modify fun cache : SplitHashCache =>
                Function.update cache (.ordinary input) (some output)).bind fun _ =>
                  ProbeFree.pure output
        · rw [if_neg hknown]
          exact splitHashQuery_probeFree (.ordinary input)

theorem probe_run_isProbeBound (candidate : Probe) (cache : SplitHashCache) :
    ((probe candidate).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probe
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1)
  rw [OracleComp.isQueryBoundP_map_iff]
  exact LazyRevealProbe.probeQuery_isProbeBound candidate.coordinate candidate.candidate

theorem probeFirstMissingInputCoordinate_run_isProbeBound
    (input : HashInput) (slot : Nat) (coordinates : List Coordinate)
    (cache : SplitHashCache) :
    ((probeFirstMissingInputCoordinate input slot coordinates).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  induction coordinates generalizing slot cache with
  | nil => simp [probeFirstMissingInputCoordinate]
  | cons coordinate remaining ih =>
      rw [probeFirstMissingInputCoordinate, StateT.run_bind]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
      · exact peekCoordinate_probeFree coordinate cache
      · intro result _
        cases result.1 with
        | none => exact probe_run_isProbeBound ⟨coordinate, slotDigest slot input⟩ result.2
        | some value => exact ih (slot + 1) result.2

theorem prepareLeafInputProbe_run_isProbeBound
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (cache : SplitHashCache) :
    ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold prepareLeafInputProbe
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
  · exact peekCoordinate_probeFree candidate.coordinate cache
  · intro result _
    cases result.1 with
    | none => exact probe_run_isProbeBound candidate result.2
    | some value =>
        exact probeFirstMissingInputCoordinate_run_isProbeBound input 0
          ((Position.leaf lay tree leafIdx).children.map Coordinate.position) result.2

theorem probingHashQuery_run_isProbeBound (parameter : PublicParameter)
    (input : HashInput) (cache : SplitHashCache) :
    ((probingHashQuery parameter input).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
          · exact probe_run_isProbeBound candidate cache
          · intro result _
            exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input result.2
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
              · exact prepareLeafInputProbe_run_isProbeBound input candidate lay tree leafIdx cache
              · intro result _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input result.2
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
              · exact probe_run_isProbeBound candidate cache
              · intro result _
                exact resolveKnownInput_probeFree parameter candidate.outputCoordinate input result.2
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact splitHashQuery_run_isProbeBound (.ordinary input) cache 1
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              change ((resolveKnownInput parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input).run cache).IsQueryBoundP
                  (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
              exact (resolveKnownInput_probeFree parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input cache).mono (by omega)
          | leaf lay tree leafIdx =>
              change ((resolveKnownInput parameter
                (.position (.leaf lay tree leafIdx)) input).run cache).IsQueryBoundP
                  (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
              exact (resolveKnownInput_probeFree parameter
                (.position (.leaf lay tree leafIdx)) input cache).mono (by omega)
          | node lay tree level nodeIdx =>
              change ((do
                probeFirstMissingInputCoordinate input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                resolveKnownInput parameter (.position (.node lay tree level nodeIdx)) input).run
                  cache).IsQueryBoundP
                    (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1
              apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
              · exact probeFirstMissingInputCoordinate_run_isProbeBound input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position) cache
              · intro result _
                exact resolveKnownInput_probeFree parameter
                  (.position (.node lay tree level nodeIdx)) input result.2
          | ftsLeaf | ftsNode | ftsRoots =>
              exact splitHashQuery_run_isProbeBound (.ordinary input) cache 1

theorem revealCoordinate_probeFree (coordinate : Coordinate) :
    ProbeFree (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (revealCoordinateOutput_probeFree coordinate).bind fun output =>
    ProbeFree.pure (truncateHash output)

theorem revealPosition_probeFree (position : Position) :
    ProbeFree (revealPosition position) :=
  revealCoordinate_probeFree (.position position)

theorem simulateQ_ordinaryHashImpl_probeFree
    (computation : OracleComp HashSpec alpha) :
    ProbeFree (simulateQ ordinaryHashImpl computation) := by
  intro cache
  apply (OracleComp.isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  exact splitHashQuery_run_isProbeBound (.ordinary input) workingCache 0

theorem simulateQ_ordinaryRomImpl_probeFree
    (computation : OracleComp OracleWorld alpha) :
    ProbeFree (simulateQ ordinaryRomImpl computation) := by
  intro cache
  apply (OracleComp.isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  cases input with
  | inl n => exact splitUniformImpl_probeFree n workingCache
  | inr hashInput => exact splitHashQuery_run_isProbeBound (.ordinary hashInput) workingCache 0

theorem ensureCoordinate_probeFree (coordinate : Coordinate) :
    ProbeFree (ensureCoordinate coordinate) := by
  intro cache
  unfold ensureCoordinate
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.ensureQuery coordinate).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  exact LazyRevealProbe.ensureQuery_isProbeBound coordinate 0

theorem sequenceFin_probeFree {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, ProbeFree (computation index)) :
    ProbeFree (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact ProbeFree.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            ProbeFree.pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem ensureFullChain_probeFree (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ProbeFree (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (sequenceFin_probeFree _ fun step =>
    ensureCoordinate_probeFree (.position (.chain lay tree leafIdx chainIdx step))).bind
      fun _ => ProbeFree.pure ()

theorem ensureChainPrefix_probeFree (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    ProbeFree (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (sequenceFin_probeFree _ fun step => by
    split
    · exact ensureCoordinate_probeFree (.position (.chain lay tree leafIdx chainIdx step))
    · exact ProbeFree.pure ()).bind fun _ => ProbeFree.pure ()

theorem ensureOtsLeaf_probeFree (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ProbeFree (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (sequenceFin_probeFree _ fun chainIdx =>
    ensureFullChain_probeFree lay tree leafIdx chainIdx).bind fun _ =>
      ensureCoordinate_probeFree (.position (.leaf lay tree leafIdx))

theorem ensureTreeNode_probeFree (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, ProbeFree (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => ensureOtsLeaf_probeFree lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (ensureTreeNode_probeFree lay tree level (2 * nodeIdx)).bind fun _ =>
        (ensureTreeNode_probeFree lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact ensureCoordinate_probeFree (.position
              (.node lay tree ⟨level, by assumption⟩ (leafOfNat nodeIdx)))
          · exact ProbeFree.pure ()

theorem maskedTreeNode_probeFree (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) : ProbeFree (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (ensureTreeNode_probeFree lay tree 0 nodeIdx).bind fun _ =>
        revealPosition_probeFree (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      rw [maskedTreeNode]
      exact (ensureTreeNode_probeFree lay tree (current + 1) nodeIdx).bind fun _ => by
        split
        · exact revealPosition_probeFree
            (.node lay tree ⟨current, by assumption⟩ (leafOfNat nodeIdx))
        · exact ProbeFree.pure 0

theorem maskedTreeRoot_probeFree (lay : Layer) (tree : TreeIndex) :
    ProbeFree (maskedTreeRoot lay tree) :=
  maskedTreeNode_probeFree lay tree (layerHeight lay) 0

theorem ensureTreePath_probeFree (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ProbeFree (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (sequenceFin_probeFree _ fun level => by
    split
    · exact ensureTreeNode_probeFree lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact ProbeFree.pure ()).bind fun _ => ProbeFree.pure ()

theorem maskedOtsSignFrom_probeFree (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      ProbeFree (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => ProbeFree.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (simulateQ_ordinaryHashImpl_probeFree
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded => by
            cases encoded with
            | none =>
                exact maskedOtsSignFrom_probeFree parameter lay tree leafIdx message attempts
                  (counter + 1)
            | some encoding =>
                exact (sequenceFin_probeFree _ fun chainIdx =>
                  ensureChainPrefix_probeFree lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ => ProbeFree.pure _

theorem maskedOtsSign_probeFree (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ProbeFree (maskedOtsSign parameter lay tree leafIdx message) :=
  maskedOtsSignFrom_probeFree parameter lay tree leafIdx message encodingAttemptLimit 0

theorem maskedLayerMessage_probeFree (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ProbeFree (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact maskedTreeRoot_probeFree _ _
  · exact simulateQ_ordinaryHashImpl_probeFree _

theorem maskedSignLayer_probeFree (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ProbeFree (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (maskedLayerMessage_probeFree parameter ftsSecret index lay).bind fun message =>
    (maskedOtsSign_probeFree parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message).bind fun signed => by
        cases signed with
        | none => exact ProbeFree.pure none
        | some part =>
            exact (ensureTreePath_probeFree lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => ProbeFree.pure (some part)

theorem revealPublishedCoordinate_probeFree (coordinate : Coordinate) :
    ProbeFree (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (revealCoordinate_probeFree coordinate).bind fun value =>
    (publishCoordinate_probeFree coordinate).bind fun _ => ProbeFree.pure value

theorem revealLayerPathValue_probeFree (index : Index) (lay : Layer)
    (level : Fin maxLayerHeight) :
    ProbeFree (if level.val < layerHeight lay then
      match level.val with
      | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
          (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
      | current + 1 =>
          if hlevel : current < maxLayerHeight then
            revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
              ⟨current, hlevel⟩
              (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
          else pure 0
    else pure 0) := by
  by_cases hbelow : level.val < layerHeight lay
  · rw [if_pos hbelow]
    cases hvalue : level.val with
    | zero =>
        exact revealPublishedCoordinate_probeFree (.position (.leaf lay
          (treeIndexAt index lay) (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
    | succ current =>
        simp only
        split
        · exact revealPublishedCoordinate_probeFree (.position (.node lay
            (treeIndexAt index lay) ⟨current, by assumption⟩
            (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
        · exact ProbeFree.pure 0
  · rw [if_neg hbelow]
    exact ProbeFree.pure 0

theorem revealLayerValues_probeFree (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    ProbeFree (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (sequenceFin_probeFree _ fun chainIdx =>
    revealPublishedCoordinate_probeFree
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun values =>
          (sequenceFin_probeFree _ fun level =>
            revealLayerPathValue_probeFree index lay level).bind fun path =>
              ProbeFree.pure (values, path)

def IsOuterHash : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance instDecidablePredDomainSumNatHashInputSignRequestHAddOracleSpecOracleWorldSigningSpecIsOuterHash : DecidablePred IsOuterHash
  | .inl (.inl _) => isFalse id
  | .inl (.inr _) => isTrue trivial
  | .inr _ => isFalse id

end SphincsSecurity.Concrete.OtsProbeSimulation
